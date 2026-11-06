import Langlands.GroupScheme.Reductive.RankOneRootCellRelation
import Langlands.GroupScheme.CentralIsogeny.CorootCompatibility
import Langlands.GroupScheme.Rational.TorusNormalizer

/-! # The Weyl element and the rank-one relation over algebraically closed points

The structure `WeylData` extends `CellData` by a cocharacter `h` with `⟨α, h⟩ = 2` and a
`k`-point `n` normalizing the torus through the reflection of `α`, with `n²` in the torus and
`G` irreducible. From the equivariance `xp(c² x) n = h(c) xp(x) n h(c)` and `n² ∈ T` it proves,
for a constant unit `β` of `k`, the relation
`xp(X) xm(β Y) = xm(β u⁻¹ Y) h(u) xp(u⁻¹ X)` with `u = 1 + XY` (`rel_of_sqField`) and that
`xp(X) xm(β Y)` is outside the cell when `1 + XY = 0` (`not_inCell_of_sqField`), over test
schemes whose global sections satisfy `SqField`, such as spectra of algebraically closed
fields. -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace RankOneRootCellRelation

variable {k : Type u} [Field k]

/-! ### Rings with square roots -/

/-- A ring in which every element is zero or a unit, every unit is a square of a unit, and some
unit has fourth power different from one. The ring of global sections of the spectrum of an
algebraically closed field has these properties. -/
def SqField (R : Type*) [CommRing R] : Prop :=
  (∀ x : R, x = 0 ∨ IsUnit x) ∧ (∀ c : Rˣ, ∃ d : Rˣ, d * d = c) ∧ ∃ c : Rˣ, c ^ 4 ≠ 1

theorem SqField.of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    (h : SqField R) : SqField S := by
  obtain ⟨h1, h2, c, hc⟩ := h
  refine ⟨fun x => ?_, fun c => ?_, Units.map e.toMonoidHom c, ?_⟩
  · rcases h1 (e.symm x) with h | h
    · left
      simpa using congrArg e h
    · right
      simpa using h.map e.toMonoidHom
  · obtain ⟨d, hd⟩ := h2 (Units.map e.symm.toMonoidHom c)
    refine ⟨Units.map e.toMonoidHom d, ?_⟩
    rw [← map_mul, hd]
    ext
    simp
  · rw [← map_pow]
    intro h
    apply hc
    have := congrArg (Units.map e.symm.toMonoidHom) h
    rw [map_pow, map_one] at this
    convert this using 2
    ext
    simp

theorem sqField_of_isAlgClosed (K : Type*) [Field K] [IsAlgClosed K] : SqField K := by
  refine ⟨fun x => ?_, fun c => ?_, ?_⟩
  · by_cases hx : x = 0
    · exact Or.inl hx
    · exact Or.inr (isUnit_iff_ne_zero.mpr hx)
  · obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq (c : K) two_pos
    have hd0 : d ≠ 0 := by
      rintro rfl
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hd
      exact c.ne_zero hd.symm
    refine ⟨Units.mk0 d hd0, ?_⟩
    ext
    simp [← hd, sq]
  · obtain ⟨d, hd⟩ := IsAlgClosed.exists_root (Polynomial.X ^ 4 - Polynomial.X - 1 : Polynomial K)
      (by
        rw [show (Polynomial.X ^ 4 - Polynomial.X - 1 : Polynomial K).degree = 4 by
          compute_degree!]
        decide)
    simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one] at hd
    have hd0 : d ≠ 0 := by
      rintro rfl
      norm_num at hd
    refine ⟨Units.mk0 d hd0, fun h => hd0 ?_⟩
    have h4 := congrArg Units.val h
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] at h4
    linear_combination h4 - hd

/-- The ring of global sections of the spectrum of an algebraically closed field. -/
theorem sqField_Γ_Spec (K : Type u) [Field K] [IsAlgClosed K] :
    SqField Γ(Spec (CommRingCat.of K), ⊤) :=
  (sqField_of_isAlgClosed K).of_ringEquiv
    (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv

/-! ### The base point -/

/-- The base `Spec k` as a test scheme. -/
abbrev base (k : Type u) [Field k] : Over (Spec (CommRingCat.of k)) := Over.mk (𝟙 _)

/-- The structure morphism of a test scheme. -/
def toBase (Z : Over (Spec (CommRingCat.of k))) : Z ⟶ base k :=
  Over.homMk Z.hom (by simp)

theorem toBase_eq {Z : Over (Spec (CommRingCat.of k))} (f : Z ⟶ base k) : f = toBase Z := by
  apply Over.OverMorphism.ext
  simpa [toBase] using Over.w f

theorem comp_toBase {Z W : Over (Spec (CommRingCat.of k))} (f : W ⟶ Z) :
    f ≫ toBase Z = toBase W :=
  toBase_eq _

theorem field_base (x : Γ((base k).left, ⊤)) : x = 0 ∨ IsUnit x := by
  have e := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  by_cases hx : e x = 0
  · left
    exact e.injective (hx.trans (map_zero e).symm)
  · right
    have := (isUnit_iff_ne_zero.mpr hx).map e.symm.toMonoidHom
    simpa using this

theorem surjective_toBase_left (Z : Over (Spec (CommRingCat.of k))) [Nonempty Z.left] :
    Function.Surjective (toBase Z).left := by
  intro z
  obtain ⟨w⟩ := ‹Nonempty Z.left›
  exact ⟨w, Subsingleton.elim (α := PrimeSpectrum k) _ _⟩

/-! ### Further cell identities -/

namespace CellData

variable (D : CellData k) {Z : Over (Spec (CommRingCat.of k))}

theorem cellPt_zero_right (y : Γ(Z.left, ⊤)) (t : Z ⟶ D.T.X) :
    D.cellPt y t 0 = D.B y * D.I t := by
  rw [cellPt, A_zero, mul_one]

theorem I_mul_A_eq_cellPt (t : Z ⟶ D.T.X) (x : Γ(Z.left, ⊤)) :
    D.I t * D.A x = D.cellPt 0 t x := by
  rw [cellPt, B_zero, one_mul]

theorem I_mul_B' (t : Z ⟶ D.T.X) (y : Γ(Z.left, ⊤)) :
    D.B ((↑(cu D.α t)⁻¹ : Γ(Z.left, ⊤)) * y) = D.I t * D.B y * (D.I t)⁻¹ := by
  rw [I_mul_B, mul_inv_cancel_right]

/-- If `xp(x) xm(y)` lies in `xm(𝔾ₐ) T`, then `x = 0`. -/
theorem eq_zero_of_A_mul_B {x y y' : Γ(Z.left, ⊤)} {t : Z ⟶ D.T.X}
    (h : D.A x * D.B y = D.B y' * D.I t) : x = 0 := by
  have h1 : D.A x = D.cellPt (y' + (↑(cu D.α t)⁻¹ : Γ(Z.left, ⊤)) * -y) t 0 := by
    rw [cellPt_zero_right, B_add, mul_assoc, ← I_mul_B, ← mul_assoc, ← h, mul_assoc, ← B_add,
      add_neg_cancel, B_zero, mul_one]
  rw [A_eq_cellPt] at h1
  exact (D.cellPt_inj h1).2.2

end CellData

/-! ### Weyl data -/

/-- Cell data together with a cocharacter `h` pairing to two with `α`, a point `n` of `G`
normalizing the torus through the reflection `1 - α ≫ h` and with square in the torus, on an
irreducible group. -/
structure WeylData (k : Type u) [Field k] extends CellData k where
  h : cocharacterLattice T
  pair : latticePairing T α h = 2
  n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X
  hn : IsNormalizingPoint i n (latticeReflectionIso α h pair)
  hn2 : ∃ z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ T.X, n * n = z ≫ i.hom.hom
  irreducible : IrreducibleSpace G.X.left

namespace WeylData

variable (D : WeylData k) {Z W : Over (Spec (CommRingCat.of k))}

/-- The point `h(c)` of the torus. -/
def tH (c : Γ(Z.left, ⊤)ˣ) : Z ⟶ D.T.X :=
  (Gm.pointsEquiv _ Z).symm c ≫ (CommGroupScheme.groupHom D.h).hom.hom

/-- The point `h(c)` of `G`. -/
def H (c : Γ(Z.left, ⊤)ˣ) : Z ⟶ D.G.X := D.I (D.tH c)

/-- The Weyl point over a test scheme. -/
def N (Z : Over (Spec (CommRingCat.of k))) : Z ⟶ D.G.X := D.G.constantPoint D.n Z

theorem hh : D.h ≫ D.α = (2 : ℤ) • 𝟙 (Gm (Spec (CommRingCat.of k))) := by
  rw [eq_gmEndEquiv_zsmul k (D.h ≫ D.α)]
  exact congrArg (fun m : ℤ => m • 𝟙 (Gm (Spec (CommRingCat.of k)))) D.pair

theorem tH_mul (c d : Γ(Z.left, ⊤)ˣ) : D.tH (c * d) = D.tH c * D.tH d := by
  rw [tH, tH, tH, map_mul, MonObj.mul_comp]

theorem tH_one : D.tH (1 : Γ(Z.left, ⊤)ˣ) = 1 := by
  rw [tH, map_one, MonObj.one_comp]

theorem tH_inv (c : Γ(Z.left, ⊤)ˣ) : D.tH c⁻¹ = (D.tH c)⁻¹ := by
  rw [tH, tH, map_inv, GrpObj.inv_comp]

theorem H_mul (c d : Γ(Z.left, ⊤)ˣ) : D.H (c * d) = D.H c * D.H d := by
  rw [H, H, H, tH_mul, CellData.I_mul]

theorem H_inv (c : Γ(Z.left, ⊤)ˣ) : D.H c⁻¹ = (D.H c)⁻¹ := by
  rw [H, H, tH_inv, CellData.I_inv]

theorem cu_tH (c : Γ(Z.left, ⊤)ˣ) : cu D.α (D.tH c) = c * c := by
  have h2 := Gm.comp_zsmul_id ((Gm.pointsEquiv _ Z).symm c) 2
  rw [← D.hh, comp_groupHom_comp] at h2
  rw [cu, tH, h2, map_zpow, MulEquiv.apply_symm_apply, zpow_two]

theorem comp_tH (f : W ⟶ Z) (c : Γ(Z.left, ⊤)ˣ) :
    f ≫ D.tH c = D.tH (Units.map f.left.appTop.hom.toMonoidHom c) := by
  rw [tH, tH, ← Category.assoc]
  congr 1
  apply (Gm.pointsEquiv _ W).injective
  rw [Gm.pointsEquiv_naturality, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

theorem comp_N (f : W ⟶ Z) : f ≫ D.N Z = D.N W :=
  D.G.constantPoint_naturality D.n f

/-- Conjugation by the Weyl point acts on the torus through the reflection. -/
theorem N_mul_I (t : Z ⟶ D.T.X) :
    D.N Z * D.I t * (D.N Z)⁻¹ =
      D.I (t ≫ (CommGroupScheme.groupHom (𝟙 D.T - D.α ≫ D.h)).hom.hom) :=
  D.hn.conj_comp Z t

theorem tH_comp_reflection (c : Γ(Z.left, ⊤)ˣ) :
    D.tH c ≫ (CommGroupScheme.groupHom (𝟙 D.T - D.α ≫ D.h)).hom.hom = (D.tH c)⁻¹ := by
  have hneg : D.tH c ≫ (CommGroupScheme.groupHom (-(D.α ≫ D.h))).hom.hom =
      (D.tH c ≫ (CommGroupScheme.groupHom (D.α ≫ D.h)).hom.hom)⁻¹ :=
    congrArg Additive.toMul ((evalPoint (D.tH c)).map_neg (D.α ≫ D.h))
  have hid : D.tH c ≫ (CommGroupScheme.groupHom (𝟙 D.T)).hom.hom = D.tH c := by
    rw [show (CommGroupScheme.groupHom (𝟙 D.T)).hom.hom = 𝟙 D.T.X from rfl, Category.comp_id]
  have hah : D.tH c ≫ (CommGroupScheme.groupHom (D.α ≫ D.h)).hom.hom = D.tH c * D.tH c := by
    rw [comp_groupHom_comp, ← D.tH_mul, ← D.cu_tH]
    simp only [tH, cu, MulEquiv.symm_apply_apply]
  rw [sub_eq_add_neg, comp_groupHom_add, hneg, hid, hah, mul_inv_rev, mul_inv_cancel_left]

theorem N_mul_H (c : Γ(Z.left, ⊤)ˣ) : D.N Z * D.H c * (D.N Z)⁻¹ = (D.H c)⁻¹ := by
  rw [H, N_mul_I, tH_comp_reflection, CellData.I_inv]

theorem N_mul_H' (c : Γ(Z.left, ⊤)ˣ) : D.N Z * D.H c = (D.H c)⁻¹ * D.N Z := by
  rw [← D.N_mul_H c, inv_mul_cancel_right]

theorem H_mul_N (c : Γ(Z.left, ⊤)ˣ) : D.H c * D.N Z = D.N Z * (D.H c)⁻¹ := by
  have := D.N_mul_H' c⁻¹
  rw [H_inv, inv_inv] at this
  exact this.symm

theorem inv_H_mul_N (c : Γ(Z.left, ⊤)ˣ) : (D.H c)⁻¹ * D.N Z = D.N Z * D.H c :=
  (D.N_mul_H' c).symm

theorem I_mul_A' (t : Z ⟶ D.T.X) (x : Γ(Z.left, ⊤)) :
    D.A ((↑(cu D.α t) : Γ(Z.left, ⊤)) * x) = D.I t * D.A x * (D.I t)⁻¹ := by
  rw [CellData.I_mul_A, mul_inv_cancel_right]

/-- **Equivariance.** `xp(c²x) n = h(c) xp(x) n h(c)`. -/
theorem A_mul_N (c : Γ(Z.left, ⊤)ˣ) (x : Γ(Z.left, ⊤)) :
    D.A ((↑(c * c) : Γ(Z.left, ⊤)) * x) * D.N Z = D.H c * (D.A x * D.N Z) * D.H c := by
  have h := D.I_mul_A' (D.tH c) x
  rw [cu_tH] at h
  rw [h, ← H, mul_assoc, inv_H_mul_N]
  simp only [mul_assoc]

/-- **The Weyl point is not in the open cell** over a test scheme with a unit whose fourth
power is not one. -/
theorem not_inCell_N (hc : ∃ c : Γ(Z.left, ⊤)ˣ, c ^ 4 ≠ 1) : ¬ D.InCell (D.N Z) := by
  obtain ⟨c, hc⟩ := hc
  intro hN
  obtain ⟨y, t, x, hyx⟩ := (D.inCell_iff _).mp hN
  have h1 : D.H c * D.N Z * (D.H c)⁻¹ = D.H c * D.H c * D.N Z := by
    rw [mul_assoc, ← D.H_mul_N, ← mul_assoc]
  rw [hyx, H, ← CellData.I_inv, CellData.I_mul_cellPt, CellData.cellPt_mul_I, ← CellData.I_mul,
    CellData.I_mul_cellPt] at h1
  have h2 := (D.cellPt_inj h1).2.1
  have h3 : D.tH c * D.tH c = 1 := by
    have : D.tH c * t * (D.tH c)⁻¹ = t := by
      rw [mul_comm (D.tH c) t, mul_inv_cancel_right]
    rw [this] at h2
    exact (mul_eq_right.mp h2.symm)
  apply hc
  have := congrArg (cu D.α) h3
  rw [cu_mul, cu_tH, cu_one] at this
  rw [← this, ← sq, ← sq, ← pow_mul]

/-! ### The point `xp(1) n` lies in the open cell -/

/-- Right multiplication by the Weyl point, as an endomorphism of the scheme of `G`. -/
def rho : D.G.X ⟶ D.G.X := 𝟙 D.G.X * D.N D.G.X

theorem comp_rho (g : Z ⟶ D.G.X) : g ≫ D.rho = g * D.N Z := by
  rw [rho, MonObj.comp_mul, Category.comp_id, comp_N]

theorem cellMul_mem_range {g : Z ⟶ D.G.X} (hg : D.InCell g) (z : Z.left) :
    g.left z ∈ Set.range D.cellMul.left :=
  D.range_subset_of_inCell hg ⟨z, rfl⟩

/-- Over a test scheme with square roots, if some `g` and `g n` lie in the open cell, then so
does `xp(1) n`. -/
theorem inCell_A_one_mul_N_of_sqField (hW : SqField Γ(Z.left, ⊤)) {g : Z ⟶ D.G.X}
    (hg : D.InCell g) (hgN : D.InCell (g * D.N Z)) : D.InCell (D.A 1 * D.N Z) := by
  obtain ⟨hz, hsqrt, c4⟩ := hW
  obtain ⟨y, t, x, hyx⟩ := (D.inCell_iff g).mp hg
  have hxN : D.InCell (D.A x * D.N Z) := by
    have : D.A x * D.N Z = D.I t⁻¹ * (D.B (-y) * (g * D.N Z)) := by
      rw [hyx, CellData.cellPt, CellData.B_neg, CellData.I_inv]
      simp only [mul_assoc, inv_mul_cancel_left]
    rw [this]
    exact CellData.InCell.I_mul _ (CellData.InCell.B_mul _ hgN _) _
  rcases hz x with rfl | hx
  · rw [CellData.A_zero, one_mul] at hxN
    exact absurd hxN (D.not_inCell_N c4)
  · obtain ⟨c, hc⟩ := hsqrt hx.unit
    have h1 := D.A_mul_N c 1
    rw [hc, IsUnit.unit_spec, mul_one] at h1
    have : D.A 1 * D.N Z = D.I (D.tH c)⁻¹ * (D.A x * D.N Z) * D.I (D.tH c)⁻¹ := by
      rw [h1, H, CellData.I_inv]
      simp only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one]
    rw [this]
    exact CellData.InCell.mul_I _ (CellData.InCell.I_mul _ hxN _) _

/-- **The point `xp(1) n` lies in the open cell** over the base. -/
theorem inCell_A_one_mul_N : D.InCell (D.A (1 : Γ((base k).left, ⊤)) * D.N (base k)) := by
  have hopen := D.open_cell
  have := D.irreducible
  have hΩ : IsOpen (Set.range D.cellMul.left) := IsOpenImmersion.isOpen_range _
  obtain ⟨p⟩ : Nonempty (base k).left := inferInstanceAs (Nonempty (Spec (CommRingCat.of k)))
  have hne1 : (Set.range D.cellMul.left).Nonempty := by
    refine ⟨_, D.cellMul_mem_range (g := (1 : base k ⟶ D.G.X)) ?_ p⟩
    rw [CellData.one_eq_cellPt]
    exact D.inCell_cellPt _ _ _
  have hne2 : (D.rho.left ⁻¹' Set.range D.cellMul.left).Nonempty := by
    refine ⟨(D.n⁻¹).left p, ?_⟩
    have h : D.rho.left ((D.n⁻¹).left p) = (D.n⁻¹ ≫ D.rho).left p := by
      rw [Over.comp_left, Scheme.Hom.comp_apply]
    rw [Set.mem_preimage, h, comp_rho, N, constantPoint_self, inv_mul_cancel]
    apply D.cellMul_mem_range
    rw [CellData.one_eq_cellPt]
    exact D.inCell_cellPt _ _ _
  obtain ⟨u, hu1, hu2⟩ :=
    nonempty_preirreducible_inter hΩ (hΩ.preimage D.rho.left.continuous) hne1 hne2
  have hpt : ∀ w, (geometricPoint D.G.X.left u) w = u := fun w => by
    rw [geometricPoint, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  let W : Over (Spec (CommRingCat.of k)) := Over.mk (geometricPoint D.G.X.left u ≫ D.G.X.hom)
  have : Nonempty W.left :=
    inferInstanceAs (Nonempty (Spec (CommRingCat.of (AlgebraicClosure
      (D.G.X.left.residueField u)))))
  let g : W ⟶ D.G.X := Over.homMk (geometricPoint D.G.X.left u) rfl
  have hg : D.InCell g := by
    apply D.inCell_of_range_subset
    rintro _ ⟨w, rfl⟩
    change (geometricPoint D.G.X.left u) w ∈ _
    rw [hpt]
    exact hu1
  have hgN : D.InCell (g * D.N W) := by
    rw [← comp_rho]
    apply D.inCell_of_range_subset
    rintro _ ⟨w, rfl⟩
    rw [Over.comp_left, Scheme.Hom.comp_apply]
    change D.rho.left ((geometricPoint D.G.X.left u) w) ∈ _
    rw [hpt]
    exact hu2
  have hW := D.inCell_A_one_mul_N_of_sqField
    (sqField_Γ_Spec (AlgebraicClosure (D.G.X.left.residueField u))) hg hgN
  have hcomp : toBase W ≫ (D.A 1 * D.N (base k)) = D.A 1 * D.N W := by
    rw [MonObj.comp_mul, CellData.comp_A, comp_N, map_one]
  rw [← hcomp] at hW
  exact CellData.InCell.of_comp _ (surjective_toBase_left W) hW

/-! ### The constants of `xp(1) n` -/

/-- The Weyl point is not in the open cell over the base. -/
theorem not_inCell_N_base : ¬ D.InCell (D.N (base k)) := by
  intro h
  have hW := CellData.InCell.comp _ h (toBase (Over.mk (toAlgebraicClosure k)))
  rw [comp_N] at hW
  exact D.not_inCell_N (sqField_Γ_Spec (AlgebraicClosure k)).2.2 hW

theorem exists_A_one_mul_N :
    ∃ b g d, D.A (1 : Γ((base k).left, ⊤)) * D.N (base k) = D.cellPt b g d :=
  (D.inCell_iff _).mp D.inCell_A_one_mul_N

/-- The `xm`-coordinate `β` of `xp(1) n = xm(β) γ xp(δ)`. -/
def cβ : Γ((base k).left, ⊤) := D.exists_A_one_mul_N.choose

/-- The torus component `γ` of `xp(1) n = xm(β) γ xp(δ)`. -/
def ct : base k ⟶ D.T.X := D.exists_A_one_mul_N.choose_spec.choose

/-- The `xp`-coordinate `δ` of `xp(1) n = xm(β) γ xp(δ)`. -/
def cδ : Γ((base k).left, ⊤) := D.exists_A_one_mul_N.choose_spec.choose_spec.choose

theorem A_one_mul_N_base :
    D.A (1 : Γ((base k).left, ⊤)) * D.N (base k) = D.cellPt D.cβ D.ct D.cδ :=
  D.exists_A_one_mul_N.choose_spec.choose_spec.choose_spec

/-- Pull back a global section of the base to a test scheme. -/
abbrev pb (Z : Over (Spec (CommRingCat.of k))) (x : Γ((base k).left, ⊤)) : Γ(Z.left, ⊤) :=
  (toBase Z).left.appTop x

theorem N_eq_comp (Z : Over (Spec (CommRingCat.of k))) : D.N Z = toBase Z ≫ D.n := rfl

theorem A_one_mul_N (Z : Over (Spec (CommRingCat.of k))) :
    D.A (1 : Γ(Z.left, ⊤)) * D.N Z = D.cellPt (pb Z D.cβ) (toBase Z ≫ D.ct) (pb Z D.cδ) := by
  have h := congrArg (fun g => toBase Z ≫ g) D.A_one_mul_N_base
  rw [MonObj.comp_mul, CellData.comp_A, comp_N, map_one, CellData.comp_cellPt] at h
  exact h

/-- `xp(c²) n = xm(c⁻² β) h(c) γ h(c) xp(c⁻² δ)`. -/
theorem A_sq_mul_N (c : Γ(Z.left, ⊤)ˣ) :
    D.A (↑(c * c) : Γ(Z.left, ⊤)) * D.N Z =
      D.cellPt ((↑(c * c)⁻¹ : Γ(Z.left, ⊤)) * pb Z D.cβ) (D.tH c * (toBase Z ≫ D.ct) * D.tH c)
        ((↑(c * c)⁻¹ : Γ(Z.left, ⊤)) * pb Z D.cδ) := by
  have h := D.A_mul_N c 1
  rw [mul_one, A_one_mul_N, H, CellData.I_mul_cellPt, CellData.cellPt_mul_I, cu_tH] at h
  exact h

theorem N_mul_N (Z : Over (Spec (CommRingCat.of k))) :
    ∃ z : Z ⟶ D.T.X, D.N Z * D.N Z = D.I z := by
  obtain ⟨z₀, hz₀⟩ := D.hn2
  refine ⟨toBase Z ≫ z₀, ?_⟩
  rw [N_eq_comp, ← MonObj.comp_mul, hz₀, CellData.I, Category.assoc]

theorem inCell_A (x : Γ(Z.left, ⊤)) : D.InCell (D.A x) := by
  rw [CellData.A_eq_cellPt]
  exact D.inCell_cellPt _ _ _

/-- **`β` is a unit.** -/
theorem cβ_isUnit : IsUnit D.cβ := by
  rcases field_base D.cβ with h | h
  · exfalso
    apply D.not_inCell_N_base
    have h1 := D.A_one_mul_N_base
    rw [h, CellData.cellPt, CellData.B_zero, one_mul] at h1
    have : D.N (base k) = D.I D.ct * D.A ((↑(cu D.α D.ct)⁻¹ : Γ((base k).left, ⊤)) * -1 + D.cδ) := by
      rw [CellData.A_add, ← mul_assoc, ← CellData.A_mul_I, mul_assoc, ← h1, ← mul_assoc,
        ← CellData.A_add, neg_add_cancel, CellData.A_zero, one_mul]
    rw [this]
    exact CellData.InCell.I_mul _ (D.inCell_A _) _
  · exact h

theorem eq_zero_of_two {x x' y y' : Γ(Z.left, ⊤)} {t t' : Z ⟶ D.T.X}
    (h1 : D.A x * D.N Z = D.B y * D.I t) (h2 : D.A x' * D.N Z = D.B y' * D.I t') :
    x - x' = 0 := by
  apply D.eq_zero_of_A_mul_B (y := y') (y' := y) (t := t * t'⁻¹)
  calc D.A (x - x') * D.B y' = D.A (x - x') * (D.B y' * D.I t') * (D.I t')⁻¹ := by
        simp only [mul_assoc, mul_inv_cancel, mul_one]
    _ = D.A (x - x') * (D.A x' * D.N Z) * (D.I t')⁻¹ := by rw [h2]
    _ = D.A x * D.N Z * (D.I t')⁻¹ := by rw [← mul_assoc, ← CellData.A_add, sub_add_cancel]
    _ = D.B y * D.I t * (D.I t')⁻¹ := by rw [h1]
    _ = D.B y * D.I (t * t'⁻¹) := by rw [CellData.I_mul, CellData.I_inv, mul_assoc]

/-- **`δ` is a unit.** -/
theorem cδ_isUnit : IsUnit D.cδ := by
  rcases field_base D.cδ with h | h
  · exfalso
    obtain ⟨-, -, c, hc⟩ := sqField_Γ_Spec (AlgebraicClosure k)
    have h1 := D.A_one_mul_N (Over.mk (toAlgebraicClosure k))
    have h2 := D.A_sq_mul_N (Z := Over.mk (toAlgebraicClosure k)) c
    have h0 : pb (Over.mk (toAlgebraicClosure k)) (0 : Γ((base k).left, ⊤)) = 0 := map_zero _
    rw [h, h0, CellData.cellPt_zero_right] at h1
    rw [h, h0, mul_zero, CellData.cellPt_zero_right] at h2
    have h3 := D.eq_zero_of_two h1 h2
    apply hc
    have h4 : c * c = 1 := Units.ext (by rw [Units.val_one]; exact (sub_eq_zero.mp h3).symm)
    rw [← sq] at h4
    rw [show 4 = 2 * 2 from rfl, pow_mul, h4, one_pow]
  · exact h

theorem cu_mul_eq_neg_one_aux {β δ : Γ(Z.left, ⊤)} {g g' z : Z ⟶ D.T.X} (r : Γ(Z.left, ⊤)ˣ)
    (hβ : IsUnit β) (hr : (r : Γ(Z.left, ⊤)) = δ)
    (e1 : D.A 1 * D.N Z = D.cellPt β g δ)
    (e2 : D.A δ * D.N Z = D.cellPt ((↑r⁻¹ : Γ(Z.left, ⊤)) * β) g' 1)
    (hz : D.N Z * D.N Z = D.I z) :
    (cu D.α g : Γ(Z.left, ⊤)) * δ = -1 := by
  have hN1 : D.N Z = D.A (-1) * D.cellPt β g δ := by
    rw [← e1, ← mul_assoc, ← CellData.A_add, neg_add_cancel, CellData.A_zero, one_mul]
  have hN2 : D.N Z = D.A (-δ) * D.cellPt ((↑r⁻¹ : Γ(Z.left, ⊤)) * β) g' 1 := by
    rw [← e2, ← mul_assoc, ← CellData.A_add, neg_add_cancel, CellData.A_zero, one_mul]
  have hP : D.N Z * D.N Z =
      D.A (-1) * D.cellPt (β + (↑(cu D.α g)⁻¹ : Γ(Z.left, ⊤)) * ((↑r⁻¹ : Γ(Z.left, ⊤)) * β)) (g * g') 1 := by
    calc D.N Z * D.N Z = D.A (-1) * D.cellPt β g δ * (D.A (-δ) * D.cellPt ((↑r⁻¹ : Γ(Z.left, ⊤)) * β) g' 1) :=
          congrArg₂ (· * ·) hN1 hN2
      _ = D.A (-1) * (D.cellPt β g δ * D.A (-δ) * D.cellPt ((↑r⁻¹ : Γ(Z.left, ⊤)) * β) g' 1) := by
          simp only [mul_assoc]
      _ = D.A (-1) * (D.B β * (D.I g * D.cellPt ((↑r⁻¹ : Γ(Z.left, ⊤)) * β) g' 1)) := by
          rw [CellData.cellPt_mul_A, add_neg_cancel, CellData.cellPt_zero_right, mul_assoc]
      _ = _ := by rw [CellData.I_mul_cellPt, CellData.B_mul_cellPt]
  have hP' : D.cellPt (β + (↑(cu D.α g)⁻¹ : Γ(Z.left, ⊤)) * ((↑r⁻¹ : Γ(Z.left, ⊤)) * β)) (g * g') 1 =
      D.cellPt 0 z ((↑(cu D.α z)⁻¹ : Γ(Z.left, ⊤)) * 1) := by
    rw [← CellData.I_mul_A_eq_cellPt, ← CellData.A_mul_I, ← hz, hP, ← mul_assoc (D.A 1),
      ← CellData.A_add, add_neg_cancel, CellData.A_zero, one_mul]
  have h0 := (D.cellPt_inj hP').1
  obtain ⟨b, rfl⟩ := hβ
  have hl := Units.mul_inv (cu D.α g)
  have hrr := Units.mul_inv r
  have hb := Units.mul_inv b
  linear_combination ((cu D.α g : Γ(Z.left, ⊤)) * ↑r * ↑b⁻¹) * h0 - (cu D.α g : Γ(Z.left, ⊤)) * hr
    - ((cu D.α g : Γ(Z.left, ⊤)) * ↑r + 1) * hb - (↑r * ↑r⁻¹ * ↑b * ↑b⁻¹) * hl
    - (↑b * ↑b⁻¹) * hrr

/-- **`λ δ = -1`** for `λ = α(γ)`, over a test scheme where `δ` is a square. -/
theorem cu_ct_mul_cδ (d : Γ(Z.left, ⊤)ˣ) (hd : (↑(d * d) : Γ(Z.left, ⊤)) = pb Z D.cδ) :
    (cu D.α (toBase Z ≫ D.ct) : Γ(Z.left, ⊤)) * pb Z D.cδ = -1 := by
  obtain ⟨z, hz⟩ := D.N_mul_N Z
  have e2 := D.A_sq_mul_N d
  have h1 : (↑(d * d)⁻¹ : Γ(Z.left, ⊤)) * pb Z D.cδ = 1 := by
    rw [← hd, Units.inv_mul]
  rw [hd, h1] at e2
  exact D.cu_mul_eq_neg_one_aux (d * d) (D.cβ_isUnit.map (toBase Z).left.appTop.hom) hd
    (D.A_one_mul_N Z) e2 hz

/-! ### The rank-one relation over test schemes with square roots -/

/-- From `xp(r) n` and `xp(s) n` in the normal form of `xp(c²) n`, the product
`xp(r - s) xm(s⁻¹ β)` lies in the open cell. -/
theorem A_sub_mul_B_aux {β δ : Γ(Z.left, ⊤)} {gr gs : Z ⟶ D.T.X} (r s : Γ(Z.left, ⊤)ˣ)
    (er : D.A (r : Γ(Z.left, ⊤)) * D.N Z =
      D.cellPt ((↑r⁻¹ : Γ(Z.left, ⊤)) * β) gr ((↑r⁻¹ : Γ(Z.left, ⊤)) * δ))
    (es : D.A (s : Γ(Z.left, ⊤)) * D.N Z =
      D.cellPt ((↑s⁻¹ : Γ(Z.left, ⊤)) * β) gs ((↑s⁻¹ : Γ(Z.left, ⊤)) * δ)) :
    D.A ((r : Γ(Z.left, ⊤)) - (s : Γ(Z.left, ⊤))) * D.B ((↑s⁻¹ : Γ(Z.left, ⊤)) * β) =
      D.cellPt ((↑r⁻¹ : Γ(Z.left, ⊤)) * β) (gr * gs⁻¹)
        ((cu D.α gs : Γ(Z.left, ⊤)) *
          ((↑r⁻¹ : Γ(Z.left, ⊤)) * δ - (↑s⁻¹ : Γ(Z.left, ⊤)) * δ)) := by
  have h1 : D.A ((r : Γ(Z.left, ⊤)) - (s : Γ(Z.left, ⊤))) *
      D.cellPt ((↑s⁻¹ : Γ(Z.left, ⊤)) * β) gs ((↑s⁻¹ : Γ(Z.left, ⊤)) * δ) =
      D.cellPt ((↑r⁻¹ : Γ(Z.left, ⊤)) * β) gr ((↑r⁻¹ : Γ(Z.left, ⊤)) * δ) := by
    rw [← es, ← er, ← mul_assoc, ← CellData.A_add, sub_add_cancel]
  calc D.A ((r : Γ(Z.left, ⊤)) - (s : Γ(Z.left, ⊤))) * D.B ((↑s⁻¹ : Γ(Z.left, ⊤)) * β)
      = D.A ((r : Γ(Z.left, ⊤)) - (s : Γ(Z.left, ⊤))) *
          D.cellPt ((↑s⁻¹ : Γ(Z.left, ⊤)) * β) gs ((↑s⁻¹ : Γ(Z.left, ⊤)) * δ) *
          D.A (-((↑s⁻¹ : Γ(Z.left, ⊤)) * δ)) * D.I gs⁻¹ := by
        rw [CellData.cellPt, CellData.A_neg, CellData.I_inv]
        simp only [mul_assoc, mul_inv_cancel, mul_one]
    _ = _ := by
        rw [h1, CellData.cellPt_mul_A, CellData.cellPt_mul_I, cu_inv, inv_inv, ← sub_eq_add_neg]

/-- **The rank-one relation** over a test scheme with square roots:
`xp(X) xm(β Y) = xm(β u⁻¹ Y) h(u) xp(u⁻¹ X)` for `u = 1 + XY`. -/
theorem rel_of_sqField (hZ : SqField Γ(Z.left, ⊤)) (X Y : Γ(Z.left, ⊤)) (u : Γ(Z.left, ⊤)ˣ)
    (hu : (u : Γ(Z.left, ⊤)) = 1 + X * Y) :
    D.A X * D.B (pb Z D.cβ * Y) =
      D.cellPt (pb Z D.cβ * ((↑u⁻¹ : Γ(Z.left, ⊤)) * Y)) (D.tH u) ((↑u⁻¹ : Γ(Z.left, ⊤)) * X) := by
  rcases hZ.1 Y with rfl | ⟨w, rfl⟩
  · obtain rfl : u = 1 := Units.ext (by rw [hu, mul_zero, add_zero, Units.val_one])
    simp only [mul_zero, inv_one, Units.val_one, one_mul, mul_one, CellData.B_zero, tH_one]
    exact D.A_eq_cellPt X
  · have hδ : IsUnit (pb Z D.cδ) := D.cδ_isUnit.map (toBase Z).left.appTop.hom
    obtain ⟨d, hd⟩ := hZ.2.1 hδ.unit
    have hl := D.cu_ct_mul_cδ d (by rw [hd, IsUnit.unit_spec])
    obtain ⟨c', hc'⟩ := hZ.2.1 w⁻¹
    obtain ⟨c, hc⟩ := hZ.2.1 (u * w⁻¹)
    have hw := Units.mul_inv w
    have hu' := Units.mul_inv u
    have ha : X = (↑(c * c) : Γ(Z.left, ⊤)) - (↑(c' * c') : Γ(Z.left, ⊤)) := by
      rw [hc, hc', Units.val_mul]
      linear_combination -X * hw - (↑w⁻¹ : Γ(Z.left, ⊤)) * hu
    have hb : pb Z D.cβ * ↑w = (↑(c' * c')⁻¹ : Γ(Z.left, ⊤)) * pb Z D.cβ := by
      rw [hc', inv_inv, mul_comm]
    have key : D.tH u * (D.tH c' * D.tH c') = D.tH c * D.tH c := by
      rw [← D.tH_mul c', ← D.tH_mul u, ← D.tH_mul c, hc', hc]
    calc D.A X * D.B (pb Z D.cβ * ↑w)
        = D.A ((↑(c * c) : Γ(Z.left, ⊤)) - (↑(c' * c') : Γ(Z.left, ⊤))) * D.B ((↑(c' * c')⁻¹ : Γ(Z.left, ⊤)) * pb Z D.cβ) := by
          rw [← ha, hb]
      _ = _ := D.A_sub_mul_B_aux (c * c) (c' * c') (D.A_sq_mul_N c) (D.A_sq_mul_N c')
      _ = _ := by
          congr 1
          · rw [hc]
            simp only [mul_inv_rev, inv_inv, Units.val_mul]
            ring
          · rw [mul_inv_eq_iff_eq_mul]
            calc D.tH c * (toBase Z ≫ D.ct) * D.tH c
                = (toBase Z ≫ D.ct) * (D.tH c * D.tH c) := by
                  rw [mul_comm (D.tH c) (toBase Z ≫ D.ct), mul_assoc]
              _ = D.tH u * (D.tH c' * (toBase Z ≫ D.ct) * D.tH c') := by
                  rw [← key, mul_comm (D.tH c') (toBase Z ≫ D.ct), mul_assoc (toBase Z ≫ D.ct),
                    mul_left_comm (toBase Z ≫ D.ct) (D.tH u)]
          · rw [cu_mul, cu_mul, cu_tH, hc, hc']
            simp only [mul_inv_rev, inv_inv, Units.val_mul]
            linear_combination (↑u⁻¹ : Γ(Z.left, ⊤)) * (↑w⁻¹ : Γ(Z.left, ⊤)) * hu -
              (↑w⁻¹ : Γ(Z.left, ⊤)) * hu' -
              ((↑w⁻¹ : Γ(Z.left, ⊤)) * ((↑u⁻¹ : Γ(Z.left, ⊤)) - 1) -
                (↑u⁻¹ : Γ(Z.left, ⊤)) * X) * hw +
              (↑w⁻¹ : Γ(Z.left, ⊤)) * (↑w⁻¹ : Γ(Z.left, ⊤)) * ↑w *
                ((↑u⁻¹ : Γ(Z.left, ⊤)) - 1) * hl

/-- Over a test scheme with square roots, `xp(X) xm(β Y)` is not in the open cell when
`1 + XY = 0`. -/
theorem not_inCell_of_sqField (hZ : SqField Γ(Z.left, ⊤)) (X Y : Γ(Z.left, ⊤))
    (h : 1 + X * Y = 0) : ¬ D.InCell (D.A X * D.B (pb Z D.cβ * Y)) := by
  intro hin
  rcases hZ.1 Y with rfl | ⟨w, rfl⟩
  · obtain ⟨c, hc⟩ := hZ.2.2
    have h01 : (1 : Γ(Z.left, ⊤)) = 0 := by simpa using h
    have h0 : ∀ a : Γ(Z.left, ⊤), a = 0 := fun a => by rw [← mul_one a, h01, mul_zero]
    exact hc (Units.ext ((h0 _).trans (h0 _).symm))
  · obtain ⟨c, hc⟩ := hZ.2.1 w⁻¹
    have hX : X = ↑(cu D.α (D.tH c)) * -1 := by
      rw [D.cu_tH, hc]
      linear_combination (↑w⁻¹ : Γ(Z.left, ⊤)) * h - X * Units.mul_inv w
    have hY : pb Z D.cβ * ↑w = (↑(cu D.α (D.tH c))⁻¹ : Γ(Z.left, ⊤)) * pb Z D.cβ := by
      rw [D.cu_tH, hc, inv_inv, mul_comm]
    rw [hX, hY, D.I_mul_A', D.I_mul_B'] at hin
    have h1 : D.InCell (D.A (-1) * D.B (pb Z D.cβ)) := by
      have := CellData.InCell.mul_I _ (CellData.InCell.I_mul _ hin (D.tH c)⁻¹) (D.tH c)
      convert this using 1
      rw [CellData.I_inv]
      simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
    have hN : D.N Z = D.A (-1) * D.B (pb Z D.cβ) * D.I (toBase Z ≫ D.ct) * D.A (pb Z D.cδ) := by
      calc D.N Z = D.A (-1) * (D.A 1 * D.N Z) := by
            rw [← mul_assoc, ← CellData.A_add, neg_add_cancel, CellData.A_zero, one_mul]
        _ = _ := by
            rw [D.A_one_mul_N Z, CellData.cellPt]
            simp only [mul_assoc]
    apply D.not_inCell_N hZ.2.2
    rw [hN]
    exact CellData.InCell.mul_A _ (CellData.InCell.mul_I _ h1 _) _

end WeylData

end RankOneRootCellRelation

end Langlands.GroupScheme
