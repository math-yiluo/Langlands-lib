import Langlands.GroupScheme.Reductive.RankOneCoverTorus
import Langlands.GroupScheme.Reductive.SplitRankOnePowerIsogeny
import Langlands.GroupScheme.Reductive.RankOneCentralCoverStatement
import Langlands.GroupScheme.Reductive.DirectProductProof
import Langlands.GroupScheme.Reductive.SpecialLinear
import Langlands.GroupScheme.Torus.SplitReductiveProof

/-! # The rank-one central cover from a root cell -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RankOneCoverOfRootCell

open RootCell (Ga crd pt powerCell gaPower)
open SpecialLinearTensorCell

/-! ### Matrix identities -/

section Matrices

variable {A : Type*} [CommRing A]

/-- `diag(s, s⁻¹)` with `s² = 1` is the scalar matrix `s`, so it commutes with everything. -/
theorem dg_mul_comm (s : Aˣ) (hs : s ^ 2 = 1) (g : Matrix.SpecialLinearGroup (Fin 2) A) :
    dg s * g = g * dg s := by
  have hinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right (by rw [← sq, hs])
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_dg, hinv]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem cell_zero_zero (s : Aˣ) : lo (0 : A) * (dg s * up 0) = dg s := by
  ext i j
  rw [coe_cell, coe_dg]
  fin_cases i <;> fin_cases j <;> simp

end Matrices

/-! ### Points of `SL₂ × C` -/

section Points

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] {C : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A point of `SL₂ × C` whose upper left entry is a unit lies in the cell. -/
theorem exists_cell₀_of_isUnit {Z : Over (Spec (CommRingCat.of k))} (y : Z ⟶ (G₀ C).X)
    (hy : IsUnit ((ptEquiv C Z y).1 0 0)) : ∃ c : Z ⟶ RootCell.Cell (T₀ C), c ≫ cell₀ C = y := by
  obtain ⟨s, hs⟩ := hy
  obtain ⟨τ, hτ1, hτ2⟩ : ∃ τ : Z ⟶ (T₀ C).X, tc τ = s ∧ τ ≫ snd _ _ = y ≫ snd _ _ :=
    ⟨lift ((splitTorus.pointsEquiv (ULift.{u} (Fin 1)) Z).symm fun _ => s) (y ≫ snd _ _),
      by rw [tc, lift_fst, MulEquiv.apply_symm_apply], lift_snd _ _⟩
  refine ⟨lift (pt ((ptEquiv C Z y).1 1 0 * ↑s⁻¹))
    (lift τ (pt (↑s⁻¹ * (ptEquiv C Z y).1 0 1))), ?_⟩
  apply (ptEquiv C Z).injective
  rw [ptEquiv_lift_cell₀, RootCell.crd_pt, RootCell.crd_pt, hτ1, hτ2, ← eq_cell _ s hs]
  rfl

/-- Matrix entries of points of `SL₂ × C` are natural in the test scheme. -/
theorem ptEquiv_comp_apply {W Z : Over (Spec (CommRingCat.of k))} (j : W ⟶ Z)
    (x : Z ⟶ (G₀ C).X) (a b : Fin 2) :
    (ptEquiv C W (j ≫ x)).1 a b = j.left.appTop ((ptEquiv C Z x).1 a b) := by
  rw [ptEquiv_apply, ptEquiv_apply, SpecialLinear.pointsEquiv_apply_apply,
    SpecialLinear.pointsEquiv_apply_apply]
  rfl

variable (C) in
/-- The Weyl point `([[0, 1], [-1, 0]], 1)` of `SL₂ × C`. -/
def wPt (Z : Over (Spec (CommRingCat.of k))) : Z ⟶ (G₀ C).X := (ptEquiv C Z).symm (wy, 1)

theorem ptEquiv_wPt (Z : Over (Spec (CommRingCat.of k))) : ptEquiv C Z (wPt C Z) = (wy, 1) :=
  MulEquiv.apply_symm_apply _ _

theorem wPt_conj {Z : Over (Spec (CommRingCat.of k))} (a : Z ⟶ (Ga k).X) :
    wPt C Z * (a ≫ (xp₀ C).hom.hom) * (wPt C Z)⁻¹ = pt (-crd a) ≫ (xm₀ C).hom.hom := by
  apply (ptEquiv C Z).injective
  rw [map_mul, map_mul, map_inv, ptEquiv_wPt, ptEquiv_xp₀, ptEquiv_xm₀, RootCell.crd_pt]
  ext1
  · exact wy_up_wy_inv _
  · change (1 : Z ⟶ C.X) * 1 * 1⁻¹ = 1
    rw [mul_one, inv_one, mul_one]

theorem wPt_mul_apply {Z : Over (Spec (CommRingCat.of k))} (x : Z ⟶ (G₀ C).X) :
    (ptEquiv C Z (wPt C Z * x)).1 0 0 = (ptEquiv C Z x).1 1 0 := by
  rw [map_mul, Prod.fst_mul, ptEquiv_wPt]
  exact wy_mul_apply_zero_zero _

end Points

/-! ### The kernel of a power map out of `SL₂ × C` -/

section Kernel

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] {C : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} {α : characterLattice T} {αv : cocharacterLattice T} {xp xm : Ga k ⟶ G}
  {t : T₀ C ⟶ T} {φ : G₀ C ⟶ G}

include i α αv in
/-- The cell map of a root cell is a monomorphism. -/
theorem mono_cell (D : RootCell.IsRootCell i α αv xp xm) :
    Mono (Dynamic.tripleCellMultiplication xm i xp) := by
  have : IsOpenImmersion (Dynamic.tripleCellMultiplication xm i xp).left := D.isOpenImmersion
  exact Over.mono_of_mono_left _

/-- **Weyl step.** Let `x` be a point of the kernel of `φ`. Over any test scheme on which the
lower left entry of `x` is a unit, the ring of global functions is zero. -/
theorem one_eq_zero_of_isUnit (D : RootCell.IsRootCell i α αv xp xm)
    (hcell : cell₀ C ≫ φ.hom.hom =
      powerCell t 1 ≫ Dynamic.tripleCellMultiplication xm i xp)
    (hxp : (xp₀ C).hom.hom ≫ φ.hom.hom = gaPower 1 ≫ xp.hom.hom)
    (hxm : (xm₀ C).hom.hom ≫ φ.hom.hom = gaPower 1 ≫ xm.hom.hom)
    {Z : Over (Spec (CommRingCat.of k))} (x : Z ⟶ (G₀ C).X) (hx : x ≫ φ.hom.hom = 1)
    {W : Over (Spec (CommRingCat.of k))} (j : W ⟶ Z)
    (hj : IsUnit (j.left.appTop ((ptEquiv C Z x).1 1 0))) : (1 : Γ(W.left, ⊤)) = 0 := by
  have := mono_cell D
  have hy : IsUnit ((ptEquiv C W (wPt C W * (j ≫ x))).1 0 0) := by
    rw [wPt_mul_apply, ptEquiv_comp_apply]
    exact hj
  obtain ⟨c, hc⟩ := exists_cell₀_of_isUnit _ hy
  have hwφ : wPt C W ≫ φ.hom.hom =
      (c ≫ powerCell t 1) ≫ Dynamic.tripleCellMultiplication xm i xp := by
    rw [Category.assoc, ← hcell, ← Category.assoc, hc, MonObj.mul_comp, Category.assoc, hx,
      MonObj.comp_one, mul_one]
  have hconj : ((c ≫ powerCell t 1) ≫ Dynamic.tripleCellMultiplication xm i xp) *
      ((pt 1 ≫ gaPower 1) ≫ xp.hom.hom) =
      ((pt (-1) ≫ gaPower 1) ≫ xm.hom.hom) *
        ((c ≫ powerCell t 1) ≫ Dynamic.tripleCellMultiplication xm i xp) := by
    have h := wPt_conj (C := C) (Z := W) (pt 1)
    rw [mul_inv_eq_iff_eq_mul, RootCell.crd_pt] at h
    have h' := congrArg (· ≫ φ.hom.hom) h
    simp only [MonObj.mul_comp, Category.assoc, hxp, hxm] at h'
    rw [hwφ] at h'
    simpa only [Category.assoc] using h'
  set c' := c ≫ powerCell t 1
  rw [RootCell.eq_lift c', Dynamic.lift_tripleCellMultiplication] at hconj
  set m := c' ≫ fst _ _
  set τ := c' ≫ snd _ _ ≫ fst _ _
  set p := c' ≫ snd _ _ ≫ snd _ _
  set a : W ⟶ (Ga k).X := pt 1 ≫ gaPower 1
  set b : W ⟶ (Ga k).X := pt (-1) ≫ gaPower 1
  have hL : lift m (lift τ (p * a)) ≫ Dynamic.tripleCellMultiplication xm i xp =
      lift (b * m) (lift τ p) ≫ Dynamic.tripleCellMultiplication xm i xp := by
    rw [Dynamic.lift_tripleCellMultiplication, Dynamic.lift_tripleCellMultiplication,
      MonObj.mul_comp, MonObj.mul_comp]
    calc _ = (m ≫ xm.hom.hom) * ((τ ≫ i.hom.hom) * (p ≫ xp.hom.hom)) * (a ≫ xp.hom.hom) := by
          simp only [mul_assoc]
      _ = (b ≫ xm.hom.hom) * ((m ≫ xm.hom.hom) * ((τ ≫ i.hom.hom) * (p ≫ xp.hom.hom))) :=
          hconj
      _ = _ := by simp only [mul_assoc]
  have hfst := congrArg (· ≫ fst _ _) (cancel_mono _ |>.mp hL)
  simp only [lift_fst] at hfst
  have hcrd := congrArg crd hfst
  rw [RootCell.crd_mul] at hcrd
  have hb : crd b = 0 := by linear_combination -hcrd
  rw [show crd b = -1 by simp only [b, RootCell.crd_comp_gaPower, RootCell.crd_pt, pow_one]]
    at hb
  exact neg_eq_zero.mp hb

/-- The upper left entry of a point of the kernel of `φ` is a unit. -/
theorem kernel_isUnit (D : RootCell.IsRootCell i α αv xp xm)
    (hcell : cell₀ C ≫ φ.hom.hom =
      powerCell t 1 ≫ Dynamic.tripleCellMultiplication xm i xp)
    (hxp : (xp₀ C).hom.hom ≫ φ.hom.hom = gaPower 1 ≫ xp.hom.hom)
    (hxm : (xm₀ C).hom.hom ≫ φ.hom.hom = gaPower 1 ≫ xm.hom.hom)
    {Z : Over (Spec (CommRingCat.of k))} (x : Z ⟶ (G₀ C).X) (hx : x ≫ φ.hom.hom = 1) :
    IsUnit ((ptEquiv C Z x).1 0 0) := by
  have hdet : (ptEquiv C Z x).1 0 0 * (ptEquiv C Z x).1 1 1 -
      (ptEquiv C Z x).1 0 1 * (ptEquiv C Z x).1 1 0 = 1 := by
    rw [← Matrix.det_fin_two]
    exact (ptEquiv C Z x).1.2
  apply Z.left.toRingedSpace.isUnit_of_isUnit_germ ⊤ ((ptEquiv C Z x).1 0 0)
  intro z hz
  have hd := congrArg (Z.left.presheaf.germ ⊤ z hz) hdet
  rw [map_sub, map_mul, map_mul, map_one] at hd
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add
      (a := Z.left.presheaf.germ ⊤ z hz ((ptEquiv C Z x).1 0 0) *
        Z.left.presheaf.germ ⊤ z hz ((ptEquiv C Z x).1 1 1))
      (b := -(Z.left.presheaf.germ ⊤ z hz ((ptEquiv C Z x).1 0 1) *
        Z.left.presheaf.germ ⊤ z hz ((ptEquiv C Z x).1 1 0)))
      (by rw [← sub_eq_add_neg, hd]; exact isUnit_one) with h | h
  · exact isUnit_of_mul_isUnit_left h
  · exfalso
    have h' : IsUnit (Z.left.presheaf.germ ⊤ z hz ((ptEquiv C Z x).1 0 1) *
        Z.left.presheaf.germ ⊤ z hz ((ptEquiv C Z x).1 1 0)) := by
      simpa using h.neg
    have hz' : z ∈ Z.left.basicOpen ((ptEquiv C Z x).1 1 0) :=
      (Z.left.mem_basicOpen_top _ z).mpr (isUnit_of_mul_isUnit_right h')
    let U := Z.left.basicOpen ((ptEquiv C Z x).1 1 0)
    let Z₁ : Over (Spec (CommRingCat.of k)) := Over.mk (U.ι ≫ Z.hom)
    let j : Z₁ ⟶ Z := Over.homMk U.ι rfl
    have hj : IsUnit (j.left.appTop ((ptEquiv C Z x).1 1 0)) := by
      apply LocalRankOneUnitCell.isUnit_appTop_of_range_subset_basicOpen
      change Set.range U.ι ⊆ _
      rw [Scheme.Opens.range_ι]
    have h10 := one_eq_zero_of_isUnit D hcell hxp hxm x hx j hj
    have : Nontrivial Γ(Z₁.left, ⊤) :=
      (Z₁.left.presheaf.germ ⊤ (⟨z, hz'⟩ : U) trivial).hom.domain_nontrivial
    exact one_ne_zero h10

/-- A point of the kernel of `φ` is `(diag(s, s⁻¹), c)` with `s² = 1`. -/
theorem kernel_ptEquiv (D : RootCell.IsRootCell i α αv xp xm)
    (hcell : cell₀ C ≫ φ.hom.hom =
      powerCell t 1 ≫ Dynamic.tripleCellMultiplication xm i xp)
    (hxp : (xp₀ C).hom.hom ≫ φ.hom.hom = gaPower 1 ≫ xp.hom.hom)
    (hxm : (xm₀ C).hom.hom ≫ φ.hom.hom = gaPower 1 ≫ xm.hom.hom)
    (hχ : t ≫ α = χ₀ C)
    {Z : Over (Spec (CommRingCat.of k))} (x : Z ⟶ (G₀ C).X) (hx : x ≫ φ.hom.hom = 1) :
    ∃ s : Γ(Z.left, ⊤)ˣ, s ^ 2 = 1 ∧ (ptEquiv C Z x).1 = dg s := by
  have := mono_cell D
  obtain ⟨c, hc⟩ := exists_cell₀_of_isUnit x (kernel_isUnit D hcell hxp hxm x hx)
  have hφx : (c ≫ powerCell t 1) ≫ Dynamic.tripleCellMultiplication xm i xp = 1 := by
    rw [Category.assoc, ← hcell, ← Category.assoc, hc, hx]
  have hone : lift (1 : Z ⟶ (Ga k).X) (lift (1 : Z ⟶ T.X) 1) ≫
      Dynamic.tripleCellMultiplication xm i xp = 1 := by
    rw [Dynamic.lift_tripleCellMultiplication, MonObj.one_comp, MonObj.one_comp,
      MonObj.one_comp, one_mul, one_mul]
  rw [RootCell.eq_lift c, RootCell.lift_powerCell, ← hone] at hφx
  have hl := (cancel_mono _).mp hφx
  have hm := congrArg (· ≫ fst _ _) hl
  have hτ := congrArg (· ≫ snd _ _ ≫ fst _ _) hl
  have hp := congrArg (· ≫ snd _ _ ≫ snd _ _) hl
  simp only [lift_fst, lift_snd_assoc, lift_snd] at hm hτ hp
  have hm0 : crd (c ≫ fst _ _) = 0 := by
    have h := congrArg crd hm
    rwa [RootCell.crd_comp_gaPower, pow_one, RootCell.crd_one] at h
  have hp0 : crd (c ≫ snd _ _ ≫ snd _ _) = 0 := by
    have h := congrArg crd hp
    rwa [RootCell.crd_comp_gaPower, pow_one, RootCell.crd_one] at h
  have hs : tc (c ≫ snd _ _ ≫ fst _ _) ^ 2 = 1 := by
    rw [← gm_χ₀, ← hχ, comp_groupHom_comp, hτ, MonObj.one_comp, map_one]
  refine ⟨tc (c ≫ snd _ _ ≫ fst _ _), hs, ?_⟩
  rw [← hc, ptEquiv_cell₀, hm0, hp0, cell_zero_zero]

/-- The kernel of `φ` is central. -/
theorem kernel_mem_center (D : RootCell.IsRootCell i α αv xp xm)
    (hcell : cell₀ C ≫ φ.hom.hom =
      powerCell t 1 ≫ Dynamic.tripleCellMultiplication xm i xp)
    (hxp : (xp₀ C).hom.hom ≫ φ.hom.hom = gaPower 1 ≫ xp.hom.hom)
    (hxm : (xm₀ C).hom.hom ≫ φ.hom.hom = gaPower 1 ≫ xm.hom.hom)
    (hχ : t ≫ α = χ₀ C)
    {Z : Over (Spec (CommRingCat.of k))} (x : Z ⟶ (G₀ C).X) (hx : x ≫ φ.hom.hom = 1) :
    x ∈ (center (G₀ C)).carrier Z := by
  intro Z' a h
  have hx' : (a ≫ x) ≫ φ.hom.hom = 1 := by rw [Category.assoc, hx, MonObj.comp_one]
  obtain ⟨s, hs, hg⟩ := kernel_ptEquiv D hcell hxp hxm hχ (a ≫ x) hx'
  change (a ≫ x) * h = h * (a ≫ x)
  apply (ptEquiv C Z').injective
  rw [map_mul, map_mul]
  ext1
  · rw [Prod.fst_mul, Prod.fst_mul, hg]
    exact dg_mul_comm s hs _
  · rw [Prod.snd_mul, Prod.snd_mul]
    exact mul_comm _ _

end Kernel

end Langlands.GroupScheme.RankOneCoverOfRootCell

namespace Langlands.GroupScheme

open RankOneCoverOfRootCell SpecialLinearTensorCell

/-- An isogeny into a connected reductive group over a field is locally of finite
presentation, since its target is locally Noetherian. -/
theorem locallyOfFinitePresentation_of_isIsogeny {k : Type u} [Field k]
    {H G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G) {f : H ⟶ G}
    (hf : IsIsogeny f) : LocallyOfFinitePresentation f.hom.hom.left := by
  have : IsFinite f.hom.hom.left := hf.1
  have : Smooth G.X.hom := hG.smooth
  have : IsLocallyNoetherian G.X.left := LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  infer_instance

/-- **The rank-one central cover from a root cell.** Let `G` be a connected reductive group
over a field `k`, `i : T ⟶ G` a homomorphism from a split torus, and `xp`, `xm` root groups
forming a root cell (`RootCell.IsRootCell`) for a character `α` and a cocharacter `αv` with
`⟨α, αv⟩ = 2`. Then there are a split torus `C`, a central isogeny `SL₂ × C ⟶ G` and an
isogeny `𝔾ₘ × C ⟶ T` compatible with `diagonalTorus 1 × id` and `i`. -/
theorem rankOneCentralCover_of_rootCell {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (hT : IsSplitTorus T.toGrp)
    {i : T.toGrp ⟶ G} {α : characterLattice T} {αv : cocharacterLattice T}
    {xp xm : RootCell.Ga k ⟶ G} (D : RootCell.IsRootCell i α αv xp xm)
    (h2 : latticePairing T α αv = 2) :
    ∃ (C : CommGroupScheme (Spec (CommRingCat.of k))), IsSplitTorus C.toGrp ∧
      ∃ (f : SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k) ⊗ C.toGrp ⟶ G)
        (t : CommGroupScheme.prod
          (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift (Fin 1))) C ⟶ T),
        IsCentralIsogeny f ∧ IsIsogeny (CommGroupScheme.groupHom t) ∧
        (SpecialLinear.FinSucc.diagonalTorus 1 (CommRingCat.of k) ⊗ₘ 𝟙 C.toGrp) ≫ f =
          CommGroupScheme.groupHom t ≫ i := by
  obtain ⟨C, hC, t, ht, hχ, hχv⟩ := RankOneCoverTorus.exists_torusIsogeny hT α αv h2
  have hG₀ : IsConnectedReductive (G₀ C) :=
    DirectProduct.isConnectedReductive_tensor (SpecialLinear.isConnectedReductive k (Fin 2) 0)
      hC.isConnectedReductive
  obtain ⟨φ, hφ, hi, hxm, hxp, hcell⟩ := RootCell.exists_powerIsogeny hG₀ hG
    (isRootCell₀ (C := C)) D t ht (ringExpChar k) 0
    (by rw [pow_zero, one_smul]; exact hχ) (by rw [pow_zero, one_smul]; exact hχv)
  rw [pow_zero] at hxm hxp hcell
  refine ⟨C, hC, φ, t, ⟨hφ, ?_, ?_⟩, ht, hi⟩
  · exact locallyOfFinitePresentation_of_isIsogeny hG hφ
  · exact (isCentral_kernelι_iff φ).mpr fun Z x hx => kernel_mem_center D hcell hxp hxm hχ x hx

end Langlands.GroupScheme
