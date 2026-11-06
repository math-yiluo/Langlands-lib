import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Langlands.GroupScheme.Reductive.SplitRankOneRootCellReduction

/-! # The cell criterion and the rank-one relation from algebraically closed points -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RootCell

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The rank-one relation `xp(X) xm(Y) = xm(Y') χv(u) xp(X')` over `Z`, in the form of
`SplitRankOneRootCellStatement`. -/
def RelationAt (i : T.toGrp ⟶ G) (χv : cocharacterLattice T) (xp xm : Ga k ⟶ G)
    (Z : Over (Spec (CommRingCat.of k))) (a b a' b' : Z ⟶ (Ga k).X) (u : Γ(Z.left, ⊤)ˣ) :
    Prop :=
  (a ≫ xp.hom.hom) * (b ≫ xm.hom.hom) =
    (b' ≫ xm.hom.hom) *
      ((Gm.pointsEquiv _ Z).symm u ≫ (CommGroupScheme.groupHom χv).hom.hom ≫ i.hom.hom) *
        (a' ≫ xp.hom.hom)

/-- Clause 5 of `SplitRankOneRootCellStatement` over the test scheme `Z`: the relation
holds for all points `X, Y` with `u = 1 + XY` a unit, `X' = u⁻¹ X` and `Y' = u⁻¹ Y`. -/
def RelationOver (i : T.toGrp ⟶ G) (χv : cocharacterLattice T) (xp xm : Ga k ⟶ G)
    (Z : Over (Spec (CommRingCat.of k))) : Prop :=
  ∀ (a b a' b' : Z ⟶ (Ga k).X) (u : Γ(Z.left, ⊤)ˣ),
    (u : Γ(Z.left, ⊤)) = 1 + crd a * crd b → crd a' = ↑u⁻¹ * crd a →
      crd b' = ↑u⁻¹ * crd b → RelationAt i χv xp xm Z a b a' b' u

/-- The product `xp(X) xm(Y)` lies in the image of the cell multiplication. -/
def InCell (i : T.toGrp ⟶ G) (xp xm : Ga k ⟶ G) {Z : Over (Spec (CommRingCat.of k))}
    (a b : Z ⟶ (Ga k).X) : Prop :=
  ∃ c, c ≫ Dynamic.tripleCellMultiplication xm i xp = (a ≫ xp.hom.hom) * (b ≫ xm.hom.hom)

theorem crd_injective {Z : Over (Spec (CommRingCat.of k))} {a a' : Z ⟶ (Ga k).X}
    (h : crd a = crd a') : a = a' :=
  VectorGroup.points_ext fun j => by rw [Fin.fin_one_eq_zero j]; exact h

theorem crd_comp {Z Z' : Over (Spec (CommRingCat.of k))} (w : Z' ⟶ Z) (a : Z ⟶ (Ga k).X) :
    crd (w ≫ a) = w.left.appTop (crd a) :=
  congrFun (VectorGroup.coordinates_comp w a) 0

theorem coe_units_map {Z Z' : Over (Spec (CommRingCat.of k))} (w : Z' ⟶ Z)
    (u : Γ(Z.left, ⊤)ˣ) :
    ((Units.map w.left.appTop.hom.toMonoidHom u : Γ(Z'.left, ⊤)ˣ) : Γ(Z'.left, ⊤)) =
      w.left.appTop (u : Γ(Z.left, ⊤)) :=
  rfl

theorem coe_units_map_inv {Z Z' : Over (Spec (CommRingCat.of k))} (w : Z' ⟶ Z)
    (u : Γ(Z.left, ⊤)ˣ) :
    (↑(Units.map w.left.appTop.hom.toMonoidHom u)⁻¹ : Γ(Z'.left, ⊤)) =
      w.left.appTop (↑u⁻¹ : Γ(Z.left, ⊤)) :=
  rfl

theorem symm_pointsEquiv_comp {Z Z' : Over (Spec (CommRingCat.of k))} (w : Z' ⟶ Z)
    (u : Γ(Z.left, ⊤)ˣ) :
    (Gm.pointsEquiv _ Z').symm (Units.map w.left.appTop.hom.toMonoidHom u) =
      w ≫ (Gm.pointsEquiv _ Z).symm u := by
  rw [MulEquiv.symm_apply_eq, Gm.pointsEquiv_naturality, MulEquiv.apply_symm_apply]

variable {i : T.toGrp ⟶ G} {χv : cocharacterLattice T} {xp xm : Ga k ⟶ G}

/-- The relation for pulled-back points is the pullback of the two sides of the relation. -/
theorem relationAt_comp_iff {Z Z' : Over (Spec (CommRingCat.of k))} (w : Z' ⟶ Z)
    (a b a' b' : Z ⟶ (Ga k).X) (u : Γ(Z.left, ⊤)ˣ) :
    RelationAt i χv xp xm Z' (w ≫ a) (w ≫ b) (w ≫ a') (w ≫ b')
        (Units.map w.left.appTop.hom.toMonoidHom u) ↔
      w ≫ ((a ≫ xp.hom.hom) * (b ≫ xm.hom.hom)) =
        w ≫ ((b' ≫ xm.hom.hom) *
          ((Gm.pointsEquiv _ Z).symm u ≫ (CommGroupScheme.groupHom χv).hom.hom ≫ i.hom.hom) *
            (a' ≫ xp.hom.hom)) := by
  rw [RelationAt, symm_pointsEquiv_comp]
  simp only [MonObj.comp_mul, Category.assoc]

theorem RelationAt.comp {Z Z' : Over (Spec (CommRingCat.of k))} (w : Z' ⟶ Z)
    {a b a' b' : Z ⟶ (Ga k).X} {u : Γ(Z.left, ⊤)ˣ} (h : RelationAt i χv xp xm Z a b a' b' u) :
    RelationAt i χv xp xm Z' (w ≫ a) (w ≫ b) (w ≫ a') (w ≫ b')
      (Units.map w.left.appTop.hom.toMonoidHom u) :=
  (relationAt_comp_iff w a b a' b' u).2 (by rw [show _ = _ from h])

theorem InCell.comp {Z Z' : Over (Spec (CommRingCat.of k))} (w : Z' ⟶ Z)
    {a b : Z ⟶ (Ga k).X} (h : InCell i xp xm a b) : InCell i xp xm (w ≫ a) (w ≫ b) := by
  obtain ⟨c, hc⟩ := h
  exact ⟨w ≫ c, by rw [Category.assoc, hc, MonObj.comp_mul, Category.assoc, Category.assoc]⟩

/-- An instance of the relation for pulled-back points, from the relation over the source. -/
theorem RelationOver.apply_comp {Z Z' : Over (Spec (CommRingCat.of k))}
    (h : RelationOver i χv xp xm Z') (w : Z' ⟶ Z) {a b a' b' : Z ⟶ (Ga k).X}
    {u : Γ(Z.left, ⊤)ˣ} (hu : (u : Γ(Z.left, ⊤)) = 1 + crd a * crd b)
    (ha : crd a' = ↑u⁻¹ * crd a) (hb : crd b' = ↑u⁻¹ * crd b) :
    RelationAt i χv xp xm Z' (w ≫ a) (w ≫ b) (w ≫ a') (w ≫ b')
      (Units.map w.left.appTop.hom.toMonoidHom u) :=
  h _ _ _ _ _ (by rw [coe_units_map, hu, crd_comp, crd_comp, map_add, map_mul, map_one])
    (by rw [coe_units_map_inv, crd_comp, crd_comp, ha, map_mul])
    (by rw [coe_units_map_inv, crd_comp, crd_comp, hb, map_mul])

/-- The relation descends along a dominant morphism to a reduced scheme. -/
theorem RelationAt.of_comp [IsSeparated G.X.hom] {Z Z' : Over (Spec (CommRingCat.of k))}
    [IsReduced Z.left] (w : Z' ⟶ Z) [IsDominant w.left] {a b a' b' : Z ⟶ (Ga k).X}
    {u : Γ(Z.left, ⊤)ˣ}
    (h : RelationAt i χv xp xm Z' (w ≫ a) (w ≫ b) (w ≫ a') (w ≫ b')
      (Units.map w.left.appTop.hom.toMonoidHom u)) :
    RelationAt i χv xp xm Z a b a' b' u := by
  rw [relationAt_comp_iff] at h
  have h' := congrArg Over.Hom.left h
  rw [Over.comp_left, Over.comp_left] at h'
  exact Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated G.X.hom
    (by rw [Over.w, Over.w]) w.left h')

/-! ### Algebraically closed points -/

/-- The morphism to `X` from the spectrum of an algebraic closure of the residue field at
the point `x`. -/
abbrev algClosedPt (X : Scheme.{u}) (x : X) :
    Spec (CommRingCat.of (AlgebraicClosure (X.residueField x))) ⟶ X :=
  geometricPoint X x

@[simp]
theorem algClosedPt_apply (X : Scheme.{u}) (x : X)
    (s : Spec (CommRingCat.of (AlgebraicClosure (X.residueField x)))) :
    algClosedPt X x s = x := by
  rw [algClosedPt, geometricPoint, Scheme.Hom.comp_apply]
  exact X.fromSpecResidueField_apply x _

theorem algClosedPt_preimage_eq_bot {X : Scheme.{u}} {x : X} {U : X.Opens} (hx : x ∉ U) :
    algClosedPt X x ⁻¹ᵁ U = ⊥ :=
  eq_bot_iff.2 fun s hs => (hx (by simpa using hs)).elim

/-- The algebraically closed point over the generic point is dominant. -/
instance {X : Scheme.{u}} [IrreducibleSpace X] : IsDominant (algClosedPt X (genericPoint X)) :=
  ⟨Dense.mono (Set.singleton_subset_iff.2 ⟨IsLocalRing.closedPoint _, algClosedPt_apply _ _ _⟩)
    (dense_iff_closure_eq.2 (genericPoint_closure X))⟩

/-! ### The universal point -/

namespace Universal

variable (k)

/-- The plane `𝔾ₐ²`, carrying the universal pair of coordinates. -/
abbrev plane : Over (Spec (CommRingCat.of k)) := (VectorGroup.groupScheme (CommRingCat.of k) 2).X

instance : IsIntegral (plane k).left :=
  inferInstanceAs (IsIntegral (Spec (CommRingCat.of (MvPolynomial (Fin 2) k))))

/-- The coordinate `X` on the plane. -/
abbrev cX : Γ((plane k).left, ⊤) := VectorGroup.coordinateSection (CommRingCat.of k) 2 0

/-- The coordinate `Y` on the plane. -/
abbrev cY : Γ((plane k).left, ⊤) := VectorGroup.coordinateSection (CommRingCat.of k) 2 1

theorem one_add_ne_zero : 1 + cX k * cY k ≠ 0 := by
  have e : 1 + cX k * cY k =
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin 2) (CommRingCat.of k)))).inv
        (1 + MvPolynomial.X 0 * MvPolynomial.X 1) := by
    simp only [cX, cY, VectorGroup.coordinateSection, map_add, map_mul, map_one]
    rfl
  rw [e]
  intro h
  have h' := congrArg
    (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin 2) (CommRingCat.of k)))).hom h
  rw [Iso.inv_hom_id_apply] at h'
  have h'' : (1 + MvPolynomial.X 0 * MvPolynomial.X 1 :
      MvPolynomial (Fin 2) (CommRingCat.of k)) = 0 := h'.trans (map_zero _)
  have := congrArg MvPolynomial.constantCoeff h''
  simp at this

/-- The open subscheme `1 + XY ≠ 0` of the plane. -/
def openU : (plane k).left.Opens := (plane k).left.basicOpen (1 + cX k * cY k)

theorem nonempty_openU : Nonempty (openU k) := by
  have h : openU k ≠ ⊥ := by
    rw [Ne, openU, basicOpen_eq_bot_iff]
    exact one_add_ne_zero k
  obtain ⟨x, hx⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 h
  exact ⟨⟨x, hx⟩⟩

/-- The open subscheme `1 + XY ≠ 0` as a scheme over `k`. -/
def overU : Over (Spec (CommRingCat.of k)) := Over.mk ((openU k).ι ≫ (plane k).hom)

instance : IsIntegral (overU k).left :=
  haveI : Nonempty (openU k).toScheme := nonempty_openU k
  isIntegral_of_isOpenImmersion (X := (openU k).toScheme) (openU k).ι

/-- The coordinate `X` on `1 + XY ≠ 0`. -/
def univX : Γ((overU k).left, ⊤) := (openU k).ι.appTop (cX k)

/-- The coordinate `Y` on `1 + XY ≠ 0`. -/
def univY : Γ((overU k).left, ⊤) := (openU k).ι.appTop (cY k)

theorem isUnit_univ : IsUnit (1 + univX k * univY k) := by
  have e : 1 + univX k * univY k = (openU k).ι.appTop (1 + cX k * cY k) := by
    rw [map_add, map_mul, map_one]
    rfl
  rw [e]
  apply isUnit_of_basicOpen_eq_top
  rw [← Scheme.preimage_basicOpen_top]
  exact (openU k).ι_preimage_self

/-- The unit `1 + XY` on `1 + XY ≠ 0`. -/
def univUnit : Γ((overU k).left, ⊤)ˣ := (isUnit_univ k).unit

end Universal

open Universal

/-- The relation at the universal point, from the relation at algebraically closed points:
pull back to the algebraically closed point over the generic point, which is dominant. -/
theorem relationAt_univ [IsSeparated G.X.hom]
    (hK : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (f : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)),
      RelationOver i χv xp xm (Over.mk f)) :
    RelationAt i χv xp xm (overU k) (pt (univX k)) (pt (univY k))
      (pt (↑(univUnit k)⁻¹ * univX k)) (pt (↑(univUnit k)⁻¹ * univY k)) (univUnit k) := by
  let g := algClosedPt (overU k).left (genericPoint (overU k).left)
  let w : Over.mk (g ≫ (overU k).hom) ⟶ overU k := Over.homMk g
  have : IsDominant w.left := inferInstanceAs (IsDominant g)
  have hu : ((univUnit k : Γ((overU k).left, ⊤)ˣ) : Γ((overU k).left, ⊤)) =
      1 + crd (pt (univX k)) * crd (pt (univY k)) := by
    rw [crd_pt, crd_pt, univUnit, IsUnit.unit_spec]
  have ha : crd (pt ((↑(univUnit k)⁻¹ : Γ((overU k).left, ⊤)) * univX k)) =
      (↑(univUnit k)⁻¹ : Γ((overU k).left, ⊤)) * crd (pt (univX k)) := by
    rw [crd_pt, crd_pt]
  have hb : crd (pt ((↑(univUnit k)⁻¹ : Γ((overU k).left, ⊤)) * univY k)) =
      (↑(univUnit k)⁻¹ : Γ((overU k).left, ⊤)) * crd (pt (univY k)) := by
    rw [crd_pt, crd_pt]
  exact RelationAt.of_comp w ((hK _ (g ≫ (overU k).hom)).apply_comp w hu ha hb)

/-- **The rank-one relation from algebraically closed points.** If clause 5 of
`SplitRankOneRootCellStatement` holds over `Spec K` for every algebraically closed field `K`
over `k`, then it holds over every test scheme. -/
theorem relationOver_of_isAlgClosed [IsSeparated G.X.hom]
    (hK : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (f : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)),
      RelationOver i χv xp xm (Over.mk f))
    (Z : Over (Spec (CommRingCat.of k))) : RelationOver i χv xp xm Z := by
  intro a b a' b' u hu ha hb
  -- The classifying point `(X, Y)` of the plane lands in `1 + XY ≠ 0`.
  let v : Z ⟶ plane k := (VectorGroup.coordinates (CommRingCat.of k) 2 Z).symm
    (Multiplicative.ofAdd ![crd a, crd b])
  have hvX : v.left.appTop (cX k) = crd a := by
    rw [cX, ← VectorGroup.coordinates_apply, MulEquiv.apply_symm_apply, toAdd_ofAdd]
    rfl
  have hvY : v.left.appTop (cY k) = crd b := by
    rw [cY, ← VectorGroup.coordinates_apply, MulEquiv.apply_symm_apply, toAdd_ofAdd]
    rfl
  have hrange : Set.range v.left ⊆ Set.range (openU k).ι := by
    have hpre : v.left ⁻¹ᵁ openU k = ⊤ := by
      rw [openU, Scheme.preimage_basicOpen_top, map_add, map_mul, map_one, hvX, hvY, ← hu]
      exact Z.left.basicOpen_of_isUnit u.isUnit
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ v.left ⁻¹ᵁ openU k := by
      rw [hpre]
      trivial
    exact hx
  let φ₀ : Z.left ⟶ (openU k).toScheme := IsOpenImmersion.lift (openU k).ι v.left hrange
  have hφ : φ₀ ≫ (openU k).ι = v.left := IsOpenImmersion.lift_fac _ _ _
  let φ : Z ⟶ overU k := Over.homMk φ₀ (by
    change (φ₀ ≫ (openU k).ι) ≫ (plane k).hom = Z.hom
    rw [hφ, Over.w])
  have hφX : φ.left.appTop (univX k) = crd a := by
    change φ₀.appTop ((openU k).ι.appTop (cX k)) = crd a
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hφ, hvX]
  have hφY : φ.left.appTop (univY k) = crd b := by
    change φ₀.appTop ((openU k).ι.appTop (cY k)) = crd b
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hφ, hvY]
  have hφu : Units.map φ.left.appTop.hom.toMonoidHom (univUnit k) = u := by
    ext
    rw [coe_units_map, univUnit, IsUnit.unit_spec, map_add, map_mul, map_one, hφX, hφY, hu]
  have hφu' : φ.left.appTop (↑(univUnit k)⁻¹ : Γ((overU k).left, ⊤)) = ↑u⁻¹ := by
    rw [← coe_units_map_inv, hφu]
  have e₁ : a = φ ≫ pt (univX k) := crd_injective (by rw [crd_comp, crd_pt, hφX])
  have e₂ : b = φ ≫ pt (univY k) := crd_injective (by rw [crd_comp, crd_pt, hφY])
  have e₃ : a' = φ ≫ pt (↑(univUnit k)⁻¹ * univX k) :=
    crd_injective (by rw [crd_comp, crd_pt, map_mul, hφX, hφu', ha])
  have e₄ : b' = φ ≫ pt (↑(univUnit k)⁻¹ * univY k) :=
    crd_injective (by rw [crd_comp, crd_pt, map_mul, hφY, hφu', hb])
  rw [e₁, e₂, e₃, e₄, ← hφu]
  exact (relationAt_univ hK).comp φ

/-- If the relation holds whenever `1 + XY` is a unit, then `xp(X) xm(Y)` lies in the open
cell whenever `1 + XY` is a unit. -/
theorem inCell_of_relationOver {Z : Over (Spec (CommRingCat.of k))}
    (h : RelationOver i χv xp xm Z) (a b : Z ⟶ (Ga k).X) (hu : IsUnit (1 + crd a * crd b)) :
    InCell i xp xm a b := by
  refine ⟨lift (pt (↑hu.unit⁻¹ * crd b)) (lift (coU χv hu.unit) (pt (↑hu.unit⁻¹ * crd a))), ?_⟩
  rw [Dynamic.lift_tripleCellMultiplication, h a b _ _ hu.unit hu.unit_spec (crd_pt _)
    (crd_pt _), coU, mul_assoc]
  simp only [Category.assoc]

/-- **Units from cell membership, via algebraically closed points.** If over every
algebraically closed field `K` over `k` the product `xp(X) xm(Y)` is outside the open cell
when `1 + XY = 0`, then over every test scheme membership in the cell forces `1 + XY` to be
a unit. A non-unit vanishes at some point `x`, and one pulls back to the algebraic closure of
the residue field at `x`. -/
theorem isUnit_of_inCell
    (hK : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (f : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
      (a b : Over.mk f ⟶ (Ga k).X), 1 + crd a * crd b = 0 → ¬ InCell i xp xm a b)
    {Z : Over (Spec (CommRingCat.of k))} (a b : Z ⟶ (Ga k).X) (h : InCell i xp xm a b) :
    IsUnit (1 + crd a * crd b) := by
  by_contra hu
  obtain ⟨x, hx⟩ : ∃ x, x ∉ Z.left.basicOpen (1 + crd a * crd b) := by
    by_contra! H
    exact hu (isUnit_of_basicOpen_eq_top (eq_top_iff.2 fun x _ => H x))
  let g := algClosedPt Z.left x
  let w : Over.mk (g ≫ Z.hom) ⟶ Z := Over.homMk g
  refine hK _ (g ≫ Z.hom) (w ≫ a) (w ≫ b) ?_ (h.comp w)
  have h0 : w.left.appTop (1 + crd a * crd b) = 0 := by
    have : IsReduced (Over.mk (g ≫ Z.hom)).left :=
      inferInstanceAs (IsReduced (Spec (CommRingCat.of (AlgebraicClosure (Z.left.residueField x)))))
    rw [← basicOpen_eq_bot_iff, ← Scheme.preimage_basicOpen_top]
    exact algClosedPt_preimage_eq_bot hx
  rw [crd_comp, crd_comp]
  simpa only [map_add, map_mul, map_one] using h0

/-- **Clauses 4 and 5 of `SplitRankOneRootCellStatement` from algebraically closed points.**
Given the rank-one relation over every algebraically closed field over `k`, and that
`xp(X) xm(Y)` is outside the open cell over such fields when `1 + XY = 0`, the cell
criterion and the relation hold over every test scheme. -/
theorem inCell_iff_and_relationOver [IsSeparated G.X.hom]
    (hrel : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (f : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)),
      RelationOver i χv xp xm (Over.mk f))
    (hcell : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (f : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
      (a b : Over.mk f ⟶ (Ga k).X), 1 + crd a * crd b = 0 → ¬ InCell i xp xm a b) :
    (∀ (Z : Over (Spec (CommRingCat.of k))) (a b : Z ⟶ (Ga k).X),
      InCell i xp xm a b ↔ IsUnit (1 + crd a * crd b)) ∧
    ∀ Z : Over (Spec (CommRingCat.of k)), RelationOver i χv xp xm Z :=
  ⟨fun Z a b => ⟨isUnit_of_inCell hcell a b,
      inCell_of_relationOver (relationOver_of_isAlgClosed hrel Z) a b⟩,
    relationOver_of_isAlgClosed hrel⟩

end Langlands.GroupScheme.RootCell
