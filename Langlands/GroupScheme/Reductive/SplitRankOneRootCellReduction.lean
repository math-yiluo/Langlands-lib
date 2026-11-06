import Langlands.GroupScheme.OpenCellGluing
import Langlands.GroupScheme.Reductive.SplitRankOneRootCellStatement
import Langlands.GroupScheme.Reductive.SplitRankZeroIsomorphism
import Langlands.GroupScheme.SmoothConnectedGeometryProof

/-! # The rank-one isomorphism theorem from root groups and the open cell -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RootCell

variable {k : Type u} [Field k]

/-- The additive group `𝔾ₐ` over `k`. -/
abbrev Ga (k : Type u) [Field k] : GroupScheme (Spec (CommRingCat.of k)) :=
  VectorGroup.groupScheme (CommRingCat.of k) 1

/-- The coordinate of a point of `𝔾ₐ`. -/
abbrev crd {Z : Over (Spec (CommRingCat.of k))} (a : Z ⟶ (Ga k).X) : Γ(Z.left, ⊤) :=
  (VectorGroup.coordinates (CommRingCat.of k) 1 Z a).toAdd 0

/-- The point of `𝔾ₐ` with a given coordinate. -/
def pt {Z : Over (Spec (CommRingCat.of k))} (a : Γ(Z.left, ⊤)) : Z ⟶ (Ga k).X :=
  (VectorGroup.coordinates (CommRingCat.of k) 1 Z).symm (Multiplicative.ofAdd fun _ => a)

@[simp]
theorem crd_pt {Z : Over (Spec (CommRingCat.of k))} (a : Γ(Z.left, ⊤)) : crd (pt a) = a := by
  rw [crd, pt, MulEquiv.apply_symm_apply, toAdd_ofAdd]

variable {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The source `𝔾ₐ × T × 𝔾ₐ` of the open cell. -/
abbrev Cell (T : CommGroupScheme (Spec (CommRingCat.of k))) : Over (Spec (CommRingCat.of k)) :=
  (Ga k).X ⊗ (T.X ⊗ (Ga k).X)

theorem eq_lift {Z : Over (Spec (CommRingCat.of k))} (c : Z ⟶ Cell T) :
    c = lift (c ≫ fst _ _) (lift (c ≫ snd _ _ ≫ fst _ _) (c ≫ snd _ _ ≫ snd _ _)) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [lift_fst]
  · apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_snd, lift_fst]
    · rw [Category.assoc, lift_snd, lift_snd]

/-- The point of `T` given by the cocharacter `χv` at a unit. -/
def coU (χv : cocharacterLattice T) {Z : Over (Spec (CommRingCat.of k))} (u : Γ(Z.left, ⊤)ˣ) :
    Z ⟶ T.X :=
  (Gm.pointsEquiv _ Z).symm u ≫ (CommGroupScheme.groupHom χv).hom.hom

/-- The cell coordinates of the product of the cell points `(m, t, p)` and `(m', t', p')`,
given the unit `u = 1 + p m'`. They depend only on the character `χ` and the cocharacter
`χv`, not on the group. -/
def cellProd (χ : characterLattice T) (χv : cocharacterLattice T)
    {Z : Over (Spec (CommRingCat.of k))} (m p m' p' : Z ⟶ (Ga k).X) (t t' : Z ⟶ T.X)
    (u : Γ(Z.left, ⊤)ˣ) : Z ⟶ Cell T :=
  lift (m * VectorGroup.weightPointAction (-χ) Z t (pt (↑u⁻¹ * crd m')))
    (lift (t * coU χv u * t')
      (VectorGroup.weightPointAction χ Z t'⁻¹ (pt (↑u⁻¹ * crd p)) * p'))

variable {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Root groups `xp`, `xm` for the weights `χ`, `-χ` of `T` in `G` whose open cell satisfies
the rank-one relation with the cocharacter `χv`: the conclusion of
`SplitRankOneRootCellStatement` for the root `χ` with coroot `χv`. -/
structure IsRootCell (i : T.toGrp ⟶ G) (χ : characterLattice T) (χv : cocharacterLattice T)
    (xp xm : Ga k ⟶ G) : Prop where
  conj_xp : ∀ (Z : Over (Spec (CommRingCat.of k))) (t : Z ⟶ T.X) (a : Z ⟶ (Ga k).X),
    (t ≫ i.hom.hom) * (a ≫ xp.hom.hom) * (t ≫ i.hom.hom)⁻¹ =
      VectorGroup.weightPointAction χ Z t a ≫ xp.hom.hom
  conj_xm : ∀ (Z : Over (Spec (CommRingCat.of k))) (t : Z ⟶ T.X) (b : Z ⟶ (Ga k).X),
    (t ≫ i.hom.hom) * (b ≫ xm.hom.hom) * (t ≫ i.hom.hom)⁻¹ =
      VectorGroup.weightPointAction (-χ) Z t b ≫ xm.hom.hom
  isOpenImmersion : IsOpenImmersion (Dynamic.tripleCellMultiplication xm i xp).left
  exists_iff : ∀ (Z : Over (Spec (CommRingCat.of k))) (a b : Z ⟶ (Ga k).X),
    (∃ c, c ≫ Dynamic.tripleCellMultiplication xm i xp = (a ≫ xp.hom.hom) * (b ≫ xm.hom.hom)) ↔
      IsUnit (1 + crd a * crd b)
  mul_eq : ∀ (Z : Over (Spec (CommRingCat.of k))) (a b a' b' : Z ⟶ (Ga k).X)
    (u : (Γ(Z.left, ⊤))ˣ), (u : Γ(Z.left, ⊤)) = 1 + crd a * crd b →
    crd a' = ↑u⁻¹ * crd a → crd b' = ↑u⁻¹ * crd b →
    (a ≫ xp.hom.hom) * (b ≫ xm.hom.hom) =
      (b' ≫ xm.hom.hom) *
        ((Gm.pointsEquiv _ Z).symm u ≫ (CommGroupScheme.groupHom χv).hom.hom ≫ i.hom.hom) *
          (a' ≫ xp.hom.hom)

variable {i : T.toGrp ⟶ G} {χ : characterLattice T} {χv : cocharacterLattice T}
  {xp xm : Ga k ⟶ G}

namespace IsRootCell

variable (D : IsRootCell i χ χv xp xm)
include D

/-- If the product of two cell points lies in the cell, then `1 + p m'` is a unit, where `p`
is the upper coordinate of the first point and `m'` the lower coordinate of the second. -/
theorem isUnit_of_mul_eq {Z : Over (Spec (CommRingCat.of k))} (m p m' p' : Z ⟶ (Ga k).X)
    (t t' : Z ⟶ T.X) (c : Z ⟶ Cell T)
    (h : (lift m (lift t p) ≫ Dynamic.tripleCellMultiplication xm i xp) *
        (lift m' (lift t' p') ≫ Dynamic.tripleCellMultiplication xm i xp) =
      c ≫ Dynamic.tripleCellMultiplication xm i xp) :
    IsUnit (1 + crd p * crd m') := by
  refine (D.exists_iff Z p m').mp
    ⟨lift (VectorGroup.weightPointAction (-χ) Z t⁻¹ (m⁻¹ * (c ≫ fst _ _)))
      (lift (t⁻¹ * (c ≫ snd _ _ ≫ fst _ _) * t'⁻¹)
        (VectorGroup.weightPointAction χ Z t' ((c ≫ snd _ _ ≫ snd _ _) * p'⁻¹))), ?_⟩
  rw [eq_lift c] at h
  simp only [Dynamic.lift_tripleCellMultiplication] at h ⊢
  rw [← D.conj_xm, ← D.conj_xp]
  have h' : (p ≫ xp.hom.hom) * (m' ≫ xm.hom.hom) =
      (t ≫ i.hom.hom)⁻¹ * (m ≫ xm.hom.hom)⁻¹ *
        (((c ≫ fst _ _) ≫ xm.hom.hom) * (((c ≫ snd _ _ ≫ fst _ _) ≫ i.hom.hom) *
          ((c ≫ snd _ _ ≫ snd _ _) ≫ xp.hom.hom))) * (p' ≫ xp.hom.hom)⁻¹ *
        (t' ≫ i.hom.hom)⁻¹ := by
    rw [← h]
    group
  rw [h']
  simp only [MonObj.mul_comp, GrpObj.inv_comp]
  group

/-- The product of two cell points, when `1 + p m'` is the unit `u`. -/
theorem mul_eq_cellProd {Z : Over (Spec (CommRingCat.of k))} (m p m' p' : Z ⟶ (Ga k).X)
    (t t' : Z ⟶ T.X) (u : Γ(Z.left, ⊤)ˣ) (hu : (u : Γ(Z.left, ⊤)) = 1 + crd p * crd m') :
    (lift m (lift t p) ≫ Dynamic.tripleCellMultiplication xm i xp) *
        (lift m' (lift t' p') ≫ Dynamic.tripleCellMultiplication xm i xp) =
      cellProd χ χv m p m' p' t t' u ≫ Dynamic.tripleCellMultiplication xm i xp := by
  have key := D.mul_eq Z p m' (pt (↑u⁻¹ * crd p)) (pt (↑u⁻¹ * crd m')) u hu (crd_pt _)
    (crd_pt _)
  simp only [cellProd, Dynamic.lift_tripleCellMultiplication, MonObj.mul_comp]
  rw [← D.conj_xm, ← D.conj_xp]
  have e₁ : (m ≫ xm.hom.hom) * ((t ≫ i.hom.hom) * (p ≫ xp.hom.hom)) *
      ((m' ≫ xm.hom.hom) * ((t' ≫ i.hom.hom) * (p' ≫ xp.hom.hom))) =
      (m ≫ xm.hom.hom) * (t ≫ i.hom.hom) * ((p ≫ xp.hom.hom) * (m' ≫ xm.hom.hom)) *
        (t' ≫ i.hom.hom) * (p' ≫ xp.hom.hom) := by
    group
  rw [e₁, key]
  simp only [coU, GrpObj.inv_comp, Category.assoc]
  group

end IsRootCell

/-- The identity point of the open cell. -/
def unitPt (T : CommGroupScheme (Spec (CommRingCat.of k))) :
    𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ Cell T :=
  lift 1 (lift 1 1)

theorem unitPt_comp : unitPt T ≫ Dynamic.tripleCellMultiplication xm i xp = 1 := by
  rw [unitPt, Dynamic.lift_tripleCellMultiplication, MonObj.one_comp xm.hom.hom,
    MonObj.one_comp i.hom.hom, MonObj.one_comp xp.hom.hom, one_mul, one_mul]

/-- The torus inside the open cell. -/
def torusPt (T : CommGroupScheme (Spec (CommRingCat.of k))) : T.X ⟶ Cell T :=
  lift 1 (lift (𝟙 T.X) 1)

theorem torusPt_comp : torusPt T ≫ Dynamic.tripleCellMultiplication xm i xp = i.hom.hom := by
  rw [torusPt, Dynamic.lift_tripleCellMultiplication, MonObj.one_comp xm.hom.hom,
    Category.id_comp, MonObj.one_comp xp.hom.hom, one_mul, mul_one]

variable {G₁ G₂ : GroupScheme (Spec (CommRingCat.of k))} {i₁ : T.toGrp ⟶ G₁}
  {i₂ : T.toGrp ⟶ G₂} {xp₁ xm₁ : Ga k ⟶ G₁} {xp₂ xm₂ : Ga k ⟶ G₂}

/-- A relation between cell points holding in `G₁` holds in `G₂`. -/
theorem cellCompatible (D₁ : IsRootCell i₁ χ χv xp₁ xm₁) (D₂ : IsRootCell i₂ χ χv xp₂ xm₂) :
    haveI := D₁.isOpenImmersion
    CellGluing.CellCompatible (Dynamic.tripleCellMultiplication xm₁ i₁ xp₁)
      (Dynamic.tripleCellMultiplication xm₂ i₂ xp₂) := by
  have := D₁.isOpenImmersion
  intro Z x y c h
  obtain ⟨m, t, p, rfl⟩ : ∃ m t p, x = lift m (lift t p) := ⟨_, _, _, eq_lift x⟩
  obtain ⟨m', t', p', rfl⟩ : ∃ m t p, y = lift m (lift t p) := ⟨_, _, _, eq_lift y⟩
  obtain ⟨u, hu⟩ := D₁.isUnit_of_mul_eq m p m' p' t t' c h
  rw [D₁.mul_eq_cellProd m p m' p' t t' u hu] at h
  have hc : c = cellProd χ χv m p m' p' t t' u := (cancel_mono _).mp h.symm
  rw [hc, D₂.mul_eq_cellProd m p m' p' t t' u hu]

/-- **Gluing along the open cells.** Two connected reductive groups with root cells for the
same character and cocharacter of a common torus are isomorphic compatibly with the torus. -/
theorem exists_iso (hG₁ : IsConnectedReductive G₁) (hG₂ : IsConnectedReductive G₂)
    (D₁ : IsRootCell i₁ χ χv xp₁ xm₁) (D₂ : IsRootCell i₂ χ χv xp₂ xm₂) :
    ∃ ψ : G₁ ≅ G₂, i₁ ≫ ψ.hom = i₂ := by
  have := hG₁.smooth
  have := hG₁.isAffineHom
  have := hG₁.connectedSpace
  have := hG₂.smooth
  have := hG₂.isAffineHom
  have := hG₂.connectedSpace
  have : GeometricallyIntegral G₁.X.hom :=
    smoothConnectedAffineGeometry.1 k G₁ inferInstance inferInstance inferInstance
  have : GeometricallyIntegral G₂.X.hom :=
    smoothConnectedAffineGeometry.1 k G₂ inferInstance inferInstance inferInstance
  have := D₁.isOpenImmersion
  have := D₂.isOpenImmersion
  obtain ⟨ψ, hψ⟩ := CellGluing.exists_iso_of_cellCompatible
    (Dynamic.tripleCellMultiplication xm₁ i₁ xp₁) (Dynamic.tripleCellMultiplication xm₂ i₂ xp₂)
    (unitPt T) unitPt_comp unitPt_comp (cellCompatible D₁ D₂) (cellCompatible D₂ D₁)
  refine ⟨ψ, Grp.hom_ext _ _ ?_⟩
  rw [Grp.comp_hom_hom, ← torusPt_comp (xm := xm₁) (xp := xp₁), Category.assoc, hψ,
    torusPt_comp]

end RootCell

open RootCell in
/-- **Reduction of the rank-one isomorphism theorem to the open cell.** The Isomorphism
Theorem in semisimple rank at most one, for a common split maximal torus, follows from the
existence of root groups whose open cell satisfies the rank-one relation. -/
theorem splitRankOneCommonTorusIsomorphism_of_rootCell
    (h : SplitRankOneRootCellStatement.{u}) : SplitRankOneCommonTorusIsomorphismStatement.{u} := by
  intro k _ G₁ G₂ hG₁ hG₂ T hT i₁ i₂ hi₁ hi₂ J₁ J₂ P₁ P₂ hP₁ hP₂ e hroot hcoroot hrk
  have := hG₁.isAffineHom
  have := hG₂.isAffineHom
  rcases isEmpty_or_nonempty J₁ with hJ | ⟨⟨r₁⟩⟩
  · exact exists_iso_of_roots_eq_empty hG₁ hG₂ hT hi₁ hi₂ hP₁ hP₂ e hroot
      (by rw [← hP₁.2.1, Set.range_eq_empty])
  have hroots : roots i₂ = roots i₁ := roots_eq_of_isRootDatumOf_of_reindex hP₁ hP₂ e hroot
  obtain ⟨xp₁, xm₁, D₁⟩ := h k G₁ hG₁ T hT i₁ hi₁ J₁ P₁ hP₁ hrk r₁
  obtain ⟨xp₂, xm₂, D₂⟩ := h k G₂ hG₂ T hT i₂ hi₂ J₂ P₂ hP₂
    (fun α hα β hβ => hrk α (hroots ▸ hα) β (hroots ▸ hβ)) (e r₁)
  have D₂' : IsRootCell i₂ (P₂.root (e r₁)) (P₂.coroot (e r₁)) xp₂ xm₂ :=
    ⟨D₂.1, D₂.2.1, D₂.2.2.1, D₂.2.2.2.1, D₂.2.2.2.2⟩
  rw [show P₂.root (e r₁) = P₁.root r₁ from congrFun hroot r₁,
    show P₂.coroot (e r₁) = P₁.coroot r₁ from congrFun hcoroot r₁] at D₂'
  exact RootCell.exists_iso hG₁ hG₂ ⟨D₁.1, D₁.2.1, D₁.2.2.1, D₁.2.2.2.1, D₁.2.2.2.2⟩ D₂'

end Langlands.GroupScheme
