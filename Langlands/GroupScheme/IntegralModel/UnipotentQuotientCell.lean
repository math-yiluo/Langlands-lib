import Langlands.GroupScheme.Dynamic.UnipotentKernelOppositeCell
import Langlands.GroupScheme.IntegralModel.OpenCellSections

/-! # Integral opposite-cell coordinates detected in a special-fibre quotient -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

variable {A K : Type u} [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] [IsLocalRing A]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    (M : IntegralModel A K G) [Smooth M.group.X.hom]
    [ConnectedSpace M.specialFibre.X.left]
    (χ : (Gm (Spec (CommRingCat.of A))).toGrp ⟶ M.group)
    {U P : GroupScheme (Spec (CommRingCat.of A))}
    (i : U ⟶ M.group) (p : P ⟶ M.group)
    (hi : (Dynamic.unipotent (Dynamic.oppositeCocharacter χ)).IsRepresentedBy i)
    (hp : (Dynamic.parabolic χ).IsRepresentedBy p)
    {Q V W : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField A)))}
    [Smooth Q.X.hom] [IsAffineHom Q.X.hom] [ConnectedSpace Q.X.left]
    (q : M.specialFibre ⟶ Q)
    (hqs : Smooth q.hom.hom.left) (hqsurj : Surjective q.hom.hom.left)
    [ConnectedSpace (kernel q).X.left] (hN : IsUnipotent (kernel q))
    (j : V ⟶ Q) (r : W ⟶ Q)
    (hj : (Dynamic.unipotent (Dynamic.oppositeCocharacter
      (Dynamic.baseChangeCocharacter (residueBaseMap A) χ ≫ q))).IsRepresentedBy j)
    (hr : (Dynamic.parabolic
      (Dynamic.baseChangeCocharacter (residueBaseMap A) χ ≫ q)).IsRepresentedBy r)

include hi hp hj hr hqs hqsurj hN in
/-- An integral section factors through the actual opposite cell precisely
when its reduction has quotient opposite-cell coordinates. -/
theorem oppositeCell_section_lifts_iff_quotient_reduction (x : M.integralSections) :
    (∃ a : Over.mk (𝟙 (Spec (CommRingCat.of A))) ⟶ U.X ⊗ P.X,
      a ≫ SubgroupFunctor.cellMultiplication i p = x) ↔
      ∃ b : Over.mk (𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField A)))) ⟶ V.X ⊗ W.X,
        b ≫ SubgroupFunctor.cellMultiplication j r = M.reduction x ≫ q.hom.hom := by
  have : Smooth M.specialFibre.X.hom :=
    inferInstanceAs (Smooth (pullback.snd M.group.X.hom (residueBaseMap A)))
  have : IsAffineHom M.specialFibre.X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd M.group.X.hom (residueBaseMap A)))
  have hi₀ := hi.baseChange (residueBaseMap A)
  rw [← Dynamic.unipotent_baseChange, Dynamic.oppositeCocharacter,
    Dynamic.baseChangeCocharacter_powerHom] at hi₀
  have hp₀ := hp.baseChange (residueBaseMap A)
  rw [← Dynamic.parabolic_baseChange] at hp₀
  have hopen : IsOpenImmersion (SubgroupFunctor.cellMultiplication i p).left :=
    dynamicBaseOppositeCell _ M.group χ U P i p hi hp
  let := hopen
  rw [M.section_lifts_iff_reduction_lifts (SubgroupFunctor.cellMultiplication i p) x]
  rw [← Dynamic.oppositeCell_exists_lift_iff
    (Dynamic.baseChangeCocharacter (residueBaseMap A) χ) q hqs hqsurj hN
    ((GroupScheme.baseChange (residueBaseMap A)).map i)
    ((GroupScheme.baseChange (residueBaseMap A)).map p) j r hi₀ hp₀ hj hr (M.reduction x)]
  let e := asIso (CartesianMonoidalCategory.prodComparison
    (Over.pullback (residueBaseMap A)) U.X P.X)
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a ≫ e.hom, ?_⟩
    rw [Category.assoc]
    change a ≫ CartesianMonoidalCategory.prodComparison _ _ _ ≫ _ = _
    rw [← DynamicBaseOppositeCell.baseChange_cellMultiplication]
    exact ha
  · rintro ⟨b, hb⟩
    refine ⟨b ≫ e.inv, ?_⟩
    rw [DynamicBaseOppositeCell.baseChange_cellMultiplication]
    change (b ≫ e.inv) ≫ (e.hom ≫ _) = _
    rw [Category.assoc, e.inv_hom_id_assoc]
    exact hb

/-- Integral source coordinates chosen from supplied quotient coordinates
of the actual special-fibre reduction. -/
def oppositeCellSectionLift (x : M.integralSections)
    (b : Over.mk (𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField A)))) ⟶ V.X ⊗ W.X)
    (hb : b ≫ SubgroupFunctor.cellMultiplication j r = M.reduction x ≫ q.hom.hom) :
    Over.mk (𝟙 (Spec (CommRingCat.of A))) ⟶ U.X ⊗ P.X :=
  ((oppositeCell_section_lifts_iff_quotient_reduction M χ i p hi hp q hqs hqsurj hN
    j r hj hr x).mpr ⟨b, hb⟩).choose

@[reassoc]
theorem oppositeCellSectionLift_comp (x : M.integralSections)
    (b : Over.mk (𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField A)))) ⟶ V.X ⊗ W.X)
    (hb : b ≫ SubgroupFunctor.cellMultiplication j r = M.reduction x ≫ q.hom.hom) :
    oppositeCellSectionLift M χ i p hi hp q hqs hqsurj hN j r hj hr x b hb ≫
      SubgroupFunctor.cellMultiplication i p = x :=
  ((oppositeCell_section_lifts_iff_quotient_reduction M χ i p hi hp q hqs hqsurj hN
    j r hj hr x).mpr ⟨b, hb⟩).choose_spec

end Langlands.GroupScheme.IntegralModel
