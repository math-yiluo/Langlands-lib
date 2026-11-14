import Langlands.BruhatTits.IntegralModels.UnramifiedFixedTorusParabolicAttainment
import Langlands.GroupScheme.Absolute.ParabolicMaximalTorusProof
import Langlands.GroupScheme.Absolute.QuotientNormalizer
import Langlands.GroupScheme.Rational.ParabolicAmbientTransport

/-! # Integral conjugation and arbitrary quotient parabolics -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

namespace Langlands.BruhatTits.IntegralModels

private theorem parabolic_conjugate_contains_fixed_torus
    {k : Type u} [Field k] [IsAlgClosed k]
    (H : GroupScheme (Spec (CommRingCat.of k)))
    (hH : IsConnectedReductive H)
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (j : T.toGrp ⟶ H) (hj : IsMaximalTorus j)
    (P : GroupScheme (Spec (CommRingCat.of k)))
    (i : P ⟶ H) (hi : IsParabolicSubgroup i) :
    ∃ (g : rationalPoints H) (f : T.toGrp ⟶ P),
      f ≫ (i ≫ (H.innerIso g).hom) = j := by
  let : Smooth H.X.hom := hH.smooth
  let : IsAffineHom H.X.hom := hH.isAffineHom
  let : ConnectedSpace H.X.left := hH.connectedSpace
  obtain ⟨T', j', f', hj', hf'⟩ := parabolicMaximalTorus k H hH P i hi
  obtain ⟨g, e, he⟩ := maximalTorusConjugacy k H T' T j' j hj' hj
  have hinv : CommGroupScheme.groupHom e.inv ≫ CommGroupScheme.groupHom e.hom =
      𝟙 T.toGrp := congrArg Additive.toMul e.inv_hom_id
  refine ⟨g, CommGroupScheme.groupHom e.inv ≫ f', ?_⟩
  calc
    _ = CommGroupScheme.groupHom e.inv ≫ (f' ≫ i) ≫ (H.innerIso g).hom := by
      simp only [Category.assoc]
    _ = CommGroupScheme.groupHom e.inv ≫ j' ≫ (H.innerIso g).hom := by rw [hf']
    _ = CommGroupScheme.groupHom e.inv ≫ CommGroupScheme.groupHom e.hom ≫ j := by
      rw [he]
    _ = j := by rw [← Category.assoc, hinv, Category.id_comp]

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)
    (D : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G)
    (x : C.Apartment)
    (hN : D.neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' {x}))
    (Q : SpecialFibreQuotientData D)

private instance conjugate_neutralSmooth : Smooth D.neutral.group.X.hom :=
  D.neutral_smooth

private instance conjugate_henselian : HenselianLocalRing (fixedFieldIntegers F) :=
  (separableUnramifiedArithmetic F).2.2.2.2

private instance conjugate_algClosed :
    IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
  (fixedFieldResidueIsAlgClosure F).1

private instance conjugate_specialAffine :
    IsAffineHom D.neutral.specialFibre.X.hom :=
  MorphismProperty.pullback_snd _ _ (inferInstanceAs (IsAffineHom D.neutral.group.X.hom))

include hN in
/-- A rational point of the supplied quotient lifts to an actual integral
section of the neutral zero-fixer model, whose generic point fixes x. -/
theorem exists_integralSection_quotient_lift
    (hQ : Q.IsReductiveQuotient) (g : rationalPoints Q.quotient) :
    ∃ s : D.neutral.integralSections,
      D.neutral.reduction s ≫ Q.projection.hom.hom = g ∧
      D.neutral.integralPointMap s ∈
        E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' {x}) := by
  let : LocallyOfFinitePresentation Q.projection.hom.hom.left := hQ.2.1.2.2.1
  let : LocallyOfFiniteType Q.projection.hom.hom.left := inferInstance
  let : Surjective Q.projection.hom.hom.left := hQ.2.1.2.1
  obtain ⟨a, ha⟩ := exists_rationalPointLift Q.projection g
  obtain ⟨s, hs⟩ := D.neutral.reduction_surjective D.neutral_smooth a
  refine ⟨s, by rw [hs, ha], ?_⟩
  rw [← hN]
  exact ⟨s, rfl⟩

/-- Every supplied quotient parabolic is attained by an inverse integral
conjugate of the actual quotient comparison at one incident ray point. -/
theorem exists_incidentRay_conjugate_quotientImage_eq_parabolic
    (hQ : Q.IsReductiveQuotient)
    (hpositive : UnramifiedRootPositiveReductionStatement.{u})
    (P : GroupScheme
      (Spec (CommRingCat.of (IsLocalRing.ResidueField (fixedFieldIntegers F)))))
    (i : P ⟶ Q.quotient) (hi : IsParabolicSubgroup i) :
    ∃ s : D.neutral.integralSections,
      D.neutral.integralPointMap s ∈
        E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' {x}) ∧
      ∃ ν : cocharacterLattice
        (unramifiedZeroFixerIntegralSplitTorusData C E D.neutral {x} hN).specialFibreTorus,
        let A := unramifiedZeroFixerIntegralSplitTorusData C E D.neutral {x} hN
        let w := C.cocharacterDirection (A.cocharacterSpecialization.symm ν)
        ∃ ε : ℝ, 0 < ε ∧
          AffineRootSystem.IsFaceOf C.affineRoots
            (AffineRootSystem.facet C.affineRoots x)
            (AffineRootSystem.facet C.affineRoots (ε • w +ᵥ x)) ∧
          ∀ (M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G)
            [Smooth M.group.X.hom] [GeometricallyConnected M.group.X.hom],
            M.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer
              (C.apartmentMap '' {ε • w +ᵥ x}) →
            ∀ φ : M.Hom D.neutral (𝟙 G),
              SubgroupFunctor.range (SchematicImage.inclusion
                ((φ.specialFibreMap ≫ Q.projection) ≫
                  (Q.quotient.innerIso
                    (D.neutral.reduction s ≫ Q.projection.hom.hom)).inv)) =
                SubgroupFunctor.range i := by
  let A := unramifiedZeroFixerIntegralSplitTorusData C E D.neutral {x} hN
  obtain ⟨g, f, hf⟩ := parabolic_conjugate_contains_fixed_torus Q.quotient hQ.2.2
    A.specialFibreTorus (A.specialFibreInclusion ≫ Q.projection)
    (unramifiedZeroFixer_quotientTorusInclusion_isMaximalTorus C E D x hN Q hQ)
    P i hi
  obtain ⟨s, hs, hsmem⟩ := exists_integralSection_quotient_lift C E D x hN Q hQ g
  obtain ⟨ν, ε, hε, hface, heq⟩ :=
    exists_incidentRay_quotientImage_eq_of_parabolic_contains_torus C E D x hN Q
      hQ hpositive P (i ≫ (Q.quotient.innerIso g).hom) f
      (hi.comp_iso (Q.quotient.innerIso g)) hf
  refine ⟨s, hsmem, ν, ε, hε, hface, ?_⟩
  intro M hMsmooth hMconnected hM φ
  have himage := heq M hM φ
  rw [hs]
  calc
    _ = (SubgroupFunctor.range (SchematicImage.inclusion
        (φ.specialFibreMap ≫ Q.projection))).comap (Q.quotient.innerIso g).hom :=
      SchematicImage.range_inclusion_comp_iso
        (φ.specialFibreMap ≫ Q.projection) (Q.quotient.innerIso g).symm
    _ = _ := by
      rw [himage, SubgroupFunctor.range_comp_iso i (Q.quotient.innerIso g),
        ← SubgroupFunctor.comap_comp, Iso.hom_inv_id, SubgroupFunctor.comap_id]

/-- Conditional attainment of arbitrary quotient parabolics by actual
quotient comparisons followed by inverse conjugation from an integral section. -/
def HasConjugateIncidentQuotientAttainment : Prop :=
  Q.IsReductiveQuotient → UnramifiedRootPositiveReductionStatement.{u} →
    ∀ (P : GroupScheme
      (Spec (CommRingCat.of (IsLocalRing.ResidueField (fixedFieldIntegers F)))))
      (i : P ⟶ Q.quotient), IsParabolicSubgroup i →
      ∃ s : D.neutral.integralSections,
        D.neutral.integralPointMap s ∈
          E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' {x}) ∧
        ∃ ν : cocharacterLattice
          (unramifiedZeroFixerIntegralSplitTorusData C E D.neutral {x} hN).specialFibreTorus,
          let A := unramifiedZeroFixerIntegralSplitTorusData C E D.neutral {x} hN
          let w := C.cocharacterDirection (A.cocharacterSpecialization.symm ν)
          ∃ ε : ℝ, 0 < ε ∧
            AffineRootSystem.IsFaceOf C.affineRoots
              (AffineRootSystem.facet C.affineRoots x)
              (AffineRootSystem.facet C.affineRoots (ε • w +ᵥ x)) ∧
            ∀ (M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G)
              [Smooth M.group.X.hom] [GeometricallyConnected M.group.X.hom],
              M.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer
                (C.apartmentMap '' {ε • w +ᵥ x}) →
              ∀ φ : M.Hom D.neutral (𝟙 G),
                SubgroupFunctor.range (SchematicImage.inclusion
                  ((φ.specialFibreMap ≫ Q.projection) ≫
                    (Q.quotient.innerIso
                      (D.neutral.reduction s ≫ Q.projection.hom.hom)).inv)) =
                  SubgroupFunctor.range i

theorem hasConjugateIncidentQuotientAttainment :
    HasConjugateIncidentQuotientAttainment C E D x hN Q := by
  intro hQ hpositive P i hi
  exact exists_incidentRay_conjugate_quotientImage_eq_parabolic C E D x hN Q
    hQ hpositive P i hi

end Langlands.BruhatTits.IntegralModels
