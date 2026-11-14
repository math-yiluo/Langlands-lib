import Langlands.BruhatTits.IntegralModels.UnramifiedConjugateParabolicAttainment
import Langlands.BruhatTits.IntegralModels.UnramifiedRadicalConjugation
import Langlands.GroupScheme.Rational.SubgroupConjugacyDescent

/-! # Actual integral comparisons from conjugated source models -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

namespace Langlands.GroupScheme

private theorem section_baseChange_eq_basePoint
    {S T : Scheme.{u}} (b : T ⟶ S) (H : GroupScheme S)
    (s : Over.mk (𝟙 S) ⟶ H.X) :
    baseChangeSectionHom b H s = baseChangeBasePoint b H s := by
  rfl

namespace IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    {M N : IntegralModel R K G}

/-- Conjugation by an actual target integral section changes the source generic
identification and gives an actual morphism over the generic identity. -/
def Hom.conjugateSource (φ : M.Hom N (𝟙 G)) (s : N.integralSections) :
    (M.transport (G.innerIso (N.integralPointMap s)⁻¹)).Hom N (𝟙 G) where
  hom := φ.hom ≫ (N.group.innerIso s⁻¹).hom
  generic_comm := by
    have hp : baseChangeBasePoint (Spec.algebraMap R K) N.group s⁻¹ ≫
        N.genericIso.hom.hom.hom = (N.integralPointMap s)⁻¹ := by
      rw [← section_baseChange_eq_basePoint]
      change N.integralPointMap s⁻¹ = _
      exact map_inv N.integralPointMap s
    change (GroupScheme.baseChange (Spec.algebraMap R K)).map
        (φ.hom ≫ (N.group.innerIso s⁻¹).hom) ≫ N.genericIso.hom =
      (M.genericIso.hom ≫ (G.innerIso (N.integralPointMap s)⁻¹).hom) ≫ 𝟙 G
    rw [Functor.map_comp, Category.assoc, baseChange_innerIso_hom,
      innerIso_hom_comp, hp, ← Category.assoc, φ.generic_comm,
      Category.comp_id, Category.comp_id]

variable [IsLocalRing R]

/-- The quotient comparison of the conjugated source is exactly the original
quotient comparison followed by the inverse inner automorphism of the reduced
and projected integral section. -/
theorem Hom.conjugateSource_specialFibreMap_comp
    (φ : M.Hom N (𝟙 G)) (s : N.integralSections)
    {H : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R)))}
    (q : N.specialFibre ⟶ H) :
    (φ.conjugateSource s).specialFibreMap ≫ q =
      (φ.specialFibreMap ≫ q) ≫
        (H.innerIso (N.reduction s ≫ q.hom.hom)).inv := by
  have hp : baseChangeBasePoint (residueBaseMap R) N.group s⁻¹ =
      (N.reduction s)⁻¹ := by
    rw [← section_baseChange_eq_basePoint]
    exact map_inv N.reduction s
  have hq : (N.reduction s)⁻¹ ≫ q.hom.hom =
      (N.reduction s ≫ q.hom.hom)⁻¹ :=
    map_inv (rationalPoints.map q) (N.reduction s)
  change (GroupScheme.baseChange (residueBaseMap R)).map
      (φ.hom ≫ (N.group.innerIso s⁻¹).hom) ≫ q = _
  rw [Functor.map_comp, Category.assoc, baseChange_innerIso_hom, hp,
    innerIso_hom_comp, hq, innerIso_inv_hom, ← Category.assoc]
  rfl

end IntegralModel
end Langlands.GroupScheme

namespace Langlands.BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]

/-- Generic inner transport carries an arbitrary characterized building subset
to its translate, preserving the same zero datum. -/
theorem integralPoints_transport_eq_translated_zeroFixer
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)
    (g : rationalPoints G) (Y : Set C.ReducedBuilding)
    (M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G)
    (hM : M.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer Y) :
    (M.transport (G.innerIso g)).integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (g • Y) := by
  have hzero : E.zeroPoints.map (rationalPoints.map (G.innerIso g).hom) =
      E.zeroPoints := by
    rw [rationalPoints_map_innerIso]
    exact Subgroup.normal_iff_map_conj_eq.mp E.normal_zeroPoints g
  have hfix : (C.pointwiseFixer Y).map
      (rationalPoints.map (G.innerIso g).hom) = C.pointwiseFixer (g • Y) := by
    rw [rationalPoints_map_innerIso]
    exact SubMulAction.fixingSubgroup_map_conj_eq rfl
  rw [M.transport_integralPoints, hM,
    Subgroup.map_inf_eq _ _ _ (rationalPoints_map_injective_of_iso _), hzero, hfix]

variable (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)
    (D : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G)
    (x : C.Apartment)
    (hN : D.neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' {x}))
    (Q : SpecialFibreQuotientData D)

/-- An arbitrary quotient parabolic is the actual quotient image of the
comparison from the integrally conjugated source model. The transported model
is characterized by the same zero datum at the translated ray point. -/
theorem exists_translatedIncidentRay_quotientImage_eq_parabolic
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
            (M.transport (G.innerIso (D.neutral.integralPointMap s)⁻¹)).integralPoints =
                E.zeroPoints ⊓ C.pointwiseFixer
                  ((D.neutral.integralPointMap s)⁻¹ •
                    (C.apartmentMap '' {ε • w +ᵥ x})) ∧
              ∀ φ : M.Hom D.neutral (𝟙 G),
                SubgroupFunctor.range (SchematicImage.inclusion
                  ((φ.conjugateSource s).specialFibreMap ≫ Q.projection)) =
                    SubgroupFunctor.range i := by
  obtain ⟨s, hs, ν, ε, hε, hface, heq⟩ :=
    exists_incidentRay_conjugate_quotientImage_eq_parabolic
      C E D x hN Q hQ hpositive P i hi
  refine ⟨s, hs, ν, ε, hε, hface, ?_⟩
  intro M hMsmooth hMconnected hM
  refine ⟨integralPoints_transport_eq_translated_zeroFixer C E
    (D.neutral.integralPointMap s)⁻¹ _ M hM, ?_⟩
  intro φ
  rw [φ.conjugateSource_specialFibreMap_comp s Q.projection]
  exact heq M hM φ

/-- Conditional actual quotient attainment from a source model characterized
at a translated incident ray point. The section and ray are chosen before all
supplied source models and comparison morphisms. -/
def HasTranslatedIncidentQuotientAttainment : Prop :=
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
              (M.transport (G.innerIso (D.neutral.integralPointMap s)⁻¹)).integralPoints =
                  E.zeroPoints ⊓ C.pointwiseFixer
                    ((D.neutral.integralPointMap s)⁻¹ •
                      (C.apartmentMap '' {ε • w +ᵥ x})) ∧
                ∀ φ : M.Hom D.neutral (𝟙 G),
                  SubgroupFunctor.range (SchematicImage.inclusion
                    ((φ.conjugateSource s).specialFibreMap ≫ Q.projection)) =
                      SubgroupFunctor.range i

theorem hasTranslatedIncidentQuotientAttainment :
    HasTranslatedIncidentQuotientAttainment C E D x hN Q := by
  intro hQ hpositive P i hi
  exact exists_translatedIncidentRay_quotientImage_eq_parabolic C E D x hN Q
    hQ hpositive P i hi

end Langlands.BruhatTits.IntegralModels
