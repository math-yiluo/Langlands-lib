import Langlands.BruhatTits.IntegralModels.UnramifiedPrescribedQuotientAttainment
import Langlands.GroupScheme.IntegralModel.SpecialFibreKernelTorus
import Langlands.GroupScheme.Torus.UnipotentQuotientMaximalSplit
import Langlands.GroupScheme.Absolute.SplitParabolicCocharacterProof

/-! # Incident-ray realization of parabolics containing the fixed residue torus -/

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

private def fixedTorus_groupIso {B : Scheme.{u}} {T U : CommGroupScheme B}
    (e : T ≅ U) : T.toGrp ≅ U.toGrp where
  hom := CommGroupScheme.groupHom e.hom
  inv := CommGroupScheme.groupHom e.inv
  hom_inv_id := congrArg Additive.toMul e.hom_inv_id
  inv_hom_id := congrArg Additive.toMul e.inv_hom_id

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)
    (D : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G)
    (x : C.Apartment)
    (hN : D.neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' {x}))

private instance fixedTorus_neutralSmooth : Smooth D.neutral.group.X.hom :=
  D.neutral_smooth

private instance fixedTorus_henselian : HenselianLocalRing (fixedFieldIntegers F) :=
  (separableUnramifiedArithmetic F).2.2.2.2

private instance fixedTorus_algClosed :
    IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
  (fixedFieldResidueIsAlgClosure F).1

private instance fixedTorus_specialAffine :
    IsAffineHom D.neutral.specialFibre.X.hom :=
  MorphismProperty.pullback_snd _ _ (inferInstanceAs (IsAffineHom D.neutral.group.X.hom))

private instance fixedTorus_specialFiniteType :
    LocallyOfFiniteType D.neutral.specialFibre.X.hom :=
  MorphismProperty.pullback_snd _ _
    (inferInstanceAs (LocallyOfFiniteType D.neutral.group.X.hom))

/-- The chosen integral apartment torus is a maximal torus in the full
special fibre of the neutral zero-fixer model. -/
theorem unramifiedZeroFixer_specialFibreInclusion_isMaximalTorus :
    IsMaximalTorus
      (unramifiedZeroFixerIntegralSplitTorusData C E D.neutral {x} hN).specialFibreInclusion := by
  let A := unramifiedZeroFixerIntegralSplitTorusData C E D.neutral {x} hN
  have hgen : IsMaximalSplitTorus (D.neutral.genericTorusMap A.torus A.inclusion) := by
    have hcomm : D.neutral.genericTorusMap A.torus A.inclusion =
        CommGroupScheme.groupHom A.genericIso.hom ≫ C.i := A.generic_comm
    rw [hcomm]
    exact C.isMaximalSplitTorus.iso_comp (fixedTorus_groupIso A.genericIso)
  exact IntegralModel.isMaximalTorus_specialFibre_of_generic C.isConnectedReductive
    D.neutral A.isSplit
    (unramifiedZeroFixerIntegralSplitTorusData_isClosedSubgroup
      C E D.neutral {x} hN) hgen

variable (Q : SpecialFibreQuotientData D)

/-- The same chosen residue torus maps isomorphically onto a maximal torus
in every supplied reductive quotient. -/
theorem unramifiedZeroFixer_quotientTorusInclusion_isMaximalTorus
    (hQ : Q.IsReductiveQuotient) :
    IsMaximalTorus
      ((unramifiedZeroFixerIntegralSplitTorusData C E D.neutral {x} hN).specialFibreInclusion ≫
        Q.projection) := by
  let : Smooth Q.radical.X.hom := hQ.1.smooth
  let : ConnectedSpace Q.radical.X.left := hQ.1.connectedSpace
  let : Smooth Q.quotient.X.hom := hQ.2.2.smooth
  have hmax := unramifiedZeroFixer_specialFibreInclusion_isMaximalTorus C E D x hN
  exact hmax.comp_of_perfect_field_unipotent_kernel Q.radicalInclusion
    hQ.1.isClosedSubgroup hQ.1.isUnipotent Q.projection hQ.2.1

/-- Every supplied parabolic containing the fixed residue torus is exactly
the schematic quotient image of every actual zero-fixer comparison at one
selected incident ray point, conditional on positive-root reduction. -/
theorem exists_incidentRay_quotientImage_eq_of_parabolic_contains_torus
    (hQ : Q.IsReductiveQuotient)
    (hpositive : UnramifiedRootPositiveReductionStatement.{u})
    (P : GroupScheme
      (Spec (CommRingCat.of (IsLocalRing.ResidueField (fixedFieldIntegers F)))))
    (i : P ⟶ Q.quotient)
    (f : (unramifiedZeroFixerIntegralSplitTorusData
      C E D.neutral {x} hN).specialFibreTorus.toGrp ⟶ P)
    (hi : IsParabolicSubgroup i)
    (hf : f ≫ i =
      (unramifiedZeroFixerIntegralSplitTorusData C E D.neutral {x} hN).specialFibreInclusion ≫
        Q.projection) :
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
            SubgroupFunctor.range
                (SchematicImage.inclusion (φ.specialFibreMap ≫ Q.projection)) =
              SubgroupFunctor.range i := by
  let A := unramifiedZeroFixerIntegralSplitTorusData C E D.neutral {x} hN
  obtain ⟨ν, hν⟩ := splitParabolicCocharacterStatement
    (IsLocalRing.ResidueField (fixedFieldIntegers F)) Q.quotient hQ.2.2
    A.specialFibreTorus (A.specialFibreInclusion ≫ Q.projection) A.specialFibreTorus_isSplit
    (unramifiedZeroFixer_quotientTorusInclusion_isMaximalTorus C E D x hN Q hQ)
    P i f hi hf
  obtain ⟨ε, hε, hface, heq⟩ :=
    exists_pos_incidentFacet_quotientImage_eq_parabolic C E D x hN Q hQ hpositive ν
  refine ⟨ν, ε, hε, hface, ?_⟩
  intro M hsm hgc hM φ
  exact (heq M hM φ).trans (by simpa only [Category.assoc] using hν.symm)

/-- Conditional realization of every quotient parabolic containing the
chosen residue torus by the corresponding incident ray comparisons. -/
def HasFixedTorusIncidentQuotientAttainment : Prop :=
  Q.IsReductiveQuotient → UnramifiedRootPositiveReductionStatement.{u} →
    ∀ (P : GroupScheme
      (Spec (CommRingCat.of (IsLocalRing.ResidueField (fixedFieldIntegers F)))))
      (i : P ⟶ Q.quotient)
      (f : (unramifiedZeroFixerIntegralSplitTorusData
        C E D.neutral {x} hN).specialFibreTorus.toGrp ⟶ P),
      IsParabolicSubgroup i →
      f ≫ i =
        (unramifiedZeroFixerIntegralSplitTorusData C E D.neutral {x} hN).specialFibreInclusion ≫
          Q.projection →
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
              SubgroupFunctor.range
                  (SchematicImage.inclusion (φ.specialFibreMap ≫ Q.projection)) =
                SubgroupFunctor.range i

theorem hasFixedTorusIncidentQuotientAttainment :
    HasFixedTorusIncidentQuotientAttainment C E D x hN Q := by
  intro hQ hpositive P i f hi hf
  exact exists_incidentRay_quotientImage_eq_of_parabolic_contains_torus
    C E D x hN Q hQ hpositive P i f hi hf

end Langlands.BruhatTits.IntegralModels
