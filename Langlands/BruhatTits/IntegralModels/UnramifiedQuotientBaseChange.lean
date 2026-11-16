import Langlands.BruhatTits.IntegralModels.SpecialFibrePositiveDescent
import Langlands.BruhatTits.IntegralModels.UnramifiedFacetSignDescent

/-! # The reductive quotient after maximal-unramified base change -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme Langlands.LocalGalois.Separable GaloisPointComparison

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}

local instance unramifiedQuotientIntegerAlgebra : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance unramifiedQuotientIntegerTower :
    IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance unramifiedQuotientResidueAlgebra :
    Algebra 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
  (residueToFixedField F).toAlgebra

local instance unramifiedQuotientBaseChangeAffine {S S' : Scheme.{u}} (b : S' ⟶ S)
    (M : GroupScheme S) [IsAffineHom M.X.hom] :
    IsAffineHom ((GroupScheme.baseChange b).obj M).X.hom := by
  change IsAffineHom (pullback.snd M.X.hom b)
  exact MorphismProperty.pullback_snd _ _ ‹IsAffineHom M.X.hom›

/-- The comparison of the two residue towers of `𝒪[F] → O`. -/
abbrev unramifiedResidueSquare (M : GroupScheme (Spec (CommRingCat.of ↥𝒪[F]))) :=
  Descent.squareComparison (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F))
    (IntegralModel.residueBaseMap (fixedFieldIntegers F)) (IntegralModel.residueBaseMap ↥𝒪[F])
    (Spec.algebraMap 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)))
    IntegralModel.unramifiedResidue_specMap_comp M

/-- The residue-field algebra `𝓀[F] → O/𝔪` given by `residueToFixedField` is
algebraic. -/
theorem unramifiedQuotientResidue_isAlgebraic :
    Algebra.IsAlgebraic 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
  (fixedFieldResidueIsAlgClosure F).isAlgebraic

/-- The residue-field algebra `𝓀[F] → O/𝔪` given by `residueToFixedField` is
separable, since `𝓀[F]` is finite. -/
theorem unramifiedQuotientResidue_isSeparable :
    Algebra.IsSeparable 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) := by
  have : Finite 𝓀[F] := inferInstance
  have := unramifiedQuotientResidue_isAlgebraic (F := F)
  infer_instance

namespace SpecialFibreQuotientData

/-- **Maximal-unramified base change of special-fibre quotient data.** Its
radical and quotient are the residue-field base changes of the supplied ones,
and its projection is the Library's `unramifiedSpecialFibreMap` of the supplied
projection. -/
def unramifiedBaseChange {D : RelativeComponentModelData ↥𝒪[F] F G}
    (Q : SpecialFibreQuotientData D) :
    SpecialFibreQuotientData (D.baseChange (fixedFieldIntegers F) (inertiaFixedField F)) where
  radical := (GroupScheme.baseChange
    (Spec.algebraMap 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)))).obj Q.radical
  radicalInclusion := (GroupScheme.baseChange
      (Spec.algebraMap 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)))).map
        Q.radicalInclusion ≫ (unramifiedResidueSquare D.neutral.group).inv
  quotient := (GroupScheme.baseChange
    (Spec.algebraMap 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)))).obj Q.quotient
  projection := D.neutral.unramifiedSpecialFibreMap Q.projection

theorem unramifiedBaseChange_projection {D : RelativeComponentModelData ↥𝒪[F] F G}
    (Q : SpecialFibreQuotientData D) :
    (Q.unramifiedBaseChange).projection =
      (unramifiedResidueSquare D.neutral.group).hom ≫
        (GroupScheme.baseChange
          (Spec.algebraMap 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)))).map
          Q.projection := by
  change Descent.squareComparisonMap _ _ _ _ _ _ _ = _
  rw [Descent.squareComparisonMap_def]

private instance unramifiedNeutralSpecialFibre_smooth
    (D : RelativeComponentModelData ↥𝒪[F] F G) :
    Smooth D.neutral.specialFibre.X.hom := by
  have : Smooth D.neutral.group.X.hom := D.neutral_smooth
  change Smooth (pullback.snd D.neutral.group.X.hom (IntegralModel.residueBaseMap ↥𝒪[F]))
  infer_instance

private instance unramifiedNeutralSpecialFibre_isAffineHom
    (D : RelativeComponentModelData ↥𝒪[F] F G) :
    IsAffineHom D.neutral.specialFibre.X.hom := by
  change IsAffineHom (pullback.snd D.neutral.group.X.hom (IntegralModel.residueBaseMap ↥𝒪[F]))
  infer_instance

set_option maxHeartbeats 2000000 in
/-- The maximal-unramified base change of a maximal reductive quotient is a
maximal reductive quotient of the special fibre of the base-changed model. -/
theorem isReductiveQuotient_unramifiedBaseChange {D : RelativeComponentModelData ↥𝒪[F] F G}
    (Q : SpecialFibreQuotientData D) (hQ : Q.IsReductiveQuotient) :
    (Q.unramifiedBaseChange).IsReductiveQuotient := by
  have := unramifiedQuotientResidue_isAlgebraic (F := F)
  have := unramifiedQuotientResidue_isSeparable (F := F)
  have hconn : ConnectedSpace D.neutral.specialFibre.X.left :=
    D.neutral.hasConnectedSpecialFibre_of_hasConnectedFibres D.neutral_connectedFibres
  refine ⟨?_, ?_, ?_⟩
  · have h1 := (separableAlgebraicUnipotentRadical 𝓀[F]
      (IsLocalRing.ResidueField (fixedFieldIntegers F)) D.neutral.specialFibre inferInstance
      inferInstance hconn).1 Q.radical Q.radicalInclusion hQ.1
    exact h1.comp_iso (unramifiedResidueSquare D.neutral.group).symm
  · have h2 := (hQ.2.1.baseChange (Spec.algebraMap 𝓀[F]
      (IsLocalRing.ResidueField (fixedFieldIntegers F)))).comapIso
        (unramifiedResidueSquare D.neutral.group).symm
    rw [unramifiedBaseChange_projection]
    change RelativeRoot.IsFppfQuotient (SubgroupFunctor.range
      ((GroupScheme.baseChange (Spec.algebraMap 𝓀[F]
        (IsLocalRing.ResidueField (fixedFieldIntegers F)))).map Q.radicalInclusion ≫
        (unramifiedResidueSquare D.neutral.group).symm.hom))
      ((unramifiedResidueSquare D.neutral.group).symm.inv ≫
        (GroupScheme.baseChange (Spec.algebraMap 𝓀[F]
          (IsLocalRing.ResidueField (fixedFieldIntegers F)))).map Q.projection)
    rw [SubgroupFunctor.range_comp_iso, SubgroupFunctor.range_baseChangeHom]
    exact h2
  · exact hQ.2.2.baseChange_of_algebraicExtension

/-- **Descent of the positive subgroup.** A rational point is positive for the
supplied quotient exactly when its maximal-unramified extension is positive for
the base-changed quotient. -/
theorem mem_positivePoints_iff_unramifiedBaseChange
    {D : RelativeComponentModelData ↥𝒪[F] F G}
    (Q : SpecialFibreQuotientData D) (hQ : Q.IsReductiveQuotient) (g : rationalPoints G) :
    g ∈ Q.positivePoints ↔
      rationalExtend F (inertiaFixedField F) G g ∈ (Q.unramifiedBaseChange).positivePoints := by
  rw [Q.positivePoints_eq_comap_unramifiedKernelPoints hQ.2.1,
    (Q.unramifiedBaseChange).positivePoints_eq_specialFibreKernelPoints
      (isReductiveQuotient_unramifiedBaseChange Q hQ).2.1]
  rfl

end SpecialFibreQuotientData

end Langlands.BruhatTits.IntegralModels
