import Langlands.BruhatTits.IntegralModels.FacetRootSignBaseChange
import Langlands.GroupScheme.Reductive.SeparableUnipotentRadicalProof
import Langlands.GroupScheme.Rational.PseudoParabolicAmbientTransport
import Langlands.GroupScheme.FppfQuotientComparison
import Langlands.GroupScheme.Reductive.AlgebraicExtensionAscent
import Langlands.GroupScheme.IntegralModel.ConnectedFibreDescent

/-! # Generic coefficient base change of actual reductive special-fibre quotients -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme

section ReductiveQuotient

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (A L : Type u) [CommRing A] [IsDomain A] [Field L]
  [Algebra R A] [Algebra A L] [IsFractionRing A L]
  [Algebra K L] [Algebra R L] [IsScalarTower R A L] [IsScalarTower R K L]
  [IsLocalRing R] [IsLocalRing A] [IsLocalHom (algebraMap R A)]

private instance neutralSpecialFibre_smooth (D : RelativeComponentModelData R K G) :
    Smooth D.neutral.specialFibre.X.hom := by
  have : Smooth D.neutral.group.X.hom := D.neutral_smooth
  change Smooth (pullback.snd D.neutral.group.X.hom (IntegralModel.residueBaseMap R))
  infer_instance

private instance neutralSpecialFibre_isAffineHom (D : RelativeComponentModelData R K G) :
    IsAffineHom D.neutral.specialFibre.X.hom := by
  change IsAffineHom (pullback.snd D.neutral.group.X.hom (IntegralModel.residueBaseMap R))
  infer_instance

/-- **Base change of a maximal reductive quotient along a separable algebraic
residue field extension.** If the residue field extension of `R → A` is
separable and algebraic, the residue-field base change of a maximal reductive
quotient of the neutral special fibre is a maximal reductive quotient of the
special fibre of the base-changed model. -/
theorem SpecialFibreQuotientData.isReductiveQuotient_baseChange
    [Algebra.IsSeparable (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A)]
    [Algebra.IsAlgebraic (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A)]
    {D : RelativeComponentModelData R K G} (Q : SpecialFibreQuotientData D)
    (hQ : Q.IsReductiveQuotient) : (Q.baseChange A L).IsReductiveQuotient := by
  have hconn : ConnectedSpace D.neutral.specialFibre.X.left :=
    D.neutral.hasConnectedSpecialFibre_of_hasConnectedFibres D.neutral_connectedFibres
  refine ⟨?_, ?_, ?_⟩
  · have h1 := (separableAlgebraicUnipotentRadical (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField A) D.neutral.specialFibre inferInstance inferInstance
      hconn).1 Q.radical Q.radicalInclusion hQ.1
    exact h1.comp_iso _
  · have h2 := (hQ.2.1.baseChange (algebraBaseMap (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField A))).comapIso (specialFibreSquareIso A D.neutral.group)
    change RelativeRoot.IsFppfQuotient (SubgroupFunctor.range
      ((GroupScheme.baseChange _).map Q.radicalInclusion ≫
        (specialFibreSquareIso A D.neutral.group).hom)) _
    rw [SubgroupFunctor.range_comp_iso, SubgroupFunctor.range_baseChangeHom]
    exact h2
  · exact hQ.2.2.baseChange_of_algebraicExtension

end ReductiveQuotient

/-- Reductive special-fibre quotients persist under a coefficient square whose
residue-field extension is separable algebraic. -/
def SpecialFibreQuotientBaseChangeStatement : Prop :=
  ∀ (R K : Type u) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (G : GroupScheme (Spec (CommRingCat.of K)))
    (A L : Type u) [CommRing A] [IsDomain A] [Field L]
    [Algebra R A] [Algebra A L] [IsFractionRing A L]
    [Algebra K L] [Algebra R L] [IsScalarTower R A L] [IsScalarTower R K L]
    [IsLocalRing R] [IsLocalRing A] [IsLocalHom (algebraMap R A)]
    [Algebra.IsSeparable (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A)]
    [Algebra.IsAlgebraic (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A)]
    (D : RelativeComponentModelData R K G) (Q : SpecialFibreQuotientData D),
    Q.IsReductiveQuotient → (Q.baseChange A L).IsReductiveQuotient

/-- The generic coefficient base-change statement follows from the unchanged
published special-fibre quotient theorem. -/
theorem specialFibreQuotientBaseChange : SpecialFibreQuotientBaseChangeStatement.{u} := by
  intro R K _ _ _ _ _ G A L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D Q hQ
  exact Q.isReductiveQuotient_baseChange A L hQ

end Langlands.BruhatTits.IntegralModels
