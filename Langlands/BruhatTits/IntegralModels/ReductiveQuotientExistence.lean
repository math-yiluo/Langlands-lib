import Langlands.BruhatTits.IntegralModels.SpecialFibre
import Langlands.GroupScheme.IntegralModel.ConnectedFibreDescent
import Langlands.GroupScheme.Reductive.UnipotentRadicalExistenceProof
import Langlands.GroupScheme.Reductive.UnipotentRadicalQuotientProof
import Langlands.GroupScheme.Reductive.PerfectFieldProof
import Langlands.GroupScheme.Absolute.UnipotentQuotientProperParabolics

/-! # Reductive quotients of actual neutral special fibres -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
  {G : GroupScheme (Spec (CommRingCat.of K))}

namespace SpecialFibreQuotientData

local instance quotientSource_smooth (D : RelativeComponentModelData R K G) :
    Smooth D.neutral.specialFibre.X.hom := by
  let : Smooth D.neutral.group.X.hom := D.neutral_smooth
  change Smooth (CategoryTheory.Limits.pullback.snd D.neutral.group.X.hom
    (IntegralModel.residueBaseMap R))
  infer_instance

local instance quotientSource_connectedSpace (D : RelativeComponentModelData R K G) :
    ConnectedSpace D.neutral.specialFibre.X.left :=
  D.neutral.hasConnectedSpecialFibre_of_hasConnectedFibres D.neutral_connectedFibres

local instance quotientSource_affine (D : RelativeComponentModelData R K G) :
    IsAffineHom D.neutral.specialFibre.X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd D.neutral.group.X.hom
    (IntegralModel.residueBaseMap R))
  infer_instance

/-- A supplied neutral model with perfect residue field admits an actual
represented radical and connected reductive fppf quotient of its special fibre. -/
theorem exists_isReductiveQuotient (D : RelativeComponentModelData R K G)
    [PerfectField (IsLocalRing.ResidueField R)] :
    ∃ Q : SpecialFibreQuotientData D, Q.IsReductiveQuotient := by
  obtain ⟨U, i, hi⟩ :=
    unipotentRadicalExistence (IsLocalRing.ResidueField R) D.neutral.specialFibre
  obtain ⟨H, q, hq, hH⟩ :=
    unipotentRadicalQuotient (IsLocalRing.ResidueField R) D.neutral.specialFibre U i hi
  let Q : SpecialFibreQuotientData D :=
    { radical := U
      radicalInclusion := i
      quotient := H
      quotient_affine := hH.isAffineHom
      projection := q }
  exact ⟨Q, hi, hq,
    (perfectFieldPseudoReductive (IsLocalRing.ResidueField R) H).mp hH⟩

variable {D : RelativeComponentModelData R K G} {Q : SpecialFibreQuotientData D}

/-- Valid quotient data determine smoothness, connectedness and unipotence of
the actual scheme-theoretic kernel of the displayed projection. -/
theorem hasSmoothConnectedUnipotentKernel (hQ : Q.IsReductiveQuotient) :
    HasSmoothConnectedUnipotentKernel Q.projection := by
  let : Smooth Q.radical.X.hom := hQ.1.smooth
  let : ConnectedSpace Q.radical.X.left := hQ.1.connectedSpace
  exact HasSmoothConnectedUnipotentKernel.of_representative Q.radicalInclusion
    hQ.1.isClosedSubgroup hQ.1.isUnipotent hQ.2.1

/-- Absence of proper rational parabolic embeddings in the actual neutral
special fibre is equivalent to the same property in its reductive quotient. -/
theorem noProperParabolic_iff (hQ : Q.IsReductiveQuotient) :
    (∀ (P : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R))))
      (i : P ⟶ D.neutral.specialFibre), IsParabolicSubgroup i → IsIso i) ↔
    (∀ (P : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R))))
      (j : P ⟶ Q.quotient), IsParabolicSubgroup j → IsIso j) := by
  let : Flat Q.projection.hom.hom.left := hQ.2.1.1
  let : Surjective Q.projection.hom.hom.left := hQ.2.1.2.1
  let : LocallyOfFinitePresentation Q.projection.hom.hom.left := hQ.2.1.2.2.1
  exact UnipotentQuotientParabolics.noProperParabolic_iff Q.projection
    (hasSmoothConnectedUnipotentKernel hQ)

end SpecialFibreQuotientData

/-- Existence of the actual reductive special-fibre quotient for every supplied
relative-component model with perfect residue field. -/
def SpecialFibreReductiveQuotientExistenceStatement : Prop :=
  ∀ (R K : Type u) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
    [PerfectField (IsLocalRing.ResidueField R)]
    (G : GroupScheme (Spec (CommRingCat.of K)))
    (D : RelativeComponentModelData R K G),
    ∃ Q : SpecialFibreQuotientData D, Q.IsReductiveQuotient

/-- Construct the radical and its quotient using the published field-group
existence theorems on the actual special fibre. -/
theorem specialFibreReductiveQuotientExistence :
    SpecialFibreReductiveQuotientExistenceStatement.{u} := by
  intro R K _ _ _ _ _ _ _ G D
  exact SpecialFibreQuotientData.exists_isReductiveQuotient D

end Langlands.BruhatTits.IntegralModels
