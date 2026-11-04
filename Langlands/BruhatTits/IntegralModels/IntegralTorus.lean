import Langlands.BruhatTits.IntegralModels.RelativeComponent
import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.GroupScheme.SimplyConnected.Basic

/-! # The integral split torus in a supplied KP model

The torus and its maps are actual group schemes and morphisms. Their KP
properties are predicates, without any assertion that the data exist.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}

/-- Supplied torus and generic-fibre identification for KP Axiom 4.1.20(3).
The inclusion targets the actual relative component of the supplied full model.
Closedness, splitting and special-fibre maximality are validity assertions. -/
structure IntegralTorusData (D : RelativeComponentModelData R K G)
    (S : CommGroupScheme (Spec (CommRingCat.of K))) (i : S.toGrp ⟶ G) where
  torus : CommGroupScheme (Spec (CommRingCat.of R))
  genericIso : (baseChange (Spec.algebraMap R K)).obj torus.toGrp ≅ S.toGrp
  inclusion : torus.toGrp ⟶ D.neutral.group
  generic_comm :
    (baseChange (Spec.algebraMap R K)).map inclusion ≫ D.neutral.genericIso.hom =
      genericIso.hom ≫ i

namespace IntegralTorusData

variable {D : RelativeComponentModelData R K G}
  {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}
  (T : IntegralTorusData D S i)

/-- The supplied integral torus is split over the integral base and is closed in
`G^0_Ω`, as required in the first sentence of KP Axiom 4.1.20(3). -/
def IsClosedSplit : Prop :=
  IsSplitTorus T.torus.toGrp ∧ IsClosedSubgroup T.inclusion

section Residue

variable [IsLocalRing R]

/-- The actual special fibre of the integral torus, kept commutative. -/
abbrev specialFibre : CommGroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R))) :=
  (CommGroupScheme.baseChange (IntegralModel.residueBaseMap R)).obj T.torus

/-- The actual residue-base change of the inclusion into the neutral model. -/
def specialFibreInclusion : T.specialFibre.toGrp ⟶ D.neutral.specialFibre :=
  (baseChange (IntegralModel.residueBaseMap R)).map T.inclusion

/-- The second sentence of KP Axiom 4.1.20(3) concerns a maximal split torus of
the neutral special fibre, before taking any reductive quotient. -/
def HasMaximalSplitSpecialFibre : Prop :=
  IsMaximalSplitTorus T.specialFibreInclusion

/-- The complete torus clause of KP Axiom 4.1.20(3) on these supplied maps. -/
def SatisfiesTorusClause : Prop :=
  T.IsClosedSplit ∧ T.HasMaximalSplitSpecialFibre

/-- Changing integral sections to the residue field respects the torus inclusion. -/
theorem reduction_naturality (x : rationalPoints T.torus.toGrp) :
    D.neutral.reduction (rationalPoints.map T.inclusion x) =
      rationalPoints.map T.specialFibreInclusion
        (baseChangeSectionHom (IntegralModel.residueBaseMap R) T.torus.toGrp x) :=
  baseChangeSectionHom_naturality (IntegralModel.residueBaseMap R) T.inclusion x

end Residue
end IntegralTorusData

namespace RelativeComponentModelData

variable (D : RelativeComponentModelData R K G)

/-- KP Axiom 4.1.20(4): for a semisimple simply connected generic group, the
actual relative-component inclusion is an isomorphism. The Library's
`IsSimplyConnected` already includes semisimplicity. -/
def HasEqualComponentsForSimplyConnected : Prop :=
  IsSimplyConnected G → IsIso D.inclusion.hom

end RelativeComponentModelData
end Langlands.BruhatTits.IntegralModels
