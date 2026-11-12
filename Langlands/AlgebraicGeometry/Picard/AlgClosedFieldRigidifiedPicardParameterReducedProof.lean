import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldRigidifiedPicardParameterReducedStatement
import Langlands.AlgebraicGeometry.Picard.FieldPicardIdentityComponent
import Langlands.AlgebraicGeometry.Picard.RigidifiedUniversalGroupObject
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof
import Langlands.AlgebraicGeometry.Modules.PullbackTensorUnitProofs
import Langlands.AlgebraicGeometry.Modules.ExplicitPullbackTensorAssociativityProofs
import Langlands.AlgebraicGeometry.Modules.TensorMonoidalComparisonProofs
import Langlands.AlgebraicGeometry.Modules.PullbackTensorCompatibilityProofs
import Langlands.AlgebraicGeometry.Picard.LocalComparisonProof
import Langlands.AlgebraicGeometry.Picard.FieldUniversalRigidifiedPicardTangentH1Proof
import Langlands.AlgebraicGeometry.FieldPointTangentLocalRegularityProof
import Langlands.AbelianScheme.FieldStructureSheafH1DimensionBoundProof
import Langlands.CommutativeAlgebra.RegularLocalDomainProof
import Langlands.GroupScheme.AlgClosedFieldReducedOfOriginProof
import Langlands.AlgebraicGeometry.SmoothConnectedRelativeDimensionProof
import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldRigidifiedPicardOriginDimensionLowerBoundProof
import Langlands.AbelianScheme.AlgebraicallyClosedFieldAmpleExistenceProof
import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldAmpleTranslationStabilizerFiniteProof
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! # Reducedness of an actual universal rigidified Picard parameter

Construct the group object from universality, prove regularity at its origin
using the tangent and local-dimension bounds, and propagate reducedness by the
published group-scheme theorem.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle

open Langlands.Scheme.Modules

variable {S X : Scheme.{u}} (f : X ⟶ S) (ε : S ⟶ X) (section_eq : ε ≫ f = 𝟙 S)
  {P : Over S} (L : relative f ε section_eq P) (hL : IsUniversal f ε section_eq L)

/-- The group object on the actual universal parameter, with all coherence
and local-comparison inputs supplied by published theorems. -/
@[instance_reducible]
def actualUniversalCommGrpObj : CommGrpObj P :=
  universalCommGrpObj pullbackTensorComparisonIsIso pullbackTensorUnitCoherence
    explicitPullbackTensorAssociativity tensorMonoidalLeftUnitorComparison
    pullbackTensorSymmetry locallyFreeRankOneIffTensorInvertible
    f ε section_eq pullbackTensorComposition L hL

/-- The unit classifies the trivial rigidified family. -/
lemma actualUniversal_unit_eq_trivialParameter :
    letI := actualUniversalCommGrpObj f ε section_eq L hL
    η[P] = trivialParameter f ε section_eq L hL := by
  let := actualUniversalCommGrpObj f ε section_eq L hL
  exact (MonObj.one_eq_one P).trans
    (one_eq_trivialParameter pullbackTensorComparisonIsIso pullbackTensorUnitCoherence
      explicitPullbackTensorAssociativity tensorMonoidalLeftUnitorComparison
      pullbackTensorSymmetry locallyFreeRankOneIffTensorInvertible
      f ε section_eq pullbackTensorComposition L hL)

end Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- The constructed group-object identity is the published Picard origin. -/
lemma actualUniversal_unit_point_eq_fullPicardOriginPoint
    (k : Type u) [Field k]
    (A : AbelianScheme (Spec (CommRingCat.of k)))
    {P : Over (Spec (CommRingCat.of k))} (L : RigidifiedFamily A P)
    (hL : RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A)
      (unitSection_comp A) L) :
    letI := RigidifiedLineBundle.actualUniversalCommGrpObj
      A.X.hom (unitSection A) (unitSection_comp A) L hL
    (η[P]).left (IsLocalRing.closedPoint k) = fullPicardOriginPoint k A L hL := by
  let := RigidifiedLineBundle.actualUniversalCommGrpObj
    A.X.hom (unitSection A) (unitSection_comp A) L hL
  change (η[P]).left (IsLocalRing.closedPoint k) =
    (RigidifiedLineBundle.trivialParameter
      A.X.hom (unitSection A) (unitSection_comp A) L hL).left (IsLocalRing.closedPoint k)
  rw [RigidifiedLineBundle.actualUniversal_unit_eq_trivialParameter
    A.X.hom (unitSection A) (unitSection_comp A) L hL]

/-- The actual tangent module is finite dimensional, with dimension at most `g`. -/
theorem rigidifiedPicardOriginTangentFiniteAndFinrankLe
    (k : Type u) [Field k]
    (A : AbelianScheme (Spec (CommRingCat.of k)))
    (P : Over (Spec (CommRingCat.of k))) (L : RigidifiedFamily A P)
    (hL : RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A)
      (unitSection_comp A) L)
    (g : ℕ) (hft : LocallyOfFiniteType P.hom) (hdim : A.HasRelativeDimension g) :
    let e := RigidifiedLineBundle.trivialParameter A.X.hom (unitSection A)
      (unitSection_comp A) L hL
    let T := Langlands.Scheme.tangentSpaceAtPoint P e
    FiniteDimensional k T ∧ Module.finrank k T ≤ g := by
  obtain ⟨equiv⟩ := fieldUniversalRigidifiedPicardTangentH1 k A P L hL hft
  have hbound := fieldStructureSheafH1DimensionBound k A g hdim
  have := hbound.1
  exact ⟨equiv.symm.finiteDimensional, equiv.finrank_eq.trans_le hbound.2⟩

/-- The tangent upper bound and stalk-dimension lower bound give regularity. -/
theorem rigidifiedPicardOriginStalkRegular
    (k : Type u) [Field k]
    (A : AbelianScheme (Spec (CommRingCat.of k)))
    (P : Over (Spec (CommRingCat.of k))) (L : RigidifiedFamily A P)
    (hL : RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A)
      (unitSection_comp A) L)
    (g : ℕ) (hft : LocallyOfFiniteType P.hom) (hdim : A.HasRelativeDimension g)
    (hlower : (g : WithBot ℕ∞) ≤
      ringKrullDim (P.left.presheaf.stalk (fullPicardOriginPoint k A L hL))) :
    IsRegularLocalRing (P.left.presheaf.stalk (fullPicardOriginPoint k A L hL)) := by
  let e := RigidifiedLineBundle.trivialParameter A.X.hom (unitSection A)
    (unitSection_comp A) L hL
  exact (Langlands.Scheme.fieldPointTangentLocalRegularity k P e hft).2.2 g
    (rigidifiedPicardOriginTangentFiniteAndFinrankLe k A P L hL g hft hdim).2 hlower

/-- The regular origin stalk is a domain and hence reduced. -/
theorem rigidifiedPicardOriginStalkReduced
    (k : Type u) [Field k]
    (A : AbelianScheme (Spec (CommRingCat.of k)))
    (P : Over (Spec (CommRingCat.of k))) (L : RigidifiedFamily A P)
    (hL : RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A)
      (unitSection_comp A) L)
    (g : ℕ) (hft : LocallyOfFiniteType P.hom) (hdim : A.HasRelativeDimension g)
    (hlower : (g : WithBot ℕ∞) ≤
      ringKrullDim (P.left.presheaf.stalk (fullPicardOriginPoint k A L hL))) :
    _root_.IsReduced (P.left.presheaf.stalk (fullPicardOriginPoint k A L hL)) := by
  have := Langlands.CommutativeAlgebra.regularLocalDomain _
    (rigidifiedPicardOriginStalkRegular k A P L hL g hft hdim hlower)
  infer_instance

/-- Every locally finite type parameter carrying an actual universal rigidified
family for an abelian scheme over an algebraically closed field is reduced. -/
theorem algClosedFieldRigidifiedPicardParameterReduced :
    AlgClosedFieldRigidifiedPicardParameterReducedStatement.{u} := by
  intro k _ _ A P L hL hft
  let := RigidifiedLineBundle.actualUniversalCommGrpObj
    A.X.hom (unitSection A) (unitSection_comp A) L hL
  apply Langlands.GroupScheme.algClosedFieldReducedOfOrigin k P hft
  rw [actualUniversal_unit_point_eq_fullPicardOriginPoint k A L hL]
  have : Subsingleton (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have : Nonempty (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))) :=
    inferInstanceAs (Nonempty (PrimeSpectrum k))
  have hconnected : ConnectedSpace A.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := A.X.hom)
  obtain ⟨g, hg⟩ :=
    Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension
      A.X.left _ A.X.hom inferInstance hconnected
  obtain ⟨M, hM⟩ := Langlands.GroupScheme.algebraicallyClosedFieldAmpleExistence
    k A.toGrp inferInstance inferInstance inferInstance
  have hfinite := algClosedFieldAmpleTranslationStabilizerFinite k A M hM
  exact rigidifiedPicardOriginStalkReduced k A P L hL g hft hg
    (algClosedFieldRigidifiedPicardOriginDimensionLowerBound k A P L hL g hft hg M hfinite)

end Langlands.AbelianScheme
