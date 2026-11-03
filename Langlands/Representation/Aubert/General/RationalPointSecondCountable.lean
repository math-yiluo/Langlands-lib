import Langlands.Representation.Aubert.General.RationalPointFamily
import Langlands.GroupScheme.AffinePointFiniteCoordinates
import Langlands.GroupScheme.AffinePointRingPointComparison
import Mathlib.NumberTheory.LocalField.Basic

/-! # Second countability for rational points over local fields -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Langlands.AlgebraicGeometry.PointTopology

theorem localField_secondCountable (k : Type u) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    SecondCountableTopology k := by
  let := IsTopologicalAddGroup.rightUniformSpace k
  have := isUniformAddGroup_of_addCommGroup (G := k)
  let : (Valued.v (R := k)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := k).comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
    have : ProperSpace k :=
      .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k
    infer_instance

/-- Finite-type affine rational points inherit second countability from the
local field, for precisely the published identity-test point topology. -/
theorem rationalPoint_secondCountable (k : Type u) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] :
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    SecondCountableTopology (RationalPoint k G.X) := by
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : SecondCountableTopology k := localField_secondCountable k
  let : TopologicalSpace (G.affinePoints (CommAlgCat.of k k)) :=
    G.affinePointsTopologicalSpace (CommAlgCat.of k k)
  have : SecondCountableTopology (G.affinePoints (CommAlgCat.of k k)) :=
    G.affinePointsSecondCountableTopology (CommAlgCat.of k k)
  have : SecondCountableTopology (RingPoint k G.X k) :=
    (G.affinePointsRingPointHomeomorph (CommAlgCat.of k k)).symm.secondCountableTopology
  exact (rationalPointHomeomorph k G.X).secondCountableTopology

/-- The finite-type premise is automatic for the smooth connected reductive
groups occurring in the parabolic-modulus target. -/
theorem reductiveRationalPoint_secondCountable (k : Type u) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G) :
    haveI := hG.isAffineHom
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    SecondCountableTopology (RationalPoint k G.X) := by
  have := hG.isAffineHom
  have := hG.smooth
  exact rationalPoint_secondCountable k G

end Langlands.Aubert.General.RationalPointFamily
