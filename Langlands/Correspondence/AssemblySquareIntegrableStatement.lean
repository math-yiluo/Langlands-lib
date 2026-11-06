import Langlands.Correspondence.AssemblyLFactorStatement

/-!
# Essentially square-integrable assembly images

Henniart 2002, §§2.6-2.9: the assembly of a supercuspidal map `c0` sends an
indecomposable parameter `σ ⊗ Sp(m)` to `St_m(c0 σ)`, and the classification of
irreducible classes by multisets of essentially square-integrable ones makes the
essentially square-integrable classes exactly the images of indecomposable
parameters. This file states the direction used to test against lower-rank
indecomposable parameters. It is a statement, not a proof.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance assemblySquareIntegrableFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance assemblySquareIntegrableGeneralLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

/-- Essentially square-integrable assembly images (statement only). For every
supercuspidal map `c0`, if a parameter class `D` is assembled from `c0` to the class
of an essentially square-integrable irreducible admissible representation `A`, then
`D` is indecomposable. -/
def AssemblySquareIntegrablePreimageStatement : Prop :=
  ∀ (c0 : SupercuspidalMap.{uF, uP, uA} F) (n : ℕ+) (D : WeilDeligneClass.{uF, uP} F n)
    (A : AutomorphicObject.{uF, uA} F n),
    IsAssembledFrom F c0 D (automorphicClassOf F A) →
    F.canonicalTopologicalData.IsEssentiallySquareIntegrable A.obj.representation →
    IsIndecomposableParameterClass F D

end Langlands.Correspondence
