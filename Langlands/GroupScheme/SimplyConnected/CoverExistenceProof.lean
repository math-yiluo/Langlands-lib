import Langlands.GroupScheme.SimplyConnected.FiniteGaloisExistenceReduction
import Langlands.GroupScheme.SimplyConnected.SplitCoverExistenceProof
import Langlands.GroupScheme.SimplyConnected.UniversalPropertyProof
import Langlands.GroupScheme.SimplyConnected.SemisimpleFieldExtensionProof
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof
import Langlands.GroupScheme.Descent.TensorFullCoverProof
import Langlands.FieldTheory.FiniteGaloisTensorDecompositionProof

/-! # Proof: existence of simply connected central covers over arbitrary fields -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Finite Galois semisimplicity ascent is the finite Galois case of ascent along an arbitrary
field extension. -/
theorem semisimpleFiniteGaloisAscent : SemisimpleFiniteGaloisAscentStatement.{u} := by
  intro k L _ _ _ _ _ G hG
  exact isSemisimpleFieldExtension k L G hG

/-- All seven inputs of the finite Galois existence reduction are proved. -/
theorem finiteGaloisCoverExistenceInputs : FiniteGaloisCoverExistenceInputsStatement.{u} :=
  ⟨torusFiniteGaloisSplitting, maximalTorusBaseChange, semisimpleFiniteGaloisAscent,
    splitSimplyConnectedCoverExistence, simplyConnectedCentralCoverUniversalProperty,
    Langlands.FieldTheory.finiteGaloisTensorDecomposition,
    simplyConnectedCoverTensorDescent.{u, u}⟩

/-- **Existence of the simply connected central cover** (CGP, Corollary A.4.11(1), with the
unique-factorization law of Milne, Proposition 18.8). Every semisimple group scheme over an
arbitrary field has an actual simply connected central cover. -/
theorem simplyConnectedCoverExistence : SimplyConnectedCoverExistenceStatement.{u} :=
  simplyConnectedCoverExistence_of_finiteGaloisInputs finiteGaloisCoverExistenceInputs

end Langlands.GroupScheme
