import Langlands.GroupScheme.Nilpotent.EmptyRoots
import Langlands.GroupScheme.Torus.NoTorusStructuralReductionProof
import Langlands.GroupScheme.Nilpotent.CentralTorusProof
import Langlands.GroupScheme.Lie.SemisimpleCentralizerSmooth
import Langlands.GroupScheme.Lie.SemisimpleCentralizerSpanningProof
import Langlands.GroupScheme.Lie.SemisimpleIsogenyReduction

/-! # Cartan structure over algebraically closed fields and the remaining input -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G C : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {j : C ⟶ G}

/-- Over an algebraically closed field, a Cartan subgroup has a single
nilpotence bound on the points of every relative scheme test. -/
theorem IsCartanSubgroup.exists_hasUniformNilpotentPoints_of_isAlgClosed
    [IsAlgClosed k] (hj : IsCartanSubgroup j) :
    ∃ d, HasUniformNilpotentPoints C d :=
  hj.centralTorusQuotient.exists_hasUniformNilpotentPoints_of_isAlgClosed

/-- A chosen all-test nilpotence bound for a Cartan subgroup over an
algebraically closed field. -/
def IsCartanSubgroup.nilpotenceBoundOfIsAlgClosed
    [IsAlgClosed k] (hj : IsCartanSubgroup j) : ℕ :=
  Classical.choose hj.exists_hasUniformNilpotentPoints_of_isAlgClosed

/-- The chosen bound applies to every relative scheme test. -/
theorem IsCartanSubgroup.nilpotenceBoundOfIsAlgClosed_spec
    [IsAlgClosed k] (hj : IsCartanSubgroup j) :
    HasUniformNilpotentPoints C hj.nilpotenceBoundOfIsAlgClosed :=
  Classical.choose_spec hj.exists_hasUniformNilpotentPoints_of_isAlgClosed

/-- A Cartan subgroup over an algebraically closed field is geometrically
nilpotent without any arbitrary-field maximal-torus base-change input. -/
theorem IsCartanSubgroup.isNilpotentGroupScheme_of_isAlgClosed
    [IsAlgClosed k] (hj : IsCartanSubgroup j) : IsNilpotentGroupScheme C :=
  hj.nilpotenceBoundOfIsAlgClosed_spec.isNilpotentGroupScheme

/-- The full Cartan structure conclusion over an algebraically closed field. -/
theorem IsCartanSubgroup.structure_of_isAlgClosed
    [IsAlgClosed k] (hj : IsCartanSubgroup j) :
    Smooth C.X.hom ∧ ConnectedSpace C.X.left ∧ IsNilpotentGroupScheme C :=
  ⟨hj.smooth_connected.1, hj.smooth_connected.2,
    hj.isNilpotentGroupScheme_of_isAlgClosed⟩

/-- The exact arbitrary-field Cartan structure target follows from
geometrically maximal torus existence over finite fields. All other
structural inputs are supplied by published proofs. -/
theorem cartanStructure_of_finiteFieldGeometricMaximalTorus
    (hfinite : FiniteFieldGeometricMaximalTorusStatement.{u}) :
    CartanStructureStatement.{u} :=
  cartanStructure_of_noTorusUnipotent
    (noTorusStructuralReduction nilpotentCentralTorusStatement hfinite
      algClosedTrivialMaximalTorusUnipotent Lie.semisimpleCentralizerSmooth
      Lie.semisimpleCentralizerSpanning semisimpleIsogenyReduction)

end Langlands.GroupScheme
