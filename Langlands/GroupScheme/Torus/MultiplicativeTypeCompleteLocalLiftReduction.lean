import Langlands.GroupScheme.Torus.CompleteLocalSimultaneousSplitting
import Langlands.GroupScheme.Torus.MultiplicativeTypeCompleteLocalLiftStatement
import Langlands.GroupScheme.Torus.MultiplicativeTypeQuasiIsotrivialProof
import Langlands.GroupScheme.Torus.MultiplicativeTypeAdicLiftStatement
import Langlands.GroupScheme.Torus.MultiplicativeTypeLocalClosed
import Mathlib.RingTheory.Henselian

/-! # Reduction of lifting over complete local rings to adic lifting -/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace Langlands.GroupScheme

/-- A local ring which is complete for its maximal ideal is a Henselian local ring. -/
theorem henselianLocalRing_of_isAdicComplete (A : Type u) [CommRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] : HenselianLocalRing A :=
  CompleteLocalDeformation.henselianLocalRing_of_complete A

/-- **Reduction of Conrad's Corollary B.3.5** to the finite étale splitting of groups of
multiplicative type over Henselian local rings and to the lifting theorem over adically
complete noetherian rings. -/
theorem multiplicativeTypeCompleteLocalLift_of_quasiIsotrivial_of_adicLift
    (hQ : MultiplicativeTypeQuasiIsotrivialStatement.{u})
    (hA : MultiplicativeTypeAdicLiftStatement.{u}) :
    MultiplicativeTypeCompleteLocalLiftStatement.{u} := by
  intro A _ _ _ _ G H _ _ hH
  have := henselianLocalRing_of_isAdicComplete A
  have hsplit := hQ.2 A H hH
  obtain ⟨h1, h2⟩ := hA A (maximalIdeal A) H G hsplit
  exact ⟨h1, h2, fun f hf =>
    MultiplicativeTypeLocalClosed.isClosedSubgroup_of_isotrivial hsplit f hf⟩

/-- **Reduction of Conrad's Corollary B.3.5** to the lifting theorem over adically complete
noetherian rings, using the published quasi-isotriviality theorem
`multiplicativeTypeQuasiIsotrivial`. -/
theorem multiplicativeTypeCompleteLocalLift_of_adicLift
    (hA : MultiplicativeTypeAdicLiftStatement.{u}) :
    MultiplicativeTypeCompleteLocalLiftStatement.{u} :=
  multiplicativeTypeCompleteLocalLift_of_quasiIsotrivial_of_adicLift
    multiplicativeTypeQuasiIsotrivial hA

end Langlands.GroupScheme
