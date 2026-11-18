import Langlands.GroupScheme.OddOrthogonalMatrix.FullInnerAutomorphisms
import Langlands.GroupScheme.EvenOrthogonalForm.GaloisStage

/-! # Finite Galois local isomorphisms of forms of the full split odd group -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.OddOrthogonalForm

variable (K : Type u) [Field K]

/-- The full split odd norm-one group over the indicated field. -/
abbrev splitGroup (n : ℕ) := OddOrthogonalMatrix.groupScheme (Fin n) K

/-- The actual full split odd group commutes with field extension. -/
def splitBaseChangeIso (N : Type u) [Field N] [Algebra K N] (n : ℕ) :
    (GroupScheme.baseChange (algebraBaseMap K N)).obj (splitGroup K n) ≅ splitGroup N n :=
  OddOrthogonalMatrix.baseChangeModelIso (algebraBaseMap K N)

/-- A form split over the separable closure has actual local isomorphisms
to the full split odd group along a finite Galois extension. -/
theorem exists_galois_localIso (H : GroupScheme (Spec (CommRingCat.of K)))
    [IsAffineHom H.X.hom] (n : ℕ)
    (e : (GroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).obj H ≅
      splitGroup (SeparableClosure K) n) :
    ∃ (N : Type u) (_ : Field N) (_ : Algebra K N) (_ : FiniteDimensional K N)
      (_ : IsGalois K N), Nonempty (LocalGroupIso H (splitGroup K n) (ringTest K N)) := by
  obtain ⟨L, _, _, _, _, ⟨φ⟩⟩ :=
    Descent.FiniteStage.exists_finiteSeparable_localIso_of_separableClosure K
      (e ≪≫ (splitBaseChangeIso K (SeparableClosure K) n).symm)
  let N := IntermediateField.normalClosure K L (SeparableClosure K)
  let f : L →ₐ[K] N :=
    (normalClosure.algHomEquiv K L (SeparableClosure K)).symm IsSepClosed.lift
  exact ⟨N, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨φ.refine (QuasiSplitInnerForm.coverRefinement f)⟩⟩

end Langlands.GroupScheme.OddOrthogonalForm
