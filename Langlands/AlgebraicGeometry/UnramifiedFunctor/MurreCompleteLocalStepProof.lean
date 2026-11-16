import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCompleteAssembly
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCompleteEtale

/-! # Step 2a of Murre's induction: the complete local step

Bourbaki exp. 294 (Murre), Step 2a of the proof of Theorem 1: over a complete local
noetherian ring `R`, a presheaf satisfying Murre's conditions which is represented over the
punctured spectrum and over the spectra of the rings `R/m^(k+1)` is represented by a separated,
locally of finite type, formally unramified scheme. -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite IsLocalRing

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

open CompleteLocal

/-- Step 2a of Murre's induction (Bourbaki exp. 294): the complete local step. -/
theorem murreCompleteLocalStep : MurreCompleteLocalStepStatement.{u, v} := by
  intro R _ _ _ F hF hX' hY
  obtain ⟨X', q', ⟨e'⟩, -, hlft', hfu'⟩ := id hX'
  choose Y q he _ hlft hfu using hY
  exact unramifiedRepresentable_of_chartEtale hF e' (fun k ↦ (he k).some)
    (fun y z hz ↦ chartElem_infinitesimallyEtaleAt (fun k ↦ (he k).some) hF hX' y z hz)

end Langlands.AlgebraicGeometry.UnramifiedFunctor
