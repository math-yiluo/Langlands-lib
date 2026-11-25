import Langlands.GaloisCohomology.Global.BrauerSequence.Proof
import Langlands.GaloisCohomology.Global.BrauerSequence.HigherDegrees.RealDegrees

/-!
# The Brauer sequence of a number field in the degrees above two

For a number field `K`, a separable closure `Ω` and a choice of embeddings `ι`:

* `H³(Gal(Ω/K), Ωˣ) = 0` (`subsingleton_cohomology_three_unitsModule`, proved in
  `BrauerSequence/HigherDegrees/DegreeThree.lean`);
* for `r ≥ 4` the localization to the real places
  `Hʳ(Gal(Ω/K), Ωˣ) → ∏_{w real} Hʳ(Gal(K̄_w/K_w), K̄_wˣ)` is bijective
  (`bijective_realBrauerLocalization`, `BrauerSequence/HigherDegrees/RealDegrees.lean`).

Together they are `UnitsCohomologyHigherDegreesStatement` (`unitsCohomologyHigherDegreesStatement`),
and with `brauerSequenceStatement_of_higherDegrees` the fundamental exact sequence of the Brauer
group holds with no hypothesis (`brauerSequenceStatement`).
-/

namespace Langlands.GaloisCohomology

universe u

/-- **The cohomology of `Ωˣ` in degrees above two**: `H³(Gal(Ω/K), Ωˣ) = 0`, and in degrees `r ≥ 4`
the localization to the real places is an isomorphism, for every number field `K`, separable
closure `Ω` and choice of embeddings `ι`. -/
theorem unitsCohomologyHigherDegreesStatement : UnitsCohomologyHigherDegreesStatement.{u} :=
  fun _ _ _ _ _ _ _ ι => ⟨subsingleton_cohomology_three_unitsModule, bijective_realBrauerLocalization ι⟩

/-- **The fundamental exact sequence of the Brauer group of a number field**, with its
consequences (`BrauerSequenceData`), for every number field, separable closure and choice of
embeddings. -/
theorem brauerSequenceStatement : BrauerSequenceStatement.{u} :=
  brauerSequenceStatement_of_higherDegrees unitsCohomologyHigherDegreesStatement

end Langlands.GaloisCohomology
