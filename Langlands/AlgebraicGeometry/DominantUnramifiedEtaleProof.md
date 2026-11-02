# Dominant unramified morphisms over geometrically unibranch integral bases

Authors: Worker 208 and Worker 122.

`Langlands.AlgebraicGeometry.DominantUnramifiedEtaleProof.dominantUnramifiedEtale`
proves exactly `Langlands.AlgebraicGeometry.DominantUnramifiedEtaleStatement.{u}`
for an arbitrary universe `u`. For actual integral schemes `X` and `Y` and a
morphism `f : X ⟶ Y`, it assumes `GeometricallyUnibranchIntegralScheme Y`,
`LocallyOfFiniteType f`, `FormallyUnramified f` and `IsDominant f`, and concludes
Mathlib's `Etale f` for that same morphism. The source's generic extension is
unrestricted. The theorem has exactly the published hypotheses.

The proof globalizes the published theorem
`UnramifiedGeometricallyUnibranchLocalCriterionProof.unramifiedGeometricallyUnibranchLocalCriterion`
from `Langlands.AlgebraicGeometry.UnramifiedGeometricallyUnibranchLocalCriterionProof`.
That local result applies to an injective finite type formally unramified map of
domains and an arbitrary model of the base localization at the contracted prime.
Geometric unibranchness of that local domain gives an etale principal neighborhood
of the chosen source prime. Its three independent universes are specialized to
`u,u,u` here, the universes of affine section rings and the actual stalks.

`etale_ringHom_of_exists_away` glues these principal neighborhoods. The elements
whose principal localizations are etale generate the unit ideal: a maximal ideal
containing all of them would contradict the neighborhood supplied at that prime.
Mathlib's localization-span criterion for `RingHom.Etale` then proves etaleness
of the original ring map. This argument also covers a ring with empty prime
spectrum.

`injective_appLE_of_dominant` proves injectivity of the section map for compatible
affine opens when the source open is nonempty. Such an open is dense in the
integral source. Its composite map to `Y` is therefore dominant; factoring through
the open immersion from the target affine chart shows that the induced map of
affine spectra is dominant. The ring-map kernel is contained in the nilradical
of the base affine ring. That ring is reduced by integrality of `Y`, so the
kernel is zero.

`dominantUnramifiedEtale_of_localCriterion` performs the affine reduction. Fix
compatible affine opens `U` of `Y` and `V` of `X`. For each prime of the section
ring of `V`, the affine equivalence supplies its point `x` in `V`. Both opens are
then nonempty, so their section rings are domains. The section map is injective
by the previous helper and inherits finite type and formal unramifiedness from
`f`. Compatibility of affine primes with that map identifies the contracted
prime with the prime corresponding to `f x` in `U`. The actual structure-sheaf
stalk at `f x` is a localization at this prime and satisfies geometric
unibranchness by the hypothesis on `Y`. Applying the local criterion gives the
etale principal neighborhood, and the first helper glues the result on the
section map. Mathlib's affine definition of `Etale` finishes the scheme proof.
For an empty source affine open there is no prime to check. The final theorem
supplies the proved local criterion to this helper, discharging its only
explicit premise beyond the named scheme statement.

The literature provenance is the integral-source dominant specialization of
Stacks Project Lemma 37.37.1, tag [0GS8](https://stacks.math.columbia.edu/tag/0GS8),
whose proof uses the local unramified criterion of Lemma 15.109.2, tag
[0GSC](https://stacks.math.columbia.edu/tag/0GSC). The retained registered original
is `stacks-dominant-unramified-etale-2026-11-01`, files `0GS8.html` and `0GSC.html`,
folder SHA-256 `1216511f5e584381bec8be680f09519c8133ff0ea406fc89ca7e275a68f4a103`.
The original statements, proofs and empty comment sections were read. The
implemented affine injectivity and localization-span gluing are internal
reductions of this route. The target statement pair and its imported dependency
closure are unchanged. This proof supplies the generic scheme criterion;
its applications to particular Harris component maps remain separate tasks.
