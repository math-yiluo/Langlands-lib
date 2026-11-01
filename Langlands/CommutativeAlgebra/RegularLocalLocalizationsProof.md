# Prime localizations of regular local rings are regular

`Langlands.CommutativeAlgebra.regularLocalLocalizations.{u}` proves exactly
`Langlands.CommutativeAlgebra.RegularLocalLocalizationsStatement.{u}`:

```lean
∀ (R : Type u) [CommRing R], IsRegularLocalRing R → IsRegularRing R
```

The universe is arbitrary and there are no additional outer hypotheses.
Mathlib's `IsRegularRing R` includes regularity of `Localization.AtPrime p`
for every prime ideal `p`, including maximal and minimal primes. No
dimension, characteristic, residue-field, completeness, henselianity or
excellence restriction is imposed.

The helper `finiteProjectiveDimension_localization` starts with finite
projective dimension for every finite module over a commutative ring `R`.
For a finite module `N` over `Localization S`, it restricts scalars along
the canonical algebra map. Worker 362's published helper
`exists_fg_submodule_isLocalizedModule` then chooses a finitely generated
`R`-submodule `K` of `N` for which the inclusion exhibits `N` as the
localization of `K`. This helper is imported from
`Langlands.CommutativeAlgebra.FiniteModuleLocalizationDescent`.

The hypothesis gives a natural projective-dimension bound for `K`.
Mathlib's `ModuleCat.localizedModule_hasProjectiveDimensionLE` preserves
that bound on its canonical categorical localization. The universal
property of localized modules identifies this object with `N` by a
linear equivalence over `Localization S`. The corresponding categorical
isomorphism transfers the bound to `ModuleCat.of (Localization S) N`.
This helper requires neither localness nor Noetherianity of `R`.

The assembly `regularLocalLocalizations_of_homologicalCriteria` applies
this helper at `S = p.primeCompl` to the canonical residue field of
`Localization.AtPrime p`. Regularity of `R` supplies Noetherianity, so
Mathlib makes the prime localization Noetherian and local; its residue
field is a finite module. The residue-field criterion therefore gives
regularity of this localization. Mathlib's `isRegularRing_iff` assembles
these conclusions for all primes, with Noetherianity of `R` already
provided by the regular-local hypothesis.

The closing theorem supplies both homological inputs from the published
Library. `regularLocalFiniteProjectiveDimension` in
`Langlands.CommutativeAlgebra.RegularLocalFiniteProjectiveDimensionProof`
(Worker 254) gives the required finite-module property.
`residueFieldFiniteProjectiveDimensionRegular` in
`Langlands.CommutativeAlgebra.ResidueFieldFiniteProjectiveDimensionRegularProof`
(Worker 214) gives regularity from finite projective dimension of the
residue field. The intermediate
`regularLocalLocalizations_of_residueCriterion` supplies the first input
while keeping the second explicit. The final theorem supplies the second
as well. The proof imports the descent helper directly and has no
dependency on factoriality or the valuative-extension conclusions.

The result is the second sentence of Stacks Project Lemma 10.110.6,
[Tag 0AFS](https://stacks.math.columbia.edu/tag/0AFS). The implemented
homological argument uses finite modules and the residue-field criterion;
it does not need to construct a uniform global-dimension bound. The
localization inequality is Lemma 10.109.13,
[Tag 00O8](https://stacks.math.columbia.edu/tag/00O8), implemented in
Mathlib. The two homological inputs are the finite-module consequence of
Proposition 10.110.1,
[Tag 00O7](https://stacks.math.columbia.edu/tag/00O7), and implication
(1) to (3) of Proposition 10.110.5,
[Tag 00OC](https://stacks.math.columbia.edu/tag/00OC).

The complete retained `0AFS.html`, including its proof and empty comments
section, was read. It is in registered source
`stacks-regular-local-localizations-2026-11-01`, directory SHA-256
`36be521ada23e27c1eca7157d1965ba42be3180b96968bfe57ce1cb78e21c1c1`
(file SHA-256
`b87a3b180fd468914b8d74516dde72cc5a785d51ee4c36a495da50ecf2d6d55f`).
The complete retained `00O7.html`, `00OC.html` and `00O8.html` were read
in registered source `stacks-regular-local-homological-2026-11-01`,
directory SHA-256
`21820755db776b97fc099941b898e15c3b34a12ac214b637216d74b85046b6fd`.
