# Picard vanishing after inverting an element of a regular local ring

The theorem
`Langlands.CommutativeAlgebra.regularLocalAwayPicard` proves exactly the
Library proposition `RegularLocalAwayPicardStatement.{u}`:

```lean
∀ (R : Type u) [CommRing R], IsRegularLocalRing R →
  ∀ f : R, Subsingleton (CommRing.Pic (Localization.Away f))
```

The universe `u` is arbitrary. There are no additional hypotheses on the
regular local ring or on `f`; zero and units are included. The target
proposition and its imports are unchanged.

## Implemented proof

The proof introduces `R`, its regularity premise `hR`, and `f`. It installs
`hR` as the regular-local instance, which supplies Noetherianity and localness.
The imported theorem `regularLocalFiniteProjectiveDimension`, from
`RegularLocalFiniteProjectiveDimensionProof`, supplies a natural
projective-dimension bound for every finite `R`-module in `Type u`.

The theorem then applies
`subsingleton_pic_localization_of_finite_projectiveDimension` to this
homological input and `Submonoid.powers f`. Mathlib's `Localization.Away f`
is definitionally `Localization (Submonoid.powers f)`, so the resulting
subsingleton instance has exactly the required type.

The supporting module
`LocalizationPicardOfFiniteProjectiveDimension` proves its localization
criterion as follows. By `CommRing.Pic.subsingleton_iff`, it suffices to show
that every invertible module `N` over the localization is free. Such a
module is finite and projective. The helper
`exists_fg_submodule_isLocalizedModule`, from
`FiniteModuleLocalizationDescent`, realizes `N` as the localization of a
finite `R`-submodule `K`. The homological input supplies a finite
projective-dimension bound for `K`. The theorem
`isStablyFree_of_isLocalizedModule_of_hasProjectiveDimensionLE`, from
`FiniteProjectiveDimensionLocalization`, makes `N` stably free. Finally,
Mathlib's `Module.free_of_isStablyFree_of_invertible` makes it free.

The stable-freeness helper inducts on the projective-dimension bound.
At zero, a finite projective module over the local ring is free. At a
successor, a finite free presentation has finite kernel of lower
projective dimension. Localizing gives a short exact sequence that splits
because its quotient is projective. The induction hypothesis and a
permutation of finite free complements give stable freeness of the quotient.
The descent helper takes the `R`-span of a finite set of localized
generators and clears denominators.

Worker 362 authored the unchanged supporting Lean/Markdown pairs
`FiniteModuleLocalizationDescent`, `FiniteProjectiveDimensionLocalization`,
and `LocalizationPicardOfFiniteProjectiveDimension`. Worker 152 authored
this final specialization. The regular-local finite-projective-dimension
theorem is imported from the Library rather than proved again here.

## Provenance and independence

The target is Stacks Project Lemma 15.123.1,
[Tag 0AFZ](https://stacks.math.columbia.edu/tag/0AFZ), retained in registered
source `stacks-regular-local-ufd-2026-10-29`, file `0AFZ.html` (directory
SHA256 `49b665ff41945fd15cc966fe79e70688059509c0487cc27f32167fe1e1baed31`).
Its corrected source proof computes in `K_0(R_f)` and applies the
determinant. The implemented proof follows the same descent and finite
homological input, using stable freeness and invertibility for the final
step.

The helper results are internal algebraic derivations from Mathlib's
localization, finite-module, projective-dimension and stable-freeness APIs.
The imported regular-local finite-projective-dimension proof uses the
Library's regular-local domain theorem and Mathlib. The complete proof
uses no regular-local factoriality theorem or geometric extension result.
