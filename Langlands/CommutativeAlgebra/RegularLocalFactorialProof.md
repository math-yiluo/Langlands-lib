# Regular local rings are unique factorization domains

`Langlands.CommutativeAlgebra.regularLocalFactorial.{u}` proves exactly
`Langlands.CommutativeAlgebra.RegularLocalFactorialStatement.{u}`:

```lean
∀ (R : Type u) [CommRing R],
  IsRegularLocalRing R → UniqueFactorizationMonoid R
```

The universe is arbitrary. There are no additional outer hypotheses or
restrictions on dimension, characteristic, residue field, completeness,
henselianity or excellence. Mathlib's regular-local hypothesis includes
Noetherianity and localness. The imported `regularLocalDomain` theorem supplies
the domain property within the proof.

The final theorem supplies the two inputs to
`RegularLocalFactorial.regularLocalFactorial_of_localizations_of_awayPicard`
from the published Library: `regularLocalLocalizations` in
`Langlands.CommutativeAlgebra.RegularLocalLocalizationsProof` gives regularity
at every prime, and `regularLocalAwayPicard` in
`Langlands.CommutativeAlgebra.RegularLocalAwayPicardProof` gives a subsingleton
Picard group after inverting any one element. Both are unconditional results
in arbitrary universe. Neither is left as an assumption of the final theorem.
The target statement and its imports are preserved.

## Ideal and local-to-global arguments

The supporting lemmas lie in
`Langlands.CommutativeAlgebra.RegularLocalFactorial`. For any ideal `I` and
linear functional `f` on `I`, applying `f` to `xy = yx` shows
`f(x)y = f(y)x`. Thus the canonical tensor-to-endomorphism map on `I` acts by
the scalar given by contraction. For a nonzero finite projective ideal in a
domain, the tensor-to-endomorphism map is bijective. Its injectivity implies
contraction is injective. A tensor mapping to the identity has contraction one:
evaluate at a nonzero ideal element and cancel that element. Contraction is
therefore also surjective, proving that `I` is an invertible module. A trivial
Picard group makes `I` free; the rank-one equivalence with `R` supplies a
principal generator. The zero ideal is handled separately.

A principal ideal in a domain is projective. A nonzero principal ideal is
isomorphic to `R` by multiplication by a generator, while the zero ideal is a
zero module. For a finitely presented ideal whose localizations at maximal
ideals are principal, Mathlib's projectivity-localization theorem supplies
global projectivity. Over a Noetherian domain with trivial Picard group, these
facts make every such locally principal ideal principal.

Consequently, a Noetherian domain with trivial Picard group and factorial
maximal stalks is factorial. For a height-one prime `I` and a maximal ideal
`P`, if `I ≤ P`, its image in `R_P` remains a height-one prime, hence is
principal by factoriality. Otherwise its image is the unit ideal. Thus `I` is
locally principal and has a global generator by the preceding argument.
Mathlib's height-one-prime criterion concludes unique factorization.

## Dimension induction

The induction is on the minimal number `n` of generators of the maximal ideal
of a regular local ring `R`; regularity identifies this number with Krull
dimension. The imported elementary tools give a principal ideal ring for
`n ≤ 1`. Otherwise choose a prime parameter `x` in the maximal ideal but
outside its square. The domain property and primality ensure that `R[1/x]`
is a domain. The published Picard theorem supplies its trivial Picard group.

At a maximal ideal `P` of `R[1/x]`, the contracted prime `q` of `R` omits `x`.
Since `x` lies in the maximal ideal of `R`, this contraction is strictly
smaller than that maximal ideal and has strictly smaller height. The published
localization theorem makes `R_q` regular local. Its embedding dimension equals
its height, so strong induction makes `R_q` factorial. The iterated-localization
isomorphism identifies `R_q` with the stalk of `R[1/x]` at `P`. The preceding
local-to-global criterion makes `R[1/x]` factorial. Finally Mathlib's
`UniqueFactorizationMonoid.iff_localizationAway_of_prime` descends unique
factorization along inversion of the prime element `x` to `R`.

## Provenance and dependencies

The source result and dimension-induction route are Stacks Project
Lemma 15.123.2, [Tag 0AG0](https://stacks.math.columbia.edu/tag/0AG0).
The retained original `0AG0.html` and section `0FJH.html`, including the proofs
and comments, were read in registered source
`stacks-regular-local-ufd-2026-10-29`, directory SHA-256
`49b665ff41945fd15cc966fe79e70688059509c0487cc27f32167fe1e1baed31`.
The two section comments concern proposed power-series additions and do not
correct this lemma. Its Picard input is Lemma 15.123.1,
[Tag 0AFZ](https://stacks.math.columbia.edu/tag/0AFZ); the retained source
includes the correction placing its K-theory argument in `K₀(R_f)`.
The implemented proof uses the published Picard theorem rather than carrying
out a K-theory argument here. Its regularity input is the second sentence of
Lemma 10.110.6, [Tag 0AFS](https://stacks.math.columbia.edu/tag/0AFS).

Worker 669 authored `RegularLocalFactorialTools`, which is included as the
supporting module. Worker 413 authored the ideal lemmas, dimension induction
and final assembly here. The tensor characterization of invertible ideals
and its use with local projectivity are internal derived implementations
using Mathlib. The localization and Picard results are imported by their
published Lean names; their own proof modules describe their homological
arguments. No geometric or valuative-extension conclusion, or result
depending on such a conclusion, enters this proof.
