# Cocenters of split-torus centralizers in simply connected groups are induced (proof)

Author: Worker 4721.

`Langlands.GroupScheme.splitTorusCentralizerCocenterInduced` proves exactly
the public proposition
`Langlands.GroupScheme.SplitTorusCentralizerCocenterInducedStatement.{u}`
of module `Langlands.GroupScheme.Rational.SplitTorusCentralizerCocenterStatement`.
The universe `u` is arbitrary, and the theorem has no hypotheses of its own.

## What is proved

Let `k : Type u` be any field, with no perfectness, separability or
characteristic assumption. Let `G` be a group over `k` with
`IsSimplyConnected G`; `G` is not assumed quasi-split. Let `a : A ⟶ G` be a
split subtorus and `j : M ⟶ G` a representative of its centralizer
`torusCentralizer a`. Let `d : D ⟶ M` exhibit the scheme-theoretic derived
subgroup of `M`. Let `q : M ⟶ D'` be a homomorphism to a commutative group
scheme `D'` such that `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q`
holds. Then `D'` is an induced torus in the sense of `IsInducedTorus`
(KP Definition 2.5.1). That is, there are a finite Galois extension `E/k` in
`Type u` splitting `D'` and a `ℤ`-basis of `X^*(D'_E)` that every element of
`Gal(E/k)` permutes.

## Implemented proof

The proof is a single application of the published conditional theorem
`splitTorusCentralizerCocenterInduced_of_inputs` (module
`Langlands.GroupScheme.Rational.SplitTorusCentralizerCocenterAssembly`).
That theorem derives the target from the conjunction
`SplitTorusCentralizerCocenterInducedInputsStatement.{u}` of five structural
propositions. This module supplies each conjunct from a published
unconditional Library theorem at the same universe `u`:

| Conjunct | Library theorem | Module |
| --- | --- | --- |
| `DynamicCentralizerReductiveStatement` | `dynamicCentralizerReductive` | `Langlands.GroupScheme.Dynamic.CentralizerReductiveProof` |
| `CocenterQuotientExistenceStatement` | `cocenterQuotientExistence` | `Langlands.GroupScheme.Derived.CocenterQuotientProof` |
| `IsSimplyConnectedFieldExtensionStatement` | `isSimplyConnectedFieldExtension` | `Langlands.GroupScheme.SimplyConnected.SimplyConnectedFieldExtensionProof` |
| `SplitSimplyConnectedCorootSpanStatement` | `splitSimplyConnectedCorootSpan` | `Langlands.GroupScheme.SimplyConnected.SplitNecessity` |
| `SplitTorusCentralizerCocenterRootModelStatement` | `splitTorusCentralizerCocenterRootModel` | `Langlands.GroupScheme.Rational.LeviCocenterRootModelProof` |

## What the imported assembly does

The assembly's paired Markdown documents it in full. For a reader of this proof, the
argument runs as follows for the supplied `k`, `G`, `a`, `j`, `d`, `D'` and `q`.

1. The first input, through `splitTorusCentralizerReductive_of_dynamic`,
   shows that the supplied centralizer `M` is connected reductive.
2. The second input, through `suppliedCocenterTorus_of_existence`, shows that
   the supplied quotient `D'` is a torus. This holds for the given `D'`, not
   only for some constructed quotient.
3. The fifth input supplies a maximal `k`-torus `t : T ⟶ M` and a finite
   Galois extension `E/k` splitting `T` and `D'`, with `(t ≫ j)_E` a maximal
   torus of `G_E`. It also supplies a finite reduced root datum `P` that is
   the actual root datum of `G_E` relative to `(t ≫ j)_E`, a base `B`, a
   subset `s` of the simple roots, and `CocenterRootDescentData`. These data
   say three things. Pullback of characters along `t ≫ q` is injective, and
   its image is the annihilator of the simple coroots in `s`. Integral
   corrections of the Galois actions preserve the root pairing and permute
   the simple coroots, preserving `s`. These corrections fix the pullback
   image.
4. The third input shows that `G_E` is simply connected. The fourth input,
   applied to the split maximal torus `(t ≫ j)_E` and the root datum `P`,
   shows that the coroots span `X_*(T_E)` over `ℤ`.
5. `isInducedTorus_of_cocenterRootDescent` concludes. The simple coroots then
   form a `ℤ`-basis of `X_*(T_E)`, and the fundamental weights form the dual
   basis of `X^*(T_E)`. The pullback image is spanned by the fundamental
   weights outside `s`. The corrected Galois action permutes these weights,
   and on the pullback image it agrees with the ordinary action. Pulling these
   weights back to `X^*(D'_E)` gives the basis that `IsInducedTorus D'` requires.

So the proof follows the fundamental-weight route of the statement's
Markdown, in its section "Why it should hold without quasi-splitness". The
five published theorems supply what its section "What a proof along this
route must establish" lists, in the following form:

- connected reductivity of `M`, and the torus property and splitting of `D'`;
- the identification of the pullback image in `X^*(T_E)` with the characters
  vanishing on the coroots of the simple roots in `s`;
- the simple connectivity of `G_E` and the integral coroot span;
- in place of an explicit `k`-parabolic and Weyl elements in `W_M`, the
  correction maps of `CocenterRootDescentData`. Composed with the ordinary
  Galois actions, they preserve the root pairing, permute the simple coroots
  and preserve `s`, and they fix the pullback image.

## Provenance

This proof is a composition of published Library results by their Lean names.
It transcribes no further literature argument. The provenance of the statement
(Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*, 2023, Definition 2.5.1
and the proof of Lemma 2.6.27) is recorded in the statement's own Markdown.

## Check

`lean_check` in environment `bb168ec3-1031-46d9-816b-5c2ed7bbe1a6` compiled
this module with no errors or warnings. For
`splitTorusCentralizerCocenterInduced` it reported only the axioms `propext`,
`Classical.choice` and `Quot.sound`.
