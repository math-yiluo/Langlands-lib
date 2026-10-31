# Finite length of restriction to the actual mirabolic subgroup: proof

Author: Worker 11.

This module proves the published proposition
`Langlands.Whittaker.MirabolicFiniteLengthStatement.{uF,uV}` of
[MirabolicFiniteLengthStatement](MirabolicFiniteLengthStatement.md):
Bernstein–Zelevinsky (1976), Corollary 5.22, implication (1) implies (2),
printed p.51. It changes neither that statement nor anything it imports.
The public theorem is

```lean
theorem Langlands.Whittaker.mirabolicFiniteLength :
    MirabolicFiniteLengthStatement.{uF, uV}
```

with independent universes `uF` (field) and `uV` (carrier) and no further
hypothesis: for every prime `p`, `F : PadicField.{uF} p`, supplied topological
data `T`, every `n` (including `n = 0`) and every smooth complex representation
`ρ` of the actual `GL_(n+1)(F)` on a carrier in `Type uV` that has finite
length over the group algebra, the restriction of `ρ` along the inclusion of
the actual mirabolic subgroup `GeneralLinear.mirabolic n F.Carrier` has finite
length over that subgroup's group algebra.

The proof has two parts. The reduction
`Langlands.Whittaker.MirabolicFiniteLength.of_irreducibleCoinvariantFiniteness`
derives the target from the published proposition
`Langlands.Whittaker.IrreducibleCoinvariantFinitenessStatement.{uF,uV}` of
[IrreducibleCoinvariantFinitenessStatement](IrreducibleCoinvariantFinitenessStatement.md),
taken as an explicit hypothesis `h`. That proposition is the finiteness part of
BZ76 Theorem 5.21 (Kazhdan), printed p.51. Let `ρ` be an irreducible smooth
complex representation of the actual `GL_n(F)` on a carrier in `Type uV`, and
`θ` a locally constant character of the actual upper-unipotent subgroup. Then
`h` says that
`Jacquet.Localization.Coinvariants ρ (GeneralLinear.upperUnipotent n F.Carrier) θ`
is finite-dimensional, for every prime `p`, `F : PadicField.{uF} p`, supplied
`T` and `n`. The hypothesis is then discharged by the published theorem
`Langlands.Whittaker.irreducibleCoinvariantFiniteness` of
[IrreducibleCoinvariantFinitenessProof](IrreducibleCoinvariantFinitenessProof.md).

The helper modules are
[MirabolicFiniteLengthCharacters](MirabolicFiniteLengthCharacters.md)
(characters of `F` and `F^n`) and
[MirabolicFiniteLengthDetection](MirabolicFiniteLengthDetection.md)
(detection of nonzero mirabolic representations, BZ76 5.14). All new
declarations live in the namespace `Langlands.Whittaker.MirabolicFiniteLength`.

## Source proof and the implemented route

The source proves (1) implies (3) from 5.21 and the exactness 2.35. Here (3)
is finite dimension of `E_(U,θ)` for all characters `θ` of `U`. It then proves
(3) implies (2): every character of `U` is conjugate under `P` to one of the
`2^(n-1)` characters of `Ω` (coefficients `0` or `1`, see 5.5). The function
`d(π) = ∑_(θ ∈ Ω) dim E_(U,θ)` is additive along chains of `P`-submodules by
2.35, and each nonzero subquotient contributes at least one by 5.14. So every
strict chain has length at most `d(π)`.

The Lean proof follows this outline with three changes.

1. Only the characters in `Ω` are used. Write `θ_S` for the characters
   `simpleCharacter ψ S` of the detection module. Detection already produces
   characters in `Ω`, so no conjugation of arbitrary characters is needed. For
   GL finite length, (3) is proved only for the restrictions of these
   characters.
2. The finite dimension of `E_(U,θ)` for a finite-length GL representation
   uses only right exactness of coinvariants. The proof is by induction on the
   length.
3. Additivity of `d` along chains is replaced by a strictly monotone bounded
   function on the lattice of subrepresentations. That function exists by
   detection and the injectivity half of 2.35.

## Finite length over GL gives finite-dimensional coinvariants

Here `G` is any topological group, `U` a subgroup and `θ : U →* ℂˣ`.

- `isIrreducible_of_forall`: a representation on a nontrivial carrier whose
  only subrepresentations are `⊥` and `⊤` is irreducible in Mathlib's sense
  (`Representation.IsIrreducible`, a simple order on subrepresentations).
- `finiteDimensional_coinvariants_of_repLength_eq U θ hirr n`: let `hirr` say
  that every irreducible smooth representation of `G` on a carrier in
  `Type uV` has finite-dimensional `θ`-coinvariants. Then every smooth
  representation `ρ` with Library length `repLength ρ = n` has
  finite-dimensional `θ`-coinvariants. `repLength` is the module length over
  the group algebra (`Langlands.Representation.Filtration.RepresentationLength`).

  The proof is strong induction on `n`, for all carriers in `Type uV`. A zero
  carrier has zero coinvariants. If there is no subrepresentation other than
  `⊥` and `⊤`, then `ρ` is irreducible and `hirr` applies. Otherwise pick a
  subrepresentation `A` with `A ≠ ⊥` and `A ≠ ⊤`, and let `Q` be the quotient.
  The Library's `repLength_eq_subrepresentation_add_quotient` gives
  `n = repLength A + repLength Q`. Both terms are finite, and both are
  positive by `repLength_eq_zero_iff`, so both are smaller than `n`. `A` and
  `Q` are smooth (`isSmooth_of_injective`, `isSmooth_of_surjective`), so their
  coinvariants are finite-dimensional by induction. The Library's
  `map_range_eq_ker` and `map_surjective` say that
  `A_(U,θ) → ρ_(U,θ) → Q_(U,θ) → 0` is exact, and
  `Module.Finite.of_exact` finishes. This uses no compactness hypothesis on
  `U`.
- `finiteDimensional_coinvariants_of_isFiniteLength`: the same conclusion for
  Mathlib's `IsFiniteLength (MonoidAlgebra ℂ G) ρ.asModule`, which makes the
  module length finite (`Module.length_ne_top_iff`).

## Finite length from finite-dimensional simple-character coinvariants

Here `F : PadicField p` with supplied `T`, whose topology is installed, and
`ψ` is a locally constant character of `F`.

- `isLocallyConstant_selectedSum`: the character `ψ ∘ selectedSum S` of the
  upper-unipotent subgroup of `GL_(n+1)` is locally constant. The sum of the
  selected adjacent entries is continuous (Library `GeneralLinear.entry`), and
  `ψ` is locally constant.
- `isLocallyConstant_simpleCharacter`: so is `θ_S`, by the continuous
  `upperUnipotentContinuousEquiv`.
- `isFiniteLength_of_finiteDimensional T ψ hψ hgen σ hσ hfin`: let `ψ`
  generate the locally constant characters of `F` (`hgen`). Let `σ` be a smooth
  representation of `GeneralLinear.mirabolic n F.Carrier` all of whose `2^n`
  coinvariant spaces `Coinvariants σ U θ_S` are finite-dimensional. Then
  `σ.asModule` has finite length over the group algebra.

Proof. Write `U` for the upper-unipotent subgroup of the mirabolic group. It
is exhausted by compact subgroups by the Library's
`GeneralLinear.Mirabolic.upperUnipotent_isLimitOfCompactSubgroups`.
For a subrepresentation `W` and each `S`, consider the image of `W` in
`Coinvariants σ U θ_S`.

*Separation.* Let `W ≤ W'` have the same images for every `S`; then
`W' ≤ W`. Otherwise the quotient `Q = W' / (W ∩ W')` has a nonzero vector,
and `Q` is smooth. Detection (`exists_relations_ne_top`) gives an `S` whose
relations in `Q` are not everything. Every `y ∈ W'` has the same image as some
`z ∈ W`, so `y - z` lies in the relations of `σ`. By
`mem_relations_of_injective` (injectivity in BZ76 2.35), it lies in the
relations of `W'`. Its image in `Q` is the image of `y`. The Library's
`relations_map_of_surjective` puts that image in the relations of `Q`. Hence
the relations of `Q` are everything, a contradiction.

*Bound.* Let `f W = ∑_S dim (image of W in Coinvariants σ U θ_S)`. Monotonicity
of images and separation make `f` strictly monotone. It is bounded by
`B = ∑_S dim Coinvariants σ U θ_S`. Mathlib's
`Subrepresentation.subrepresentationSubmoduleOrderIso` identifies
subrepresentations with group-algebra submodules of `σ.asModule`. So the
submodule lattice has a strictly monotone map into `Fin (B + 1)`. Both `<` and
`>` are therefore well-founded on it. The module is Artinian and Noetherian,
hence of finite length (`isFiniteLength_iff_isNoetherian_isArtinian`). The
zero representation needs no separate case.

This replaces the source's count `k ≤ d(π)` for a chain
`0 = E₀ ⊊ ⋯ ⊊ E_k = E`: there, each step raises `d` by at least one; here,
each step raises `f` by at least one.

## The reduction to Theorem 5.21

`of_irreducibleCoinvariantFiniteness h` proves
`MirabolicFiniteLengthStatement.{uF,uV}`. Given `p`, `F`, `T`, `n`, `V` and a
smooth `ρ` of finite length over `GL_(n+1)`, the proof installs `T.topology`,
`T.valuativeRel` and `T.localField`. It then proceeds as follows.

1. `exists_generating_character T` supplies a locally constant `ψ` generating
   all locally constant characters of `F`.
2. The restriction `σ = ρ.comp (GeneralLinear.mirabolic n F.Carrier).subtype`
   is smooth by the Library's `isSmooth_comp`, since the subgroup inclusion is
   continuous.
3. For each `S`, `relations_eq_of_surjective` along the Library's
   `GeneralLinear.Mirabolic.upperUnipotentEquiv` identifies the relations of
   `σ` for `θ_S` with those of `ρ` for `ψ ∘ selectedSum S`. The latter
   character of the upper-unipotent subgroup of `GL_(n+1)` is locally
   constant. So `finiteDimensional_coinvariants_of_isFiniteLength` applies,
   with `hirr` given by `h` at rank `n + 1`. The finite dimension is
   transported along `Submodule.quotEquivOfEq`.
4. `isFiniteLength_of_finiteDimensional` concludes.

Thus the step (1) implies (3) of the source is used only for the characters
`ψ ∘ selectedSum S`, and (3) implies (2) is the criterion above. Neither
admissibility nor a nontrivial additive character is assumed, and every
`n`, including `n = 0`, is covered.

## The closing theorem

`Langlands.Whittaker.mirabolicFiniteLength` (in the namespace
`Langlands.Whittaker`, outside the helper namespace) applies
`of_irreducibleCoinvariantFiniteness` to
`irreducibleCoinvariantFiniteness.{uF,uV}`, the published proof of BZ76
Theorem 5.21's finiteness assertion at the same universes. The hypothesis
`h` of the reduction has exactly the type of that theorem, so the composite
has exactly the type `MirabolicFiniteLengthStatement.{uF,uV}`, with no added
hypothesis and only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Sources

I. N. Bernshtein and A. V. Zelevinskii, *Representations of the group GL(n,F)
where F is a non-Archimedean local field*, Russian Mathematical Surveys 31:3
(1976), 1–68. Registered source `bernstein-zelevinsky-1976-representations-gln`,
Central-Library PDF SHA256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`; printed
pages equal one-based PDF pages. Read: §§2.30–2.35 pp.24–25, §§5.1–5.5
pp.44–45, §5.14 p.48, Theorem 5.21 and Corollaries 5.22 and 5.23 pp.51–52.
No matching erratum note was found.
