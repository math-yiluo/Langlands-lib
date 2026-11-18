# Restricted B7 for the Harris branches

`RestrictedCyclicWeakBaseChangeComplexPlaceStatement` is a proposition
definition. It states the restricted cuspidal clauses (1)r and (2)r of B7:
complex-place parameters of unitary cuspidal cyclic weak transfers that are
supercuspidal at an auxiliary conjugate pair. It is a named, unproved input to
the Harris branch reductions. Nothing is proved here. Its universe parameters,
in order, are `uF,uE,uV,uW`: `F` lives in `uF`, `E` in `uE`, and `uV`, `uW`
are the universes of the spectral presentations over `F` and over `E`. The
same `uV`, `uW` are used in the weak-transfer relations and in the
supercuspidality conditions.

## Fields, extension and auxiliary pair

`F` and `E` are actual number fields, and `E` is an `F`-algebra. `F` is a CM
field (`NumberField.IsCMField F`). A CM field is totally complex, so every
infinite place of `F` is complex. For this reason there is no separate
totally complex form. No CM structure on `E` is assumed. The extension `E/F`
is Galois (`IsGalois F E`), its Galois group `E ≃ₐ[F] E` is cyclic, and
`Module.finrank F E` is prime. Both additive adele quotients `𝔸_F/F` and
`𝔸_E/E` are compact. These are true facts, supplied as instance hypotheses
because the Library's cuspidal-class vocabulary requires them.

Next come an actual finite place `v₀` of `F` and its complex conjugate
`Harris.conjPlace F v₀`, which is the image of `v₀` under complex conjugation
of the CM field `F`. They are assumed distinct. The hypotheses
`∀ w', w' = w₀` and `∀ w', w' = wc` say that `w₀` is the unique place of `E`
above `v₀` and `wc` the unique place above `Harris.conjPlace F v₀`. These data
come before both clauses. They only restrict which global classes are
considered: the conclusions concern every complex place of `F`.

## Hypotheses common to both clauses

In both clauses `S` is an actual cuspidal realization over `F` and `T` an
actual cuspidal realization over `E`. Both have unitary central character, in
the sense of `ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter`:
there is a continuous idele-class character of absolute value one that is the
central character of the realization. This is the convention of the Library's
cyclic transfer statements (`CyclicTransferStatement`). Comparing it with
unitarity of the representation is left to later proofs.

Both classes are supercuspidal at the auxiliary pair. `S.isoClass` has
supercuspidal components at `v₀` and at `Harris.conjPlace F v₀`, and
`T.isoClass` at `w₀.1` and at `wc.1`. The predicate is the published
`IsoClass.HasSupercuspidalComponent`: some genuine spectral presentation of a
representative has an irreducible admissible local component at that place,
and its canonical `p`-adic class is supercuspidal. It is not an extra label.

There is no regular-algebraicity hypothesis and no conjugate-self-duality
hypothesis, upstairs or downstairs.

## Clause (1)r: base change

Both realizations have the same index `r`. In the Library's convention for
`CuspidalOperatorRealization F r` this means matrix rank `r+1`. The clause
assumes `IsoClass.IsWeakBaseChangeOf T.isoClass S.isoClass`: `T.isoClass` is
a weak base change of `S.isoClass`. That relation is witnessed by genuine
spectral presentations of both classes whose spectral systems satisfy the
arithmetic weak base-change relation at unramified finite places.

The conclusion is a biconditional. For every complex place `v` of `F`, every
actual place `w` of `E` above `v`, and every list
`ds : List ComplexCharacterData`:

- `S.isoClass` has the complex-place parameter `ds` at `v` if and only if
- `T.isoClass` has the parameter `complexPlaceParameterTransport v w ds` at
  the complex place `complexPlaceAbove v w`.

`complexPlaceAbove v w` is the place `w` itself, packaged with the proof that
it is complex.

The biconditional is what permits descent. Suppose the parameter of
`T.isoClass` at `w` is known for a list of the form
`complexPlaceParameterTransport v w ds`. Then the reverse direction gives the
parameter `ds` of `S.isoClass` at `v`. The transport either leaves a list
unchanged or conjugates every entry, so applying it twice returns the
original list. Hence any known upstairs list has this form, with `ds` its own
transport. This elementary involutivity of the transport is not proved in
this module.

The clause states compatibility only for supplied lists. It does not assert
that every class has a parameter at `v`.

## Clause (2)r: automorphic induction

`S` has index `r` and `T` has index `m`, so their matrix ranks are `r+1` and
`m+1`. The clause makes two assumptions:

1. **Galois non-stability, stated without a generator.** For every
   automorphism `σ : E ≃ₐ[F] E` with `σ ≠ 1`, `T.isoClass` is not
   `IsGaloisStable σ`. Here `IsGaloisStable σ` means isomorphic to its
   arithmetic transport along `σ`. No generator of the cyclic group is
   chosen. In a cyclic group of prime order this condition is equivalent to
   non-stability under the nontrivial powers of one generator. That
   conversion is not used or proved here.
2. **Weak induction.** `IsoClass.IsWeakInductionOf S.isoClass T.isoClass`:
   `S.isoClass` is weakly induced from `T.isoClass`. The relation is again
   witnessed by genuine spectral presentations, and it already carries the
   rank equation `r+1 = (m+1)·[E:F]`.

The conclusion quantifies over:

- every complex place `v` of `F`;
- every natural number `d` with a genuine equivalence
  `e : Fin d ≃ InfinitePlacesAbove E v.1`, so that every actual place above
  `v` is listed exactly once;
- every family `ds` of lists indexed by the places above `v`, such that
  `T.isoClass` has the literal parameter `ds w` at `complexPlaceAbove v w` for
  every `w`.

For these data it concludes that `S.isoClass` has the literal parameter
`complexPlaceLanglandsSum v e ds` at `v`. This list is formed in three steps:

- transport each `ds (e i)` to the coordinates of `v`;
- list the transported lists in the order `i = 0, …, d-1`;
- concatenate them.

The concatenation keeps every entry, so the multiplicities of characters
within each list and across places are all retained. The conclusion is
asserted for every enumeration `e`, so it asserts the literal parameter in
each resulting order of the places. The order of the entries within each
`ds w` is the supplied one.

This is the induced infinity type. The archimedean component of the class
induced from `T` is the Langlands sum of the components of `T` at all places
above `v`, read in the coordinates of `v`. Clause (2)r supplies that formula,
with no regularity or algebraicity input.

## Parameter vocabulary and normalization

`IsoClass.HasComplexPlaceParameter` is the Library's literal predicate. A list
`ds` of `n` complex character data (`n = r+1` or `m+1`) is a parameter when
there is an injective `ℂ`-linear map from the `U(n)`-finite functions of the
standard module of `ds` into the realization's space. This map must
intertwine right translation by `U(n)` with the compact action at the place,
and right derivatives with the Lie action at the place. Both actions use the
place's selected identification of the completion with `ℂ`. The predicate is
stated for the list in its given order. No closure under permutation is built
into it.

The transport uses the actual selected completion coordinates.
`complexPlaceParameterTransport v w ds` is `ds` when the selected embedding of
`w`, restricted to `F`, equals the selected embedding of `v`. Otherwise it is
`ds.map ComplexCharacterData.conj`. `ComplexCharacterData.conj` precomposes
the character with complex conjugation, negates the weight and keeps the
exponent. No normalization shift is introduced. The parameters are therefore
in the same vocabulary and normalization as canonical B7 and its separate
archimedean bridge.

Infinitesimal characters, the existence of parameters, and regular
algebraicity are not asserted. They belong to that separate archimedean
bridge.

The conclusion formulas of (1)r and (2)r are literally those of clauses (1)
and (2) of canonical B7 (Task 7479, `abcbb7a8-e133-45df-b7cf-6413542ec954`).
The hypotheses are stronger in five ways:

- the CM base;
- the auxiliary pair with unique places above it;
- unitary central character on both sides, whereas canonical B7 asks it only
  of `S` in (1) and only of `T` in (2);
- supercuspidality of both classes at the pair;
- no isobaric clause (3).

## Sources and provenance

The design source is the registered operator plan
`operator-external-inputs-plan-2026-11-16` (`external-inputs-plan.tex`):

- Section 2.2, B7 (line 199);
- Section 4.6, the interface paragraphs, where B7 is a consequence of
  III.5.1 at a split place (line 737); and the recommendation (lines
  768–770) to restrict B1–B3 and III.5.1 to the representations that occur
  (cuspidal, regular algebraic, supercuspidal at a pair of conjugate places
  with a single prime above each) and to state B7 beside them;
- Section 4.8, the paragraph "The infinity type" (lines 910–911).

The restriction to classes supercuspidal at the auxiliary conjugate pair is
point 4(ii) of the operator ruling
`/home/taskhub/pilot/correspondence/afc4eb775dc157d6807bbc17caa2b02b.md`. It
is authorized in this form by point (b) of the operator's R2 ruling,
`/home/taskhub/pilot/correspondence/a79e2e832569567a8582b3c994f2fc1b.md`.
That point drops the plan's regular-algebraicity condition: it requires only
unitary cuspidal classes that are supercuspidal at the auxiliary conjugate
pair.

The original global source is `arthur-clozel-1989-base-change`, Chapter III:

- Definition 1.2 (strong base change lift: at every finite or infinite
  `w | v`, `Π_w` is a base change lift of `π_v`), printed p.199 / PDF p.213;
- Definition 4.1 (representations induced from unitary cuspidal
  representations), printed p.202 / PDF p.216;
- Theorem 4.2(b), (c), (e) (the weak lift of a self-twisted cuspidal `π` is
  `Π₁ × Π₁^σ × ⋯ × Π₁^{σ^{ℓ-1}}` with `Π₁` not `σ`-stable; a representation
  induced from cuspidal ones has a unique lift induced from cuspidal ones;
  such a product lifts a unique cuspidal `π`), printed p.202 / PDF p.216;
- Theorem 5.1 (a weak lift between representations induced from cuspidal
  ones is a strong lift), printed pp.212–213 / PDF pp.226–227.

At a complex place `v`, every place `w` above `v` has `E_w = F_v = ℂ`, up to
the choice of coordinates, so local base change at `v` is the split case.
Theorem 5.1 then identifies `T_w` with `S_v` in case (1)r. In case (2)r it
identifies each component at `w` of the lift `T × T^σ × ⋯` with `S_v`. That
component is the sum of the components of `T` at all places above `v`.

The displayed proposition is a restricted, derived parameter consequence of
these results, written in the Library's vocabulary. It is not a verbatim
transcription of III.5.1, and it is not a proof of strong lifting.
Expressing local components through literal standard-module parameters in
selected coordinates is an internal comparison, and it is not proved here.

## Relation to the restricted complex-place premise and other targets

The intended later route (Task 7340) derives this statement from a separate
restricted complex-place III.5.1 premise without algebraicity, stated in
Task 7553 (`7c6af0ac-5d10-471f-85bd-c42b84dfdbc3`). That premise uses
aggregate isobaric parameters on both sides. Passing from it to the literal
formulas here needs four further comparisons, all unproved obligations of the
later derivation:

- **Singleton comparison.** The aggregate predicate of a singleton isobaric
  datum is the permutation closure of the literal predicate: it gives a
  literal list `ds'` with `ds.Perm ds'`. It must not be identified with the
  literal predicate at the same list `ds`.
- **Parameter-order comparison.**
- **Weak-transfer comparison.** This compares the cuspidal and isobaric weak
  base-change relations on singletons, and unitary central character with
  isobaric unitarity.
- **Orbit-induction comparison.** The isobaric sum of the Galois conjugates of
  `T` is a weak base change of a class weakly induced from `T`, including at
  inert unramified places, and the transported Langlands sum must match.

None of these comparisons is proved by defining either proposition.

Task 7465 (`6cf9cf58-e349-4b29-89cf-1d33171cb458`) assumes a regular-algebraic
downstairs source and concludes finite-place chosen-map compatibility. It does
not imply this statement, and it is not changed. Canonical B7 (Task 7479),
including its third clause, and the original Harris/cohomological fallback
also remain unchanged.
