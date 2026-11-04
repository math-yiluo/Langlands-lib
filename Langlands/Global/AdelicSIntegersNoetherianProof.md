# Arithmetic Noetherianity from one-dimensional overrings

Authors: Worker 208 (Lean proof and first Markdown draft), Worker 972
(Markdown revision and submission).

The theorem `Langlands.Global.adelicSIntegersNoetherian` proves
`Langlands.Global.AdelicSIntegersNoetherianStatement.{u}` in an
arbitrary common universe `u`. Both clauses are proved for every finite
`S`, including empty `S`. The proof uses the actual published S-integer
rings with their original operations and adds no hypotheses: no
separability, perfectness, finiteness of the constant field, nonempty
`S`, affine model, or Noetherianity or dimension premise. The provenance
of the target is described in the statement's Markdown,
`Langlands/Global/AdelicSIntegersNoetherianStatement.md`.

Both clauses rest on the published Krull–Akizuki theorem
`Subalgebra.isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite`,
ported from the Anthropic FLT formalization. Let `A` be a Noetherian
domain with `Ring.KrullDimLE 1 A` and fraction field `K`, and let `L` be
a finite extension of `K`. Then every `A`-subalgebra `B` of `L` is
Noetherian and satisfies `Ring.DimensionLEOne B`. The proof uses only
these two conjuncts; the theorem's finite-length conjunct is discarded.

## Subalgebras of a function field

The private lemma `functionField_subalgebra_noetherian` takes fields
`k` and `F` in universe `u` with `FunctionField k F` and the compatible
`RatFunc k`-structure. It proves that every `B : Subalgebra k F`
satisfies `IsNoetherianRing B ∧ Ring.DimensionLEOne B`. The proof splits
on whether some element of `B` is transcendental over `k`.

*Transcendental case.* Choose `s ∈ B` transcendental over `k`, and let
`R = Algebra.adjoin k {s}`, that is `k[s]`. Then `R ≤ B`, because `B` is
a `k`-subalgebra containing `s`. Opening the scope
`AlgebraicCurve.CurveModel` (from the published
`Langlands.AnthropicFLT.Definitions.Def_JacJ1_ChartAlgebra`) makes the
instance `isPrincipalIdealRing_adjoin_singleton` available. It shows
that `R` is a principal ideal ring, as the image of `k[X]` under
evaluation at `s`. As a subring of a field, `R` is a domain. Lean
therefore finds the instances `IsNoetherianRing R` and
`Ring.KrullDimLE 1 R`. Mathlib's scoped
`IntermediateField.algebraAdjoinAdjoin` instances give the algebra
`R → k⟮s⟯` and `IsFractionRing R k⟮s⟯`.
`FunctionField.finiteDimensional_of_adjoin_transcendental` makes `F`
finite-dimensional over `k⟮s⟯`. This Mathlib result needs no
separability premise. The proof then views the underlying subring of
`B` as an `R`-subalgebra `B'` of `F`. Only the proof of
`algebraMap_mem'` is new, so `B'` has the same carrier and ring
operations as `B`. The Krull–Akizuki theorem with `A = R`,
`K = k⟮s⟯` and `L = F`, applied to `B'`, gives both properties for `B`.

*Algebraic case.* Suppose no element of `B` is transcendental over `k`.
Then every element of `B` is algebraic over `k`, by
`Subalgebra.isAlgebraic_iff_isAlgebraic_val`, so `B` is an algebraic
and hence integral `k`-algebra. `B` is a domain, being a subring of `F`,
so `isField_of_isIntegral_of_isField'` makes `B` a field. A field is
Noetherian and has dimension at most one, which settles this case. No
assumption on `k` is needed, and the case split uses no information
about `S`.

## The two clauses

*Function fields.* For `k`, `F` and `S` as in
`CurvePlaceSIntegersNoetherianStatement`, the actual subring
`curvePlaceSIntegers k F S` contains the image of `k`. The published
`curvePlaceSIntegersConstants k F S` witnesses this by restricting the
original inclusion `algebraMap k F`. The proof records this as a
`Subalgebra k F` with the same carrier and applies the lemma above. The
result is a statement about the same type with the same ring structure,
so it closes the clause for `curvePlaceSIntegers k F S` itself.

*Number fields.* Let `K` be a number field and `S` a finite set of
finite places. Here `FinitePlace K` is the Library abbreviation for
`IsDedekindDomain.HeightOneSpectrum (𝓞 K)`. Mathlib's `Set.integer`
makes `(S : Set (FinitePlace K)).integer K` a `Subalgebra (𝓞 K) K`.
The ring `𝓞 K` is a Dedekind domain with fraction field `K`, and `K`
is finite over itself. The Krull–Akizuki theorem with `A = 𝓞 K` and
`K = L = K` therefore applies to the actual ring directly.

## Scope

This proof supplies only the named arithmetic target. It does not
identify an affine curve model, prove finite generation over the
constants, identify the S-integer spectrum or fraction field, or
establish any geometric or topological comparison. These and all other
obligations of parent task `886bf565-95e9-4dc6-8a9d-73284a523668`
remain with that task.
