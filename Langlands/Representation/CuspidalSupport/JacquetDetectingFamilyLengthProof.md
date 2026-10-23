# Finite detecting-family Jacquet length criterion: proof

Author: Worker 325.

`Langlands.CuspidalSupport.jacquetDetectingFamilyLength.{uF,uV}` proves the
published proposition
`Langlands.CuspidalSupport.JacquetDetectingFamilyLengthTheorem.{uF,uV}`
without any additional premises. The field universe `uF` and representation
carrier universe `uV` are independent. The statement pair and all its imports
are preserved.

For an actual smooth complex representation `A` of `GL_n(F)`, a finite set `s`
of block shapes, and natural bounds `b`, the hypotheses are precisely the
published composition-length bound for each actual normalized Jacquet object
`J_C(A)`, for `C ∈ s`, and detection of each nonzero actual smooth subquotient
of `A` by some `J_C`. The conclusions are both finite length of the actual
group-algebra module `A.representation.asModule` and an actual composition
series of length at most `∑ C ∈ s, b C`.

## Actual successive subquotients

The helper namespace `JacquetDetectingFamilyLengthProof` starts with two
constructions for invariant subspaces `S` and `U` of `A`:

- `lower A S U` is the inverse image of `S` in the carrier of `U`, with the
  restricted action. Its underlying submodule is
  `S.toSubmodule.comap U.toSubmodule.subtype`.
- `inclusion A S U h`, for `h : S ≤ U`, is the actual inclusion intertwiner
  from the smooth representation on `S` into that on `U`.

`inclusion_exact` proves that the inclusion's range is the kernel of the
actual quotient map by `lower A S U`. The proof uses representatives and
`Submodule.Quotient.mk_eq_zero`. `quotient_nontrivial` proves that this
quotient is nonzero when `S < U`: choose a vector in `U` outside `S`, whose
quotient class cannot vanish. Thus
`SmoothRep.subquotient A U (lower A S U)` is a nonzero actual subquotient of
`A`; its subquotient witness uses the identity isomorphism. All of these
objects have the original carrier universe `uV`, so the detection hypothesis
applies directly.

## Jacquet length calculations

`jacquet_injective` uses the published injectivity of smooth coinvariant maps
for the actual block unipotent radical. Its hypotheses are supplied by
`Parabolic.unipotentFiniteContainment` and `Parabolic.isSmooth_radical`.
The normalized Jacquet map has the same underlying linear map as that
coinvariant map, by
`T.normalizedJacquetMap_toLinearMap_eq_coinvariantsMap`.

`jacquet_length_le` turns the resulting intertwiner into a linear map over
the Levi group algebra with `IntertwiningMap.equivLinearMapAsModule` and
applies Mathlib's `Module.length_le_of_injective`. The length used throughout
is the published `repLength`, namely Mathlib's module length of the actual
representation's group-algebra module, with values in `ℕ∞`.

`jacquet_length_step` applies `T.normalizedJacquetMap_exact` to the inclusion
and actual successive quotient map. The upper smooth subrepresentation
supplies smoothness, and the preceding helper supplies range–kernel equality.
The published `repLength_eq_add_of_exact` then gives

`length J_C(U) = length J_C(S) + length J_C(U/S)`.

No replacement functor or assumed exactness package is introduced.

## A bounded strictly increasing natural measure

The main proof first turns each assumed actual composition series for
`J_C(A)` into its numerical module-length bound, using
`repLength_eq_of_hasSimpleFactors`. Injectivity of `J_C(S) → J_C(A)` then
bounds `length J_C(S)` by `b C` for every invariant subspace `S` and `C ∈ s`.
In particular, these lengths are finite. The proof defines the natural number

`measure(S) = ∑ C ∈ s, (length J_C(S)).toNat`.

It is bounded by `∑ C ∈ s, b C`, and every summand is monotone in `S`.
Whenever `S < U`, detection supplies `C ∈ s` with nonzero `J_C(U/S)`.
`repLength_pos_iff` makes its length positive. Additivity and finiteness of
`length J_C(S)` imply a strict increase in that summand. The conversion to
natural numbers is justified by `ENat.natCast_toNat` for both finite lengths;
`Finset.sum_lt_sum` therefore proves `StrictMono measure`.

For any strict chain `c : Fin (m + 1) → Subrepresentation A.representation`,
its measure values form a strict natural-number `LTSeries`. Mathlib's
`head_add_length_le_nat` gives

`measure(c 0) + m ≤ measure(c (Fin.last m)) ≤ ∑ C ∈ s, b C`.

Consequently `m ≤ ∑ C ∈ s, b C`. The published bounded-chain criterion,
implemented by `LengthCriterionProof.hasCompositionLengthAtMost_of_bound`,
produces the required actual composition series. The second clause of
`objectCompositionLengthCriterion` gives group-algebra finite length from
that series.

## Scope and provenance

The proof makes no positivity assumption on `n`, no nonemptiness assumption
on `s`, and no positivity assumption on any bound. Empty families, zero
bounds, zero representations, and rank zero use the same argument. For an
empty family, any strict inclusion would yield a nonzero successive quotient
and hence contradict detection. No admissibility, cuspidality,
irreducibility, finite-dimensionality, or prior finite-length assumption is
placed on `A`.

This is an internal algebraic proof of the Library's existing criterion.
The statement's historical motivation is Bernstein–Zelevinsky (1977),
§2.14(2), as documented in the unchanged
`JacquetDetectingFamilyLengthStatement.md`; this proof does not assert that
the arbitrary-representation finite-family formulation is a verbatim theorem
there. Its implementation combines the published normalized Jacquet
exactness, the published representation module-length calculations, and the
published bounded-chain criterion. It does not use the cuspidal-induction
length theorem, an induction association theorem, or a pending proof draft.
