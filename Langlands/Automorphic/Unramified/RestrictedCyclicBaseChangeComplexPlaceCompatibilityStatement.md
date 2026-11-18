# Restricted cyclic base change at complex places

`Langlands.Automorphic.Unramified.RestrictedCyclicBaseChangeComplexPlaceCompatibilityStatement`
is a named unproved external input for the restricted B7 derivations. It states
the complex-place parameter consequence of strong lifting in the setting
authorized by point (b) of the operator's R2 ruling.

## Quantifiers and hypotheses

1. Quantify over number fields `F : Type uF` and `E : Type uE`, with `F` CM and
   `E/F` Galois with cyclic group `E ≃ₐ[F] E`. Both additive adele quotients
   are supplied with compactness instances. The first hypothesis is
   `(Module.finrank F E).Prime`. The CM assumption already makes `F` totally
   complex.
2. Quantify over an actual finite place `v₀` of `F` and assume
   `v₀ ≠ Harris.conjPlace F v₀`. Then quantify over `w₀` above `v₀` and `wc`
   above `Harris.conjPlace F v₀`. The hypotheses `∀ w', w' = w₀` and
   `∀ w', w' = wc` express uniqueness in the respective types of places above.
3. Quantify over `r : ℕ`, `S : CuspidalOperatorRealization F r`, and
   `D : IsobaricData E`. The realization `S` has matrix rank `r+1`. Its
   hypotheses, in order, are `HasUnitaryCentralCharacter S` in the published
   cyclic transfer convention, followed by
   `S.isoClass.HasSupercuspidalComponent` at `v₀` and at
   `Harris.conjPlace F v₀`. Next assume `D.IsUnitary`, meaning each of its
   actual positive-rank cuspidal constituents is unitarizable, and assume
   `IsobaricData.IsWeakBaseChangeOf D` of the singleton
   `IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank S.isoClass)`.
   This weak relation includes equality of total ranks and uses genuine
   constituent spectral presentations at almost all finite places.
4. For each complex place `v` of `F`, each actual `w : InfinitePlacesAbove E v.1`
   and each `ds : List ComplexCharacterData`, the singleton of `S.isoClass`
   has aggregate parameter `ds` at `v` if and only if `D` has aggregate
   parameter `complexPlaceParameterTransport v w ds` at
   `complexPlaceAbove v w`. The latter packages the actual place `w.1`
   with its proof of being complex.

The independent universes are `uF`, `uE`, `uV`, `uW` in that order. The
supercuspidality predicates use the downstairs spectral universe `uV` and the
weak transfer uses `uV` and `uW` for the downstairs and upstairs spectral
presentations. The statement applies regardless of regular algebraicity or
conjugate self-duality on either side. The supercuspidality hypotheses concern
only `S.isoClass`, and the CM instance concerns only `F`. The auxiliary places
restrict the global inputs, while the conclusion ranges over every complex
place and every supplied list.

## Aggregate parameters and completion coordinates

Both sides use `IsobaricData.HasComplexPlaceParameter` from Task 7466. For
isobaric data `D` over a number field `K`, attachment of a list `ds` at a
complex place of `K` gives an enumeration
`σ : Fin b → PositiveRankCuspidalClass K` with `Finset.univ.val.map σ = D`
and a literal parameter list `d j` at that place for each `σ j`. The supplied
list satisfies `ds.Perm (List.ofFn d).flatten`. Repeated constituents and
repeated character blocks contribute every occurrence. The published singleton
theorem
`IsobaricData.hasComplexPlaceParameter_ofCuspidal` gives exactly

```lean
(IsobaricData.ofCuspidal c).HasComplexPlaceParameter v ds ↔
  ∃ ds', c.HasComplexPlaceParameter v ds' ∧ ds.Perm ds'
```

The literal cuspidal predicate is for the list `ds'` in the order supplied to
its standard module. At rank `n` it uses an injective `ℂ`-linear map from the
`U(n)`-finite functions of the normalized complex principal series into the
realization, intertwining the compact and Lie actions. The character blocks
use the normalization
`χ(z) = (z / ‖z‖)^m · ‖z‖^(2s)` for `z ∈ ℂˣ`, with integer weight `m`,
complex exponent `s`, Euclidean norm `‖z‖`, and normalized local absolute
value `‖z‖²`.
The principal series includes the square root of the Borel modulus.

The place actions use the selected `Completion.extensionEmbedding` at each
place. The completed inclusion in these coordinates is the identity when
`w.1.embedding.comp (algebraMap F E) = v.1.embedding` and complex conjugation
otherwise. The published `complexPlaceParameterTransport v w ds` uses exactly
this test. In the identity case it returns `ds`, and in the conjugation case it
returns `ds.map ComplexCharacterData.conj`. Each conjugate block precomposes
its character with `z ↦ z̄`, negates the weight and keeps the exponent. This
preserves list positions and all repetitions, with the same normalization as
the parameter predicate used by B7.

## Source and scope

The original is James Arthur and Laurent Clozel, *Simple Algebras, Base Change,
and the Advanced Theory of the Trace Formula* (1989), registered as
`arthur-clozel-1989-base-change`. [Publisher's edition](https://press.princeton.edu/books/paperback/9780691085180/simple-algebras-base-change-and-the-advanced-theory-of-the-trace)

- Chapter III, Definition 1.2, printed p. 199 / PDF p. 213, defines strong
  lifting by the local base-change relation at every place above a place of
  `F`, including infinite places.
- Definition 4.1 and Theorem 4.2(c), printed p. 202 / PDF p. 216, specify
  induction from unitary cuspidal data and give existence and uniqueness of the
  weak lift within this class for cyclic extensions of prime degree.
- Theorem 5.1, printed pp. 212–213 / PDF pp. 226–227, upgrades a weak lift
  between representations induced from cuspidal to a strong lift.

At a complex `v`, the completed extension splits as a product of copies of
`ℂ`. Strong lifting identifies the local lift at each `w` with the downstairs
component through the completed inclusion. In the Library this leads to the
displayed comparison of transported standard-module blocks and their
multiplicities. The proposition is a restricted, derived parameter consequence
of strong lifting. The comparison of the original induced representations and
local lifting with the Library's weak spectral and archimedean predicates is
part of the unproved content.

The registered operator plan `operator-external-inputs-plan-2026-11-16`
(`external-inputs-plan.tex`, Sections 2.2 B7, 4.6 and 4.8) supplies the design
for using strong lifting at split infinite places. Point (b) of the subsequent
R2 ruling authorizes this complex-place formulation without the plan's
regular-algebraicity condition. Task 7465 assumes a regular-algebraic source
and asks for finite-place compatibility with a chosen local base-change map.
The complex-place comparison here is a separate external premise. The
simple trace formula packages of Task 7340 leave the global separation of
archimedean components needed for this premise open.

## Conditional derivation of restricted B7

Task 7340 owns the derivation of the literal clauses (1)r and (2)r of
`RestrictedCyclicWeakBaseChangeComplexPlaceStatement` from this premise and
the following comparisons.

- For (1)r, take `D` to be the singleton of the upstairs cuspidal class. Use
  `CuspidalOperatorRealization.isUnitarizable_of_hasUnitaryCentralCharacter`
  and `IsobaricData.isUnitary_ofCuspidal` for its unitarity, and
  `IsobaricData.isWeakBaseChangeOf_ofCuspidal_iff` for the comparison between
  the singleton and cuspidal weak-transfer relations.
- For both clauses use the singleton parameter theorem above. Recovering
  literal parameters for the exact lists in restricted B7 requires a
  parameter-order comparison for the relevant normalized standard modules
  or a direct attachment of those lists. The singleton theorem supplies
  `ds'` together with `ds.Perm ds'`.
- For (2)r, the isobaric sum `IsobaricData.galoisOrbit` of the upstairs
  cuspidal class uses one constituent for each Galois automorphism. Show
  that this datum is unitary and is a weak base change of the downstairs
  singleton given the cuspidal weak-induction hypothesis. This requires
  comparing the arithmetic spectral relations at split and inert unramified
  places. At split places all places above the base place contribute. At
  inert unramified places the fixed upstairs unramified component contributes
  with degree multiplicity after the residue-degree power in weak base change.
- For (2)r, compare the complex-place parameter of each Galois conjugate at
  the chosen `w` with the parameter of the original class at the corresponding
  place above `v`. Transporting the concatenated list
  `complexPlaceLanglandsSum v e ds` from `v` to `w` must give the aggregate
  list for this orbit up to `List.Perm`. The reverse implication in the
  premise then supplies the downstairs aggregate parameter before the
  literal parameter-order comparison.

These steps belong to the later conditional derivation. The complex-place
argument uses split local compatibility, while E2 concerns the separate
finite-place derivation.
