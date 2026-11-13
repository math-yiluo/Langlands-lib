# Proof of Tadic's local reduction for Speh representations

Module `Langlands.Representation.Classification.SpehUnitarizabilityReductionProof`.

The theorem `spehUnitarizabilityLocalReduction` proves the statement
`SpehUnitarizabilityLocalReduction F T` of
`SpehUnitarizabilityReductionStatement`, for arbitrary `p`, `F`, `T` and
independent universes `uF`, `uV`. That statement is an implication; the
proof introduces its hypotheses as

- `h1 : ComplementarySeriesUnitarity` (Tadic 1986, Proposition 2.9);
- `h2 : BernsteinUnitaryProductIrreducibility` (Theorem 2.5(i));
- `h3 : BernsteinUnitaryProductFactorUnitarity` (weak 2.5(ii));
- `hin : SpehUnitarityInputs`, destructured into the three Speh inputs
  `h5 : SpehComplementaryIrreducibility`,
  `h6a : SpehNeighborProductIrreducibility` and
  `h6b : SpehNeighborProductEndpointSubquotient`,

and from these derives `SpehUnitarizability`. The proof is the induction of
Tadic 1986, Lemma 6.2 (Badulescu 2014, Theorem 1(b)). It is a supporting unit
of Task 5099: once the hypotheses are proved in the Library, composing them
with this theorem gives `SpehUnitarizability` unconditionally.

## Results used from the Library

- `spehExistenceUniqueness`: every discrete-series datum has a Speh
  representative.
- `spehLengthOneComparison`: for length one, `IsSpeh π` means `π ≅ δ` after
  the exact rank transport.
- `SpehDatum.hasNonzeroInvariantSesquilinearForm_of_isSpeh` (Library module
  `Langlands.Representation.Classification.SpehHermitian`): every Speh
  representation is Hermitian, that is, carries a nonzero invariant
  sesquilinear form (Tadic 1986, Proposition 5.6(iii)).
- `twistedProductInducedZeroIso`: at exponent `0` the twisted product is the
  untwisted normalized product.
- `twistedProductInducedIso`: isomorphic blocks give isomorphic products.
- `Weil.IsomorphismInvariance.irreducible_iff` and
  `isUnitarizable_iff_of_equiv`: invariance under isomorphism.
- `SmoothRep.IsQuotient.isSubquotient`: a quotient is a subquotient.

## Helper lemmas (namespace `SpehUnitarityReduction`, all private)

- `irreducible_cast`, `unitarizable_cast`, `complementary_cast`:
  irreducibility, unitarizability, and irreducibility of the complementary
  product `complementaryProduct F T hn σ α` are unchanged by an exact rank
  transport `h ▸ σ` along `h : a = b`. Each is proved by `subst h`.
- `complementary_irreducible`: let `σ` be irreducible and unitarizable, and
  let `π(σ, α)` be irreducible for every `α ≠ 0` in `(-1/2, 1/2)`. Then
  `π(σ, α)` is irreducible on all of `(-1/2, 1/2)`. At `α = 0`, the product
  `ν^0 σ × ν^0 σ` is isomorphic (`twistedProductInducedZeroIso`) to the
  normalized product of the constant family `σ` on the uniform shape `(n, n)`.
  That product is irreducible by `h2`.
- `isSubquotient_of_isIrreducibleQuotient`: the irreducible quotient in
  `IsSpeh` is a subquotient.
- `lengthOne`: a representative of `u(δ, 1)` is unitarizable. By
  `spehLengthOneComparison` it is isomorphic to `δ` after the rank transport
  `1 * r = r`, and `δ` is unitarizable by `IsDiscreteSeries`.
- `centeredInduced_two`: for length two, the centered product
  `(d.withLength 2 _).centeredInduced` is equal to `complementaryProduct F T _
  δ (1/2)`. Both are `twistedProductInduced` on the shape `uniform 2 r` with
  constant block `δ`. The exponents `(2-1)/2 - i` for `i = 0, 1` are `1/2`
  and `-1/2`. The proof uses `fin_cases`, `simp` and `norm_num`.
- `step_h5`, `step_cast`, `step_iso`, `delta_complementary_irreducible`:
  `π(δ, α) = ν^α δ × ν^(-α) δ` is irreducible for every `α ∈ (-1/2, 1/2)`. For
  `α ≠ 0`, take a representative `S` of `u(δ, 1)` (`spehExistenceUniqueness`).
  `h5` makes `π(S, α)` irreducible. Then `complementary_cast` transports
  this along `1 * r = r`. The isomorphism `h ▸ S ≅ δ` from
  `spehLengthOneComparison`, applied blockwise through
  `twistedProductInducedIso`, gives `π(δ, α)`. The point `α = 0` is handled by
  `complementary_irreducible`. The isomorphism is given with its explicit
  type `complementaryProduct … ≅ complementaryProduct …`, so that
  `irreducible_iff` matches the representations syntactically.

## Main proof

Fix a discrete-series datum `d` with rank `r` and block `δ`. The auxiliary
claim `key` states that for every `k ≥ 1`, every representative `π` of
`(d.withLength k _)`, that is of `u(δ, k)`, is unitarizable. It is proved by
strong induction on `k` (`Nat.strong_induction_on`), with three cases.

- `k = 1`: `lengthOne`.
- `k = 2`: by `delta_complementary_irreducible`, `π(δ, α)` is irreducible on
  `(-1/2, 1/2)`. Apply `h1` to `σ = δ` and `α₀ = 1/2`: every irreducible
  subquotient of `π(δ, 1/2)` is unitarizable. The representative `π` is an
  irreducible quotient of `(d.withLength 2 _).centeredInduced`, which equals
  `π(δ, 1/2)` by `centeredInduced_two`. So `π` is unitarizable.
- `k = m + 3`: let `e = d.withLength (m + 2) _`, so `u(δ, m+2)` is the
  previous length and `e.length ≥ 2`. Choose representatives `S` of
  `u(δ, m+2)` and `Sdown` of `u(δ, m+1)` with `spehExistenceUniqueness`. The
  induction hypothesis makes `S` unitarizable. `h5` for `S` and
  `complementary_irreducible` make `π(S, α)` irreducible on `(-1/2, 1/2)`.
  So by `h1` every irreducible subquotient of `π(S, 1/2)` is unitarizable.
  The given `π` is a representative of
  `e.withLength (e.length + 1) = u(δ, m+3)`; this holds definitionally.
  `h6a` makes the binary product `X = π × Sdown` irreducible. `h6b` then makes
  `h ▸ X` a subquotient of `π(S, 1/2)`, where
  `h : (m+3) r + (m+1) r = 2 ((m+2) r)` is proved by `ring`. Hence `h ▸ X` is
  unitarizable, and so is `X` (`irreducible_cast`, `unitarizable_cast`). Both
  factors `π` and `Sdown` are irreducible (from `IsSpeh`) and Hermitian
  (`SpehDatum.hasNonzeroInvariantSesquilinearForm_of_isSpeh`). So `h3`,
  applied to the binary shape and the family
  `(T.binaryPairFamilyFunctor _ _).obj (π, Sdown)`, makes block `0`
  unitarizable. Block `0` is `π`.

Finally, apply `key` with `k = d.length`. Here `d.withLength d.length _` is
definitionally `d` for its degree and its `IsSpeh` relation, so this gives the
conclusion of `SpehUnitarizability` for `d`.

The module uses no `sorry` and no axioms beyond `propext`, `Classical.choice`
and `Quot.sound`.
