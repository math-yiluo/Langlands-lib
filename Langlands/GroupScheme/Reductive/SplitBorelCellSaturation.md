# Saturation of realized weights over an arbitrary field

This module proves that the realized weights of a split pinning are saturated over
every field: if a positive multiple `n • lam` of a torus character is realized by a
coordinate, then `lam` is realized. The Library's
`SplitPinning.IsRealizedWeight.of_nsmul` (module `Reductive.SplitBorelCellPower`)
proves this only over an algebraically closed field. The only use of algebraic
closure there is to compare two coordinates with equal `n`-th powers. Here that
comparison is done after base change to `AlgebraicClosure k`. The needed integrality
of the base change comes from geometric integrality of smooth connected affine
groups.

A coordinate `f` realizes `lam` (`SplitPinning.IsRealizedBy`, module
`Reductive.SplitBorelCell`) when:

- it is left covariant for the negative Borel subgroup with the character
  coordinate of `lam`;
- it is right invariant under the positive unipotent subgroup;
- its counit is one.

## Roots of a power over a non-closed field

`AffineCoordinates.exists_eq_algebraMap_mul_of_pow_eq_of_isDomain_baseChange`. The
setting:

- `R` is a commutative `k`-algebra;
- `K` is an algebraically closed extension of `k` with `K ⊗[k] R` a domain;
- `ε : R →ₐ[k] k` is a `k`-point.

If `y ^ n = z ^ n` with `0 < n` and `ε z ≠ 0`, then `y = ζ z` for a scalar `ζ` of
`k`.

Proof. Map `y` and `z` into `K ⊗[k] R` by the right inclusion. The Library lemma
`AffineCoordinates.exists_eq_algebraMap_mul_of_pow_eq` (module
`Reductive.CovariantPowerDescent`, over an algebraically closed field and a domain)
gives `ξ : K` with `y = ξ z` there. Apply the `K`-point `K ⊗[k] R → K` built from `ε`.
This gives `ξ = ε y / ε z`, which lies in `k`. Injectivity of the right inclusion,
which holds because `k → K` is injective, then gives `y = (ε y / ε z) z` in `R`.

## Base changes are domains

- `AffineCoordinates.isDomain_algebra_tensor_field`: for an affine group `H` with
  `H.X.hom` smooth and `H.X.left` connected, `algebra H ⊗[k] K` is a domain for every
  field extension `K` of `k`. The smoothness, connectedness and affineness are first
  transferred along `groupSchemeIso H` to the corepresented group scheme. The Library
  theorem `smoothConnectedAffineGeometry` (module `SmoothConnectedGeometryProof`)
  makes that group scheme geometrically integral. Applying this to the pullback
  square of `Spec` of the tensor-product pushout shows that
  `Spec (algebra H ⊗[k] K)` is integral, so the ring is a domain.
- `AffineCoordinates.isDomain_field_tensor_algebra_tensor`: for two such groups `H`
  and `G`, `K ⊗[k] (algebra H ⊗[k] algebra G)` is a domain. Let `L` be the fraction
  field of the domain `algebra G ⊗[k] K`. Then `algebra H ⊗[k] L` is a domain by the
  previous lemma. By flatness over the field `k`, `algebra H ⊗[k] (algebra G ⊗[k] K)`
  injects into it. Commutativity and associativity of the tensor product finish the
  proof.
- `SplitPinning.isDomain_algebraicClosure_negativeBorel_tensor` and
  `SplitPinning.isDomain_algebraicClosure_positiveUnipotent_tensor` specialize this to
  `H = p.negativeBorel` and `H = p.positiveUnipotent` with `K = AlgebraicClosure k`,
  using the Library's smoothness and connectedness of these subgroups and of `G`.

## From powers to covariance and invariance

Both lemmas assume that `AlgebraicClosure k ⊗[k] (algebra H ⊗[k] algebra G)` is a
domain.

- `AffineCoordinates.mem_leftCovariantSubspace_of_pow_of_isDomain_baseChange`. Let
  `f` and `χ` have counit one. Suppose the `n`-th power of the left covariance
  equation `f(i(h) g) = χ(h) f(g)` holds on every scheme test. Then `f` is left
  covariant for `i` with weight `χ`.

  Proof. Evaluate at the universal pair of points of `H × G`, the left and right
  inclusions into `algebra H ⊗[k] algebra G`. This gives
  `(r ⊗ id)(Δ f) ^ n = (χ ⊗ f) ^ n` in that algebra, where `r` is pullback along
  `i`. The root lemma, with the product of the counits as `k`-point, gives
  `(r ⊗ id)(Δ f) = ζ • (χ ⊗ f)`. So `f` is covariant for `ζ • χ`. Evaluating
  that covariance at the identity, with both counits one, forces `ζ = 1`.
- `AffineCoordinates.mem_rightInvariantSubspace_of_pow_of_isDomain_baseChange`. If
  `f` has counit one and the `n`-th power of right invariance under `j` holds on
  every test, then `f` is right invariant. The proof applies the previous lemma with
  `χ = 1` to the antipode coordinate of `f`, which has counit one. It translates back
  using the antipode evaluation `pointAlgebraHom G T g⁻¹ (S f) = pointAlgebraHom G T g f`.

## Saturation

- `SplitPinning.IsRealizedBy.of_pow'`. If `F` realizes `n • lam`, `f ^ n = F` and `f`
  has counit one, then `f` realizes `lam`. Left covariance follows from the first
  lemma above, using that the character coordinate of `n • lam` evaluates to the
  `n`-th power of that of `lam`. Right invariance follows from the second lemma.
- `SplitPinning.IsRealizedWeight.of_nsmul'`. If `n • lam` is realized for some
  `0 < n`, then `lam` is realized.

  Proof. The Library lemma `IsRealizedBy.exists_pow_eq_algebraMap` gives an `n`-th
  root of `F` in the localization of `algebra G` at the cell coordinate. The cell
  coordinate is a nonzerodivisor. Its image in the fraction field is therefore a
  unit, so this root maps into the fraction field. The coordinate algebra is an
  integrally closed domain (`isIntegrallyClosed_algebra_of_isConnectedReductive`),
  so the root comes from some `f₀ ∈ algebra G` with `f₀ ^ n = F`. Its counit `c`
  satisfies `c ^ n = 1`, so `c ≠ 0`, and `c⁻¹ • f₀` has counit one and `n`-th power
  `F`. Then `IsRealizedBy.of_pow'` applies.
- `SplitPinning.nsmul_mem_realizedWeights_iff'`: the same statement as membership in
  `p.realizedWeights`.

## Provenance

This is an internal lemma for the classification of simple representations by
highest weight (Milne, *Algebraic Groups* (2017), Theorem 22.2, registered as
`milne-2017-algebraic-groups`). The use of normality of the coordinate ring to pass
from a multiple of a weight to the weight follows the Library's algebraically closed
version (`Reductive.SplitBorelCellPower`). The geometric integrality of smooth
connected groups replaces the algebraic closedness of `k`.
