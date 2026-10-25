# Normalized Cartan coverage of the actual central quotient

Author: Worker 197.

This pair states two closed propositions in
`Langlands.GeneralLinear.CartanQuotient`, using the published definitions from
`Langlands.Group.GL.CartanQuotientDefinitions`. Neither proposition is proved
here. The second is a separately named consequence intended for consumers that
need disjoint subsets.

## Exact statements

Both declarations quantify over every natural prime `p` with `[Fact p.Prime]`,
every `F : PadicField.{uF} p`, every supplied `T : F.TopologicalData`, and every
rank `n : ℕ` with `0 < n`. The only universe parameter is the field universe
`uF`; no representation carrier or further universe is introduced. The
supplied `T` selects the valuation and uniformizer already used by the concrete
definitions. The statements install no topology and introduce no additional
topological hypothesis.

`CartanQuotientCoverStatement` says that for every
`x : centralQuotient F n` there is a unique function `lam : Fin n → ℤ` such that
`Normalized lam` and `x ∈ cell T lam`. Uniqueness is among normalized tuples
whose cells contain this same `x`, as expressed by `∃!`. It does not assert
uniqueness of either integral factor.

`CartanQuotientDisjointStatement` says that for any two normalized tuples
`lam` and `mu`, the hypothesis `lam ≠ mu` implies
`Disjoint (cell T lam) (cell T mu)`. For sets this means their intersection is
empty. Once the covering proposition is proved, its uniqueness clause gives
this statement: a point in both cells would force the two tuples to agree.
This pair states that consequence independently; neither unproved proposition
is supplied as a hypothesis to the other.

The objects in these statements have their existing concrete meanings:

- `Normalized lam` means `Antitone lam`, all coordinates are nonnegative, and
  some coordinate is zero. At positive rank this fixes the minimum, which is
  the last coordinate, to zero. Positive rank matters because at rank zero
  no coordinate attains zero, although the central quotient has an identity.
- `centralQuotient F n` is the actual group
  `GeneralLinear n F.Carrier ⧸ Subgroup.center (GeneralLinear n F.Carrier)`.
  It divides by the entire center. Mathlib's
  `Matrix.GeneralLinearGroup.center_eq_range_scalar` identifies that center
  with the image of all scalar units of `F.Carrier`.
- `cell T lam` is the image under `quotientMap F n` of
  `K * representative T lam * K`, where
  `K = Iwasawa.integralRange T.discreteValuation n` and the representative is
  `Iwasawa.torus (LocalFactor.PadicAbelian.uniformizerUnit T) lam`.
  Membership is exactly the existing `mem_cell` formula. There is no abstract
  Cartan datum, covering field, or assumed factorization. These statements
  concern these `K` cells, and do not claim coverage by arbitrary `H` cells.

## Algebraic proof boundary

A separate proof must reuse the published theorem
`Langlands.GeneralLinear.Cartan.cartanDecomposition` from
`Langlands.Group.GL.CartanProof`, whose unique antitone exponents concern the
actual general linear group. That theorem is already proved; it does not by
itself assert normalized uniqueness after passage to the central quotient.
The remaining steps are as follows.

1. Establish `Iwasawa.IsUniformizingElement T.discreteValuation
   (LocalFactor.PadicAbelian.uniformizerUnit T)` for the supplied `T`.
   The existing `T.discreteValuation_uniformizer` identifies its value as
   `WithZero.exp (-1)`; nonzero values in `ℤᵐ⁰` are powers of this value.
   This is the concrete valuation adapter needed to apply the published
   general Cartan theorem; it is not a new assumption on `T`.
2. Lift `x` to a matrix `g` and apply `Cartan.cartanDecomposition`. If `a` is
   its antitone exponent tuple, subtract its last coordinate from every
   coordinate. The result is normalized. A common shift multiplies the
   diagonal representative by a scalar power of the uniformizer, which the
   central quotient kills. Thus the resulting normalized cell contains `x`.
3. For uniqueness, two cell factorizations with the same quotient image
   differ by an element of the entire center. Use
   `Matrix.GeneralLinearGroup.center_eq_range_scalar` to express it as
   `scalar u` for `u : F.Carrierˣ`. Split `u` as a power of the specified
   uniformizer times a scalar unit of valuation one. Both the latter scalar
   and its inverse are integral, so its scalar matrix lies in `integralRange`
   and can be absorbed into an integral factor. One may use the existing
   `Iwasawa.diagonalUnits_mem` and `Iwasawa.integralRange_succ` for this step
   after writing the positive rank as a successor.
4. The resulting equality in `GL_n(F)` compares antitone exponent tuples
   differing by one common integer shift. Apply the uniqueness part of
   `Cartan.cartanDecomposition` (also exposed as
   `Cartan.exponent_unique`). Both original normalized tuples have minimum
   zero, so the shift is zero and the tuples are equal. Finally derive the
   disjointness proposition from this uniqueness conclusion.

Scalar killing, representative and cell shift invariance, and the
positive-rank equivalence between `Normalized` and antitone with last
coordinate zero are shared helper obligations with the separate intrinsic-laws
work. Quotient equality lifting, scalar valuation factorization, and the
valuation-one scalar's integral membership are the additional boundary for
this covering proof. None of these helpers is assumed here or imported as an
unproved statement. Their proofs and the resulting two target theorems remain
separate work. No new analytic theorem is needed for this route.

## Provenance and scope

Source: J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques,
d'après Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, section I.1,
printed pp.239–242 (PDF pages 5–8). Source ID
`waldspurger-2003-plancherel`; SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
Retained original:
`/home/taskhub/central-library/Waldspurger--La formule de Plancherel pour les groupes p-adiques d'apres Harish-Chandra--2003.pdf`.
These original pages were read, and equation (4) on printed p.241 was also
checked in the rendered page. No matching errata note was located in the
public Library notes or project notes.

Printed p.239 defines the positive chamber by nonnegative simple-root
pairings. Printed p.240 uses the convention
`q^(-⟨chi, H_G(g)⟩) = |chi(g)|`, so for the upper Borel of `GL_n` the diagonal
powers with decreasing integer exponents give that chamber. Equation (4),
printed p.241, is the disjoint Cartan covering by `K m K`, indexed by the
positive chamber modulo `M₀¹`. The integer coordinates, quotient by the
entire center of `GL_n`, normalization by a common integer shift, and the
explicit disjointness proposition here are **derived specializations**.
Waldspurger does not state these exact Lean propositions or this normalized
integer indexing of the central quotient verbatim. The algebraic route above
explains their derivation from the existing GL Cartan theorem.

Equation (5), printed pp.241–242, concerns inverse-modulus volume estimates;
no part of that estimate is asserted here. The pair includes no Haar measure,
volume, measurability, compactness, summability, representation theory, or
analytic estimate. It supplies statement targets, not proofs or analytic
coverage certificates.
