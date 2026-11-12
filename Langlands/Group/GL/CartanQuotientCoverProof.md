# Normalized Cartan covering modulo the entire center

Authors: Worker 1443; Worker 197 of the previous instance (the carried draft's
seven algebraic adapters).

`Langlands.GeneralLinear.CartanQuotient.cartanQuotientCover.{uF}` proves the
exact published closed proposition
`Langlands.GeneralLinear.CartanQuotient.CartanQuotientCoverStatement.{uF}`.
The separately named theorem `cartanQuotientDisjoint.{uF}` proves
`Langlands.GeneralLinear.CartanQuotient.CartanQuotientDisjointStatement.{uF}`.
Both statements are imported from
`Langlands.Group.GL.CartanQuotientCoverStatement`. Their pair and all imported
definitions remain unchanged.

## Hypotheses and concrete objects

The theorems quantify over every `p : ℕ` with `[Fact p.Prime]`, every
`F : PadicField.{uF} p`, every supplied `T : F.TopologicalData`, every
`n : ℕ` with `0 < n`, and the actual central quotient
`GeneralLinear n F.Carrier ⧸ Subgroup.center (GeneralLinear n F.Carrier)`.
The field universe is arbitrary. There is no representation carrier, additional
topological datum, or restriction to `canonicalTopologicalData`.

Write `v = T.discreteValuation`, `ϖ = uniformizerUnit T`,
`K = maximalCompact T n = Iwasawa.integralRange v n`, and
`π = quotientMap F n`. The representative `a(lam) = representative T lam`
is the actual diagonal matrix `Iwasawa.torus ϖ lam`.
Membership in `cell T lam` means exactly
`x = π (k₁ * a(lam) * k₂)` for `k₁, k₂ ∈ K`.
`Normalized lam` means that `lam` is antitone, every coordinate is
nonnegative, and some coordinate is zero. The unique object in the covering
theorem is this tuple; neither integral factor is asserted unique.

## Uniformizer and scalar adapters

`uniformizer_isUniformizingElement T` proves
`Iwasawa.IsUniformizingElement v ϖ`. The published
`T.discreteValuation_uniformizer` gives `v ϖ = WithZero.exp (-1) < 1`.
For `x ≠ 0`, the valuation is nonzero, and
`-WithZero.log (v x) : ℤ` is an exponent expressing `v x` as a power of
`v ϖ`. The proof uses `WithZero.exp_zsmul` and `WithZero.exp_log`.
It applies to the supplied `T` throughout.

`scalar_unit_split T u` expresses every field unit as
`u = ϖ ^ e * ε`, with `e : ℤ` and `v ε = 1`. It applies the preceding
uniformizer result to `u`, defines `ε = u * (ϖ ^ e)⁻¹`, and computes the
valuation by multiplicativity and inversion.

`scalar_mem_maximalCompact T ε hε` proves membership of the actual scalar
matrix in `K` when `v ε = 1`. In successor rank it identifies that scalar
with `Iwasawa.diagonalUnits (fun _ => ε)` and applies
`Iwasawa.diagonalUnits_mem`. That lemma gives membership in the successor
integral subgroup, definitionally the same subgroup as `integralRange` by
`Iwasawa.integralRange_succ`. In rank zero all invertible matrices coincide
with the identity. Thus this helper includes rank zero.

`quotientMap_eq_iff_scalar g h` proves
`π g = π h ↔ ∃ u : F.Carrierˣ, g * scalar u = h`.
It uses `QuotientGroup.mk'_eq_mk'` and
`Matrix.GeneralLinearGroup.center_eq_range_scalar`, so it accounts for the
entire center, not just the subgroup of uniformizer powers.
`quotientMap_eq_power_integral T` combines this lift with `scalar_unit_split`
and integral scalar membership. Centrality moves the uniformizer scalar to
the left and gives
`scalar (ϖ ^ e) * g * k = h` with `k ∈ K`.

`integral_factors_eq_of_quotient_eq T` applies that result to two lifted cell
factorizations. It commutes the uniformizer scalar past the left integral
factor and absorbs the valuation-one scalar into the right integral factor.
The result is an equality in the actual general linear group:
`k₁ * (scalar (ϖ ^ e) * a(lam)) * k₃ = l₁ * a(mu) * l₂`,
where `k₃ ∈ K`.

## Existence and normalized uniqueness

The implementation imports the published
`Langlands.Group.GL.CartanQuotientLawsProof` for `representative_shift`,
`cell_shift`, and `normalized_iff_antitone_last_eq_zero`; none of these laws
is an unproved hypothesis.

For existence, `cartanQuotientCover` writes the positive rank as `m + 1`
and lifts `x` along the surjective quotient homomorphism.
It applies `Langlands.GeneralLinear.Cartan.cartanDecomposition` from
`Langlands.Group.GL.CartanProof`, using the uniformizer adapter above, to
obtain an antitone tuple `a` and actual integral factors for the lift.
The new tuple is
`lam = shift a (-a (Fin.last m))`.
Translation preserves antitonicity and makes its last coordinate zero.
The published normalization equivalence proves `Normalized lam`.
The published `cell_shift` identifies its cell with the original cell,
so the original factors establish membership of `x`.

For uniqueness, `normalized_eq_of_mem T` takes a point in two normalized
cells and lifts the equality of quotient images using
`integral_factors_eq_of_quotient_eq`.
The published `representative_shift` rewrites the scalar-modified middle
factor as `representative T (shift lam e)`.
This tuple is antitone. The published `Cartan.exponent_unique`, applied to
the resulting equality with four integral outer factors, yields
`shift lam e = mu`.

`eq_of_normalized_shift` then proves `lam = mu`. An attained zero in
`lam`, together with nonnegativity of `mu`, gives `0 ≤ e`; an attained zero
in `mu`, together with nonnegativity of `lam`, gives `e ≤ 0`. Thus `e = 0`
and the tuple equality is pointwise equality of the original tuples.
This helper uses only the normalization predicates and works at any rank
where they can hold. The closed covering theorem combines existence with
this uniqueness lemma.

Finally `cartanQuotientDisjoint` uses the uniqueness clause of the proved
closed covering theorem. A point belonging to the cells of two normalized
tuples would make both tuples equal to its unique covering tuple, contradicting
their assumed inequality.

## Provenance and scope

Original: J.-L. Waldspurger, *La formule de Plancherel pour les groupes
p-adiques, d'après Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333,
section I.1, printed pp.239–242 (one-based PDF pp.5–8).
Source ID `waldspurger-2003-plancherel`; SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
Retained original:
`/home/taskhub/central-library/Waldspurger--La formule de Plancherel pour les groupes p-adiques d'apres Harish-Chandra--2003.pdf`.
These original pages were read for this proof. No matching source-specific
erratum was found in the available project notes; the corrections in the
published Waldspurger source map do not concern I.1(4).

Printed p.239 defines the positive chamber by nonnegative simple-root
pairings. Printed p.240 uses
`q ^ (-⟨χ, H_G(g)⟩) = |χ(g)|`, giving decreasing integer exponents in
the upper-Borel chamber for `GL_n`. Equation (4), printed p.241, states the
disjoint Cartan covering. The normalized integer tuples and the quotient by
the entire center here are derived `GL_n` specializations, not verbatim
statements of that equation. The implemented proof uses the Library's
algebraic GL Cartan theorem and the explicit scalar calculations above;
it does not formalize Waldspurger's general reductive-group argument.
The seven initial adapters were reused from the carried draft by
Worker 197 of the previous instance;
the closing existence, uniqueness and disjointness proofs were added by
Worker 1443.

This pair closes the two exact algebraic targets. It proves no covering by
arbitrary `H` cells, uniqueness of integral factors, analytic estimate,
Haar-volume assertion from equation (5), summability, or representation
theorem. Those consumer obligations remain separate.
