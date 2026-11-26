# Weyl Jacquet multisets of unramified principal series

The module `Langlands.BaseChange.UnramifiedWeylJacquetSupportStatement` defines the
multiset of exponents of the normalized Borel Jacquet module of a representation of
`GL_(r+1)(F)`, for a p-adic field `F` of characteristic zero, and proves that it counts
the dimensions of simultaneous generalized weight spaces. It then states, as the
proposition `UnramifiedWeylJacquetSupportStatement`, the Weyl multiset and
opposite-order properties of the irreducible constituents of unramified principal
series. Finally, it derives from that proposition the premise `HasWeylJacquetSupport`
of `WeylSphericalTraceReplacementStatement` for families of generic constituents. The
file states the proposition and does not prove it.

## The Jacquet multiset

Throughout, `F` is a `PadicField`, with the canonical topology, the canonical
uniformizer `F.canonicalTopologicalData.uniformizerUnit` (written `ϖ`) and the
spherical subgroup `sphericalSubgroup F r = GL_(r+1)(𝒪_F)`. The upper Borel subgroup is
the standard block parabolic of `borelShape r`, with `r + 1` blocks of size one. Its
Levi `(borelShape r).Levi F.Carrier` is the diagonal torus `T(F) = (F^×)^(r+1)`, as a
product of copies of `GL_1(F)`.

- `borelIntegralDiagonal F r` is `T(𝒪_F)`: the Levi elements whose diagonal matrix
  lies in `GL_(r+1)(𝒪_F)`. `singletonLevi_mem_borelIntegralDiagonal_iff` proves that a
  diagonal element is in it exactly when every entry has valuation zero.
  `borelIntegralDiagonalOpen F r` is the same subgroup as an open subgroup of the
  canonical Levi topology.
- `borelUniformizerLevi F r i` is the diagonal element with `ϖ` in coordinate `i` and
  `1` elsewhere (`leviEmbedding_borelUniformizerLevi_val`). It is central in the
  Levi, being a block scalar.
- The Jacquet module is the Library's normalized Jacquet module
  `F.canonicalNormalizedJacquet (borelShape r) ρ`, that is
  `F.canonicalTopologicalData.normalizedJacquet (borelShape r) ρ`. It is the
  coinvariant quotient of `ρ` by the upper unipotent group, with the diagonal element
  `t` acting by `δ_B(t)^(-1/2)` times the action of `ρ(t)`, where `δ_B` is the modulus
  of the upper Borel subgroup.
- `borelJacquetIntegralFixed F ρ` is the subspace of the Jacquet module fixed by
  `T(𝒪_F)`. `finiteDimensional_borelJacquetIntegralFixed` proves that it is
  finite-dimensional when `ρ` is admissible, from the admissibility of the normalized
  Jacquet module (`Parabolic.isAdmissible_normalizedJacquet`).
- `borelJacquetUniformizerAction F ρ i` is the action of `borelUniformizerLevi F r i`
  on this subspace. These operators preserve it and commute with each other
  (`commute_borelJacquetUniformizerAction`) because the uniformizer elements are
  central.
- For `z : Fin (r + 1) → ℂˣ`, `borelJacquetWeightSpace F ρ z` is the simultaneous
  generalized eigenspace of these operators with eigenvalues `z i`, and
  `borelJacquetMultiplicity F ρ z` is its dimension.
- `borelJacquetMultiset F ρ` is the multiset in which each `z` has this multiplicity.
  It is defined to be empty if infinitely many tuples have positive multiplicity.
  `finite_support_borelJacquetMultiplicity` proves that this does not happen when the
  fixed space is finite-dimensional, since the generalized weight spaces of commuting
  operators are independent. `count_borelJacquetMultiset` proves that for an
  admissible `ρ` the multiset contains `z` exactly `borelJacquetMultiplicity F ρ z`
  times. `count_borelJacquetMultiset_principalSeriesOfTuple` and
  `count_borelJacquetMultiset_automorphicObject` record the two cases used in the
  statement.

Because `T(𝒪_F)` acts trivially on the fixed space, the torus acts there through
`T(F)/T(𝒪_F) ≅ ℤ^(r+1)`, whose basis is given by the uniformizer elements. The fixed space
then decomposes into the generalized weight spaces, and each composition factor for the
torus is a character of `T(F)` trivial on `T(𝒪_F)`. Its values at the uniformizer
elements form a tuple `z`. The number of composition factors with tuple `z` equals the
dimension of the generalized weight space of `z`. The multiset therefore counts the
unramified characters of `T(F)` occurring in the fixed space, with their multiplicities
as composition factors. The modulus `δ_B` is trivial on `T(𝒪_F)`, so the normalized
and unnormalized actions have the same fixed vectors. For a subquotient of an
unramified principal series every composition factor of the Jacquet module is
unramified, so this subspace is the whole Jacquet module. These two remarks are
mathematical background and are not stated in Lean.

## The proposition

`UnramifiedWeylJacquetSupportStatement` quantifies over every prime `p`, every
`F : PadicField p` in universe `uF`, every `r` and every `z : Fin (r + 1) → ℂˣ`, with
carriers of the irreducible representations in an independent universe `uV`. Let
`I(z)` be `principalSeriesOfTuple F z`, the normalized induction from the upper Borel
subgroup of the unramified characters with values `z i` at `ϖ`. The proposition asserts:

1. `borelJacquetMultiset F I(z) = weylTupleMultiset z`. The right side is the multiset
   of the tuples `z ∘ w` over all permutations `w`, so a tuple fixed by some
   permutations is counted once for each of them.
2. For every irreducible admissible `A : AutomorphicObject F r.succPNat` that is a
   subquotient of `I(z)` (`IsSubquotientOf`), `borelJacquetMultiset F A ≤
   weylTupleMultiset z`.
3. If moreover `A` is generic (`Whittaker.IsGeneric ψ r A` for some nontrivial
   additive character `ψ`: irreducible, admissible and with a nonzero Whittaker
   functional for the standard character of the upper unipotent group), then:
   - if `A` has a nonzero `GL_(r+1)(𝒪_F)`-fixed vector, its multiset is
     `weylTupleMultiset z`;
   - if `A` has no nonzero `GL_(r+1)(𝒪_F)`-fixed vector, no tuple `y` of its multiset
     satisfies `IsOppositeWeightOrder y`, that is, no tuple has weakly decreasing
     absolute values `‖y 0‖ ≥ ‖y 1‖ ≥ ⋯`.

`UnramifiedWeylJacquetSupportStatement.hasWeylJacquetSupport` proves that the
proposition gives `HasWeylJacquetSupport inducing spherical exponents` for every family
`A i` of generic irreducible subquotients of `I(inducing i)`, with `spherical i` the
existence of a nonzero `GL_(r+1)(𝒪_F)`-fixed vector in `A i` and `exponents i` the
actual multiset `borelJacquetMultiset F (A i)`. This is the Jacquet support premise of
`WeylSphericalTraceReplacementStatement`. The twisted trace of the Galois operator on
the Jacquet module is a different input and does not appear here.

## Normalizations and orders

Henniart–Lemaire write `A_0` for the diagonal torus, `δ_0` for the modulus of the upper
Borel subgroup and `I_χ` for the normalized principal series of a character `χ` of
`A_0(E)`. In I.5.4 they define `X(χ)` as the multiset of the conjugates `χ^w`, `w ∈ W`,
with multiplicities, and quote the geometric lemma: the semisimplification of the
unnormalized Borel Jacquet module of `I_χ` is the sum of the characters `δ_0^(1/2) χ^w`.
For an irreducible subquotient `π` they define the submultiset `X(χ, π)` by the same
decomposition of the Jacquet module of `π`. The normalized Jacquet module removes the
factor `δ_0^(1/2)`. When `χ` is unramified with values `z i` at the uniformizer, the
conjugates `χ^w` are the unramified characters with values `z ∘ w`. Thus `X(χ)`
corresponds to `weylTupleMultiset z` and `X(χ, π)` to `borelJacquetMultiset F π`.
Clauses 1 and 2 are these two facts.

Write `|χ|(x) = |x_1|^(a_1) ⋯ |x_n|^(a_n)`. In I.4.1, `ℝⁿ₊` is the set of real tuples
with `a_1 ≥ ⋯ ≥ a_n`, and `χ` is positive when `a(χ) ∈ ℝⁿ₊`. Since `|ϖ| = q^(-1) < 1`,
where `q` is the residue cardinality, the value `z_i = χ_i(ϖ)` has absolute value
`q^(-a_i)`. So positive characters are
those whose uniformizer values have weakly increasing absolute values. Let `t` be the
longest Weyl element. In I.5.5, `Y_χ^t` consists of the characters `χ^(wt)`, `w ∈ W_|χ|`.
For positive `χ`, these are exactly the members of `X(χ)` whose real exponents are
weakly increasing, with the same multiplicities. Their uniformizer values have weakly
decreasing absolute values, which is the opposite order `IsOppositeWeightOrder` of
`WeylSphericalTraceReplacement`.

The argument of I.5.5, Lemme 1, applies after reordering `z` into a positive tuple,
which changes neither `weylTupleMultiset z` nor the composition factors of `I(z)`. Let
`I*_χ` be the unique generic irreducible subquotient and `Ī_χ` the unique irreducible
quotient of `I_χ`. Part (2) proves `Y_χ^t ⊂ X(χ, Ī_χ)` and identifies `Ī_χ` with the
spherical subquotient for unramified `χ`. Since `X(χ)` is the sum of the `X(χ, π)` over
the composition factors `π`, the factor `Ī_χ` occurs once, and an irreducible subquotient
without spherical vectors has no tuple in the opposite order. This gives the exclusion
clause. Part (3) states that `I_χ` is irreducible exactly when its spherical and generic
subquotients are isomorphic. A subquotient that is both spherical and generic is
isomorphic to both, so `I_χ` is irreducible and isomorphic to it, and its multiset is
the full `X(χ)`. This gives the other clause of 3. The Théorème of I.5.5 uses these
facts for the generic constituents `π_i` and `ρ_j` on both sides of the base change
identity.

## Source

Guy Henniart and Bertrand Lemaire, *Changement de base et induction automorphe pour
`GL_n` en caractéristique non nulle*, Mém. Soc. Math. Fr. 124 (2011):

- I.4.1, printed p. 26 (PDF p. 34): the convention `ℝⁿ₊ = {ν_1 ≥ ⋯ ≥ ν_n}`;
- I.5.4, printed pp. 33–35 (PDF pp. 41–43): positive characters, `X(χ)`, `X(χ, π)` and
  the geometric lemma for the Borel Jacquet module;
- I.5.5, Lemme 1 and its proof, printed pp. 35–36 (PDF pp. 43–44): the multisets
  `X_χ ⊂ Y_χ ⊂ X*_χ` and `Y_χ^t ⊂ X(χ, Ī_χ)`, the spherical Langlands quotient and the
  irreducibility criterion;
- I.5.5, Théorème and its proof, printed pp. 37–39 (PDF pp. 45–47): the use of these
  multisets for generic constituents.
