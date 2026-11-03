# Normalized transitivity for compatible nested dynamic parabolics

`DynamicNestedParabolicTransitivityStatement` states the lemma of Renard,
*Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, VI.1.4, printed pp.136–137 / PDF pp.142–143. The registered source
is `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
For semistandard parabolics `P = MN ⊂ Q = LU` the lemma reads
`i_P^G = i_Q^G ∘ i_(P∩L)^L` and `r_P^G = r_(L∩P)^L ∘ r_Q^G`. The proof begins
by saying that these displayed equalities of functors are in fact natural
isomorphisms. The Lean statement asserts them as such.

## Setting

The statement quantifies over every nonarchimedean local field `F` and every
connected reductive group scheme `G` over `F`. The group is the actual
rational-point group `RationalPoint F G.X`, with its topology pinned to
`rationalPointTopology F G.X`. For cocharacters `χ, ψ` write `P = P(χ)`,
`M = Z(χ)`, `N = U(χ)`, `Q = P(ψ)`, `L = Z(ψ)` and `U = U(ψ)`. The functors use
these subgroups evaluated at the identity test object
`Over.mk (𝟙 (Spec F))`, whose points are the rational points.
The field and group universe `u` and the representation-carrier universe `uV`
are independent. There is no characteristic-zero, split, quasi-split,
finite-length or admissibility restriction.

## Compatible semistandard choices

`Dynamic.IsCompatibleNestedPair χ ψ` gives the inclusions `P ≤ Q` and `M ≤ L`
on every test scheme. It also gives one maximal split torus `T` and
cocharacters `α, β` of `T` with `χ = α ≫ i` and `ψ = β ≫ i`. This expresses
Renard's hypothesis that `P ⊂ Q` are semistandard with compatible Levi
factors. The torus is quantified existentially rather than fixed in advance.
This changes nothing, since Renard's fixed maximal split torus may be taken to
be `T`. Only the Levi inclusion `M ≤ L` (from `hPair.2.1`) is needed to form
the functors. The parabolic inclusion and the common torus restrict the
statement to Renard's semistandard nested setting.

## Structural input

The separate, visible input `Dynamic.NestedParabolicDecomposition χ ψ` holds
on every test scheme. It gives normality and complementary factors inside
`L ∩ P`, and the three products of the paragraph preceding the lemma:

- `L ∩ P = M (L ∩ N)`;
- `N = (L ∩ N) U`;
- `P = (L ∩ P) U`.

The algebraic-groups program keeps the theorem that compatible pairs have
this decomposition. This file does not prove that theorem, and it does not
replace it by a representation-theoretic premise.

`dynamic_nested_isSemidirectDecomposition_in_levi` converts the supplied
decomposition on a given test scheme. It takes the normality and complement
clauses and reverses the complement order using
`IsSemidirectDecomposition.of_isComplement'_symm`. It then restricts the
result to `L` with the published lemma `IsSemidirectDecomposition.subgroupOf`.
Intersection simplification gives exactly
`IsSemidirectDecomposition (P.subgroupOf L) (M.subgroupOf L) (N.subgroupOf L)`.
This proves a consequence of a given structural input, not the input itself.

## Topological hypotheses

Local compactness and the nonarchimedean group property are explicit instance
hypotheses on the canonical rational-point topology. Closedness of `N`, `U` and
`L` is also explicit, because the existing intrinsic Haar-modulus functors need
it. Closedness of `L` makes the outer Levi locally compact. The inner radical is
`N.subgroupOf L`, and the Levi-in-Levi functors get its closedness by preimage
from that of `N`.

## Conclusions and composition order

The statement asserts both

- `i_P^G ≅ i_(P ∩ L)^L ⋙ i_Q^G`;
- `r_P^G ≅ r_Q^G ⋙ r_(P ∩ L)^L`.

Here `F₁ ⋙ F₂` applies `F₁` first, so these match Renard's `i_Q^G ∘ i_(P∩L)^L`
and `r_(L∩P)^L ∘ r_Q^G`. Each assertion is `Nonempty` of an actual natural
isomorphism between functors on the full smooth complex representation
categories. The induction isomorphism uses `normalizedInductionFunctor` for
`P = M ⋉ N` and `Q = L ⋉ U`, and `leviNormalizedInductionFunctor` inside `L`.
The Jacquet isomorphism uses `jacquetFunctor` for `P` and `Q`, and
`leviNormalizedJacquetFunctor` inside `L`. The Levi-in-Levi functors transport
along the continuous equivalence `M.subgroupOf L ≃ₜ* M`. The statement adds no
new category, replacement functor, objectwise-only equivalence or unspecified
normalization.

## Universes

Induction functors raise the carrier universe from `uV` to `max u uV`. The
direct induction for `P` therefore lands in carrier universe `max u uV`. The
composite applies the Levi induction at `uV` and then the induction for `Q` at
`max u uV`. It lands in `max u (max u uV)`, which is the same universe
`max u uV`. All three Jacquet functors keep carrier universe `uV`.

## Modulus convention

The Library's modulus `δ(m)` is the Haar scaling factor of conjugation
`u ↦ m u m⁻¹` on the unipotent radical. It is Mathlib's `mulEquivHaarChar`,
with `μ(φ X) = mulEquivHaarChar φ · μ(X)`. Normalized induction twists by
`δ^{1/2}` and normalized Jacquet restriction by `δ^{-1/2}`. Renard's `δ_P`
comes from his choice of modular function in II.3.7, and the remark at printed
p.136 / PDF p.142 says it is the inverse of the usual convention. So his
formulas `i_P^G(τ) = Ind_P^G(τ ⊗ δ_P^{-1/2})` and
`r_P^G(π) = π_N ⊗ δ_P^{1/2}` of VI.1.2 describe the same normalizations.

## Provenance and proof obligations

This is a conditional dynamic-group formulation of the source lemma. The
structural packaging and the universe bookkeeping are derived formalization
choices. The statement has no transitivity, modulus-product or adjunction
premise. A proof must supply the modulus product `δ_(N∩L) δ_U = δ_N` on `M`
and both representation-theoretic isomorphisms. In the source, Jacquet
transitivity uses the transitivity of the unnormalized functors `j` (lemma
III.2.9) and of the forgetful functors, and the equalities `δ_P = δ_N`,
`δ_Q = δ_U` of V.5.4. It computes the product on `A_M` in terms of roots and
extends it to `M` by the Cartan decomposition.
Induction transitivity then follows by adjunction and uniqueness of adjoints
(A.V). A later proof may use any other verified route.

Worker 6 wrote the statement and the first explanation. Worker 1304 supplied
the conversion for an arbitrary pair to the existing Levi-in-Levi interface,
following the published standard-index conversion
`RationalPointFamily.isSemidirectDecomposition_in_levi` in
`RationalLeviDecomposition`.
