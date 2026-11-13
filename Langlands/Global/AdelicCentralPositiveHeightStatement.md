# Central archimedean factors of adelic points with polynomially bounded height

Author: Worker 5152.

`Langlands.Global.RepresentationGrowth.CentralNormOneHeightFactorStatement` is a
target proposition for proof. This module states it and proves nothing about it.
It is the factorization `G(𝔸) = A_G · G(𝔸)¹` of Getz–Hahn Lemma 2.6.2, together
with a polynomial bound on the height of the central factor.

## The statement

The proposition is universally quantified, in universe `u`, over:

- a number field `F : Type u` and a group scheme `G` over `Spec F` with
  `IsAffine G.X.left`;
- a natural number `N` and a matrix representation
  `rho : GroupScheme.MatrixRepresentation G (Fin N)`.

It assumes three things: `GroupScheme.IsConnectedReductive G`,
`GroupScheme.IsClosedSubgroup rho` and `0 < N`. These are the binders and hypotheses
of `AdelicSliceModerateGrowthStatement`.

It asserts that there are a real `c` and a natural number `e` such that every actual
adelic point `g ∈ G(𝔸)` has a factor `z ∈ G(𝔸)` with four properties:

1. `z` is central: `Commute z x` for every adelic point `x`;
2. the finite component of `z` is trivial:
   `AdelicGroupPoints.finite F G z = 1`;
3. `z⁻¹ g` lies in the norm-one subgroup `AdelicGroupPoints.normOneSubgroup F G`.
   This is the intersection of the kernels of the normalized idelic norms
   `|χ(·)|` of all `F`-rational characters `χ` of `G`;
4. `adelicHeight F G rho z ≤ c * adelicHeight F G rho g ^ e`, where
   `adelicHeight` is the full local-product matrix-and-inverse height of `rho`
   (module `AdelicRepresentationHeight`).

`c` and `e` come before the point quantifier.

## Meaning and expected proof

The first three properties say that `G(𝔸) = A_G · G(𝔸)¹`, where `A_G` is a central
group of archimedean points. They are already available. The published theorem
`Langlands.Global.PositiveRealTorus.adelicPositiveDecompositionStatement` (module
`AdelicPositiveDecompositionProof`) gives a split component `i : T → G`. This is a
central maximal split torus. The theorem also gives a topological group isomorphism
`E : A_T × G(𝔸)¹ ≃ G(𝔸)` with `E(a, n) = positivePointMap(a) · n`, where `A_T` is the
intrinsic positive subgroup of `T`. Put `z = positivePointMap(a)` for
`(a, n) = E⁻¹(g)`:

- `z` is central because `i` is central;
- the finite components of intrinsic positive points are trivial
  (`PositiveRealTorus.atFinitePlace_intrinsic`, module
  `AdelicPositiveTorusCompatibility`);
- `z⁻¹ g = n` is norm one.

The new content is the height bound 4. One proof: `rho ∘ i` is a representation of a
split torus, so in a rational basis `rho(z)` is diagonal. Its entries are the values
`ψ(a)` of the weights `ψ` of `T` in `rho`. These are positive reals, the same at all
infinite places, and the entries are `1` at the finite places. For each weight `ψ`,
the `ψ`-isotypic subspace `V_ψ` is `G`-stable because `T` is central. So
`χ_ψ = det(rho|V_ψ)` is a rational character of `G`, and it restricts to
`ψ^{d_ψ}` on `T`, where `d_ψ = dim V_ψ`.

The rational character `χ_ψ` is idele-valued, and in general `χ_ψ(g) ≠ χ_ψ(z)`.
Since `n = z⁻¹ g` is norm one, only the normalized idelic norms agree:
`|χ_ψ(g)|_𝔸 = |χ_ψ(z)|_𝔸`. The finite components of `z` are trivial, so
`|χ_ψ(z)|_𝔸 = ψ(a)^{d_ψ [F:ℚ]}`, with the normalized absolute values at the infinite
places.

The global norm `|χ_ψ(g)|_𝔸` is not a polynomial expression in adelic matrix entries.
It is bounded place by place. Choose a rational basis adapted to `V = ⊕ V_ψ`. In it,
`rho(g_v)` is block diagonal, and `χ_ψ(g_v)` is the determinant of one block. Hence
it is a polynomial of degree `d_ψ` in the entries of `rho(g_v)`. Likewise,
`χ_ψ(g_v)⁻¹ = χ_ψ⁻¹(g_v)` is the determinant of the corresponding block of
`rho(g_v)⁻¹`. The change of basis is a fixed rational matrix, integral with integral
inverse at almost all places. So at each place `v`,
`|χ_ψ(g_v)|_v^{±1} ≤ c_v · (local height of g at v)^{d_ψ}`, with `c_v = 1` at almost
all places; the local height is formed from the entries of `rho(g_v)` and
`rho(g_v)⁻¹`. The product of these local estimates over all places bounds
`|χ_ψ(g)|_𝔸^{±1}` by a constant times `adelicHeight(g)^{d_ψ}`. Then
`ψ(a)^{±1} = |χ_ψ(g)|_𝔸^{±1/(d_ψ [F:ℚ])}` is bounded the same way. This bounds the
diagonal entries of `rho(z_v)` and `rho(z_v)⁻¹` at every infinite place, and hence
bounds `adelicHeight(z)` by a constant times a power of `adelicHeight(g)`.

## Use

`Langlands.Global.RepresentationGrowth.adelicRationalHeightReductionStatement_of_siegel`
(module `AdelicRationalHeightReduction`) uses this statement to move from `G(𝔸)` to
the norm-one group covered by the Siegel statement
`AdelicSiegelFactors.AdelicSiegelReductionStatement`. Properties 1 and 2 keep the
central factor out of the finite component, and property 4 controls its height.

## Original-source correspondence

Getz–Hahn, *An Introduction to Automorphic Representations* (2024), registered as
`getz-hahn-2024-automorphic-representations` (PDF page = printed page + 17):

- (2.19)–(2.20), printed p. 68 (PDF p. 85): `G(𝔸_F)¹` is the intersection of the
  kernels of `|·| ∘ χ` over the characters of `G`. `A_G` is the neutral component of
  the real points of the greatest `ℚ`-split torus in `Res_{F/ℚ} Z_G`.
- Lemma 2.6.2, printed p. 69 (PDF p. 86): for reductive `G` over a number field,
  `A_G G(𝔸_F)¹ = G(𝔸_F)` and `A_G ∩ G(𝔸_F)¹ = 1`.

Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995),
registered as `moeglin-waldspurger-1995-spectral-decomposition`, chapter file
`05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf`, I.2.2, printed p. 20
(PDF p. 3):

- property (iv) compares `log ‖a‖` with `‖log_{M₀} a‖` on `A_{M₀}`, which contains
  `A_G`;
- property (v) bounds `m_{P₀}(g)^λ` by `c ‖g‖^r`.

For the central factor `z` of `g`, `log z` is determined by the values `|χ(g)|` of
the rational characters of `G`. Property (v) bounds these polynomially in `‖g‖`, and
property (iv) then bounds `‖z‖`. Together they give the bound 4 in MW's setting.

## Provenance

The statement is derived. GH Lemma 2.6.2 gives the factorization. Here `A_G` is
represented by the factor `z`, which is central with trivial finite component, rather
than by a named subgroup. The polynomial height bound combines MW I.2.2 (iv) and (v)
on the central part `A_G ⊆ A_{M₀}`. It is stated for the Library's `adelicHeight` of a
closed `rho` instead of MW's height for an embedding into `SL_{2n}`. The statement
uses the Library's `normOneSubgroup`, finite projection, `adelicHeight` and the
hypotheses of `AdelicSliceModerateGrowthStatement`.
