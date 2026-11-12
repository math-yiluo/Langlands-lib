# Stabilizer fibres are equidimensional

Author: Worker 79.

`StabilizerFibreLocalDimensionStatement` states that every fibre of the stabilizer scheme of
a group action is equidimensional. It is an input to the semicontinuity argument for the
orbit-dimension strata of Conrad's Example 5.5 (clause 1 of
`UnipotentOrbitQuotientStatement`). The module states the claim and contains no proof.

## The statement

The data are those of `UnipotentOrbitQuotientStatement.lean`: a scheme `S`, a group scheme
`G : GroupScheme S`, a scheme `V : Over S` and an action `a : SchemeAction G V`. Products
are fibre products over `S`. The stabilizer scheme is the base change of the action graph
`lift a.hom (snd G.X V) : G × V ⟶ V × V`, `(g, v) ↦ (g.v, v)`, along the diagonal
`lift (𝟙 V) (𝟙 V) : V ⟶ V × V`. Its projection to `V` is
`σ = pullback.snd (lift a.hom (snd G.X V)) (lift (𝟙 V) (𝟙 V))`, the same morphism as in
`IsStabilizerFlat` and `HasOrbitDimension`. For a point `v` of `V`, the fibre
`σ.left.fiber v` (Mathlib's `Scheme.Hom.fiber`, the base change along
`Spec κ(v) → V`) is the stabilizer of `v`, a group scheme over the residue field `κ(v)`.

Assume that `G → S` is locally of finite type. The statement says: for every point `x` of
the stabilizer scheme,

`relativeTopologicalKrullDimAt σ.left x = topologicalKrullDim (σ.left.fiber (σ.left x))`.

The left side is the Library's relative local dimension
(`Langlands/AlgebraicGeometry/SchemeLocalFiberDimension.lean`): the local topological
Krull dimension at `x` of the fibre of `σ` through `x`, the minimum of the dimensions of
the open neighbourhoods of `x` in that fibre. The right side is the dimension of the whole
fibre. So the stabilizer of `v = σ(x)` has the same dimension at each of its points as
its total dimension.

## Source

The Stacks Project, Groupoid Schemes chapter PDF (registered source
`stacks-groupoid-schemes-chapter-pdf-2026-07-14`, SHA-256
`4506a39201063afc270cbb68c9c0c1d3c90937c03f98cfee074605b402e7a30f`), Section 39.8,
Lemma 39.8.1 (Tag 045X), PDF p.14: "Let `k` be a field. Let `G` be a locally algebraic
group scheme over `k`. Then `G` is equidimensional and `dim(G) = dim_g(G)` for all
`g ∈ G`." A locally algebraic scheme over `k` is one locally of finite type over `k`
(Section 39.8, opening paragraph). Stacks' `dim_g(G)` is the minimum of the dimensions of
the open neighbourhoods of `g`, which is `topologicalKrullDimAt`.

## Derivation (provenance: derived)

The statement is Lemma 39.8.1 applied to the fibres of `σ`. Fix a point `v` of `V`.

- The fibre `σ⁻¹(v)` is a group scheme over `κ(v)`: on points it is the subgroup
  `{g | g.v = v}` of `G_{κ(v)}`, with the group law of `G`.
- It is locally of finite type over `κ(v)`. Its map to `G_{κ(v)}` is a base change of the
  diagonal `V → V × V`, an immersion and hence locally of finite type. The map
  `G_{κ(v)} → Spec κ(v)` is a base change of `G → S`.

So Lemma 39.8.1 gives `dim_x σ⁻¹(v) = dim σ⁻¹(v)` at every point `x` of the fibre. This
is the statement for `v = σ(x)`. No hypothesis on `S` or `V` is needed. The names of
the declarations are derived here.

## Use

For a unipotent group `G` over a field acting on `V`, the identity section
`e : V → Stab`, `v ↦ (1, v)`, is continuous and satisfies `σ ∘ e = id`. The Library's
`RelativeDimensionSublevelOpenness` (Stacks Lemma 29.29.4) makes
`{x | relativeTopologicalKrullDimAt σ.left x ≤ n}` open in the stabilizer scheme, since
`σ` is locally of finite type. By this statement, its preimage under `e` is
`{v | dim σ⁻¹(v) ≤ n}`, so this set is open in `V`. The stratum
`{v | HasOrbitDimension a v d}` is the set where `dim σ⁻¹(v) = dim G - d`, the
difference of two such open sets, hence locally closed. Conrad's parenthetical (Brian
Conrad, *Weil and Grothendieck approaches to adelic points*, registered source
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`, Example 5.5,
printed p.16) is: "This is locally closed due to applying semicontinuity of fiber
dimension to the action map `G × V → V`."
