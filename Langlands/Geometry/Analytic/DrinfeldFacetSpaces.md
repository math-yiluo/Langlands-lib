# Harris's domains `U(f)` are open, and the action of their stabilizers

Author: Worker 21.

For a finite set `f` of vertices of the building, in particular for a facet,
this module proves that Harris's subset `U(f) = Res⁻¹(B(f, ε))` of Drinfeld's
upper half space `Ω` is open. It then makes `U(f)` an analytic domain of `Ω`
and constructs the action on it of every subgroup `H` of the stabilizer
`S(f)`, with the inclusion `U(f) → Ω` equivariant. Along the way it proves
that ultrametric norms on `F^n` are continuous and that `(z, a) ↦ |ℓ_a(z)|` is
jointly continuous on `Ω × F^{d+1}`. Everything in the module is proved. All
declarations lie in `Langlands.Analytic`.

The definitions of `U(f)`, `B(f, ε)`, the Goldman–Iwahori distance and `S(f)`
are those of the module `DrinfeldBuildingCovering`. The restricted action is
the general construction `invariantDomainAction` of the module
`InvariantAnalyticDomains`, applied to the action `omegaAction` of
`GL_{d+1}(F)` on `Ω` (module `DrinfeldGroupAction`).

## Original sources

Harris, *Supercuspidal representations in the cohomology of Drinfel'd upper half
spaces* (1997), registered as `harris-1997-drinfeld-cohomology`, SHA256
`aea284b917442459028b710dbfd9ae537631490504f3bc6d54a1e76ee697e0d9`, §2,
printed p.90 / PDF p.16:

> We choose an admissible, G_J^ad-equivariant covering of Ω by distinguished
> open subsets adapted to the map Res. For example, choose ε > 0, and for each
> vertex e ∈ BT let B(e, ε) be the open ε-neighborhood of the star of e in the
> first barycentric subdivision of BT. For the i-dimensional simplex f with
> vertices e₀, e₁, …, e_i, we let B(f, ε) = B(e₀, ε) ∩ B(e₁, ε) ∩ ⋯ ∩ B(e_i, ε).
> Then for each facet e ⊂ BT the subset U(e) = Res⁻¹(B(e, ε)) ⊂ Ω is
> distinguished, and the covering of Ω by the {U(e)} is admissible (cf. [BC]).

The same page: "for any facet e of BT, let S(e) be the stabilizer of e."

Harris, *Galois properties of cohomological automorphic forms on GL(n)*
(1999), registered as
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`, §2,
printed p.303 (PDF page = printed page − 298):

> Recall that the Drinfel'd upper half space Ω attached to the group G_J
> admits an admissible covering by open subsets denoted U(e) in [H1, §2],
> where e runs through the set of facets in the Bruhat-Tits building BT
> attached to G_J^ad.

and, later on the same page:

> Recall that the action of G_J on Ω lifts to an action on ℳ_N, and U(ê) is
> stabilized by a compact open subgroup S(ê) ⊂ G_J.

Harris does not prove that `U(e)` is open: `B(e, ε)` is an open
neighbourhood and `Res` is continuous. In the Library, `B(e, ε)` is measured
with the Goldman–Iwahori distance on norm classes (a derived choice explained
in `DrinfeldBuildingCovering.md`). The building `NormClass` carries the
quotient of the topology of pointwise convergence, and openness of `B(e, ε)` in
it is not proved here. Instead, the module proves directly that
`Res⁻¹(B(e, ε))` is open in `Ω`.

## Continuity of ultrametric norms (namespace `VectorNorm`)

For a norm `ν` on an `F`-vector space (`VectorNorm`, module
`DrinfeldReduction`):

- `apply_neg`: `ν(−a) = ν(a)`.
- `sub_le_apply_sub`, `abs_sub_le`: `|ν a − ν b| ≤ ν(a − b)`, from the
  ultrametric inequality `ν(b + (a − b)) ≤ max(ν b, ν(a − b))`.
- `add_le_add`: `ν(a + b) ≤ ν a + ν b`.

For a norm on `F^n` with the sup norm `‖·‖`:

- `le_mul_norm`: `ν a ≤ (Σ_i ν(e_i)) ‖a‖`, by writing `a = Σ_i a_i e_i`.
- `continuous`: `ν` is Lipschitz with constant `Σ_i ν(e_i)`, by the two
  previous estimates, hence continuous.

## Openness of `U(f)` (namespace `DrinfeldUpperHalfSpace`)

- `continuous_omegaNorm_apply`: `(z, a) ↦ |ℓ_a(z)|` (the Library's
  `omegaNorm K z a`) is continuous on `Ω × F^{d+1}`. At `(z₀, a₀)`, choose a
  polydisc chart `m` containing `z₀`; the chart `m + 1` is a neighbourhood of
  `z₀` (`range_chart_mem_nhds`). On it, `linearForm_le` bounds
  `|ℓ_{a − a₀}(z)|` by `(d + 1) ‖ϖ‖^{−(m+1)} ‖a − a₀‖`. Hence
  `||ℓ_a(z)| − |ℓ_{a₀}(z)|| → 0`, while `|ℓ_{a₀}(z)| → |ℓ_{a₀}(z₀)|` by
  continuity in `z` (`continuous_linearNorm`).
- `IsFacet.finite`: a facet, the set of classes of a lattice chain
  `ν₀, …, ν_k`, is finite.
- `one_mem_shell`, `ratio_smul`, `ratioSup_eq_sSup`: fix `c ∈ F` with
  `|c| > 1`. The ratio `ν a / μ a` is invariant under `a ↦ t a` for `t ≠ 0`,
  and every nonzero vector has a multiple in the compact shell
  `shell F d c = {|c|⁻¹ ≤ ‖a‖ ≤ 1}` of `DrinfeldUpperHalfSpace`
  (`exists_smul_mem_shell`). So the supremum `ratioSup ν μ` of
  `ν a / μ a` over all vectors (the value at `a = 0` is `0`) equals the
  maximum over the shell, which is attained because the ratio is continuous on
  the compact shell.
- `continuous_sSup_omegaNorm_div`, `continuous_sSup_div_omegaNorm`: for a fixed
  norm `μ`, the maps `z ↦ sup_{a ∈ shell} |ℓ_a(z)| / μ(a)` and
  `z ↦ sup_{a ∈ shell} μ(a) / |ℓ_a(z)|` are continuous on `Ω`. This is
  Mathlib's `IsCompact.continuous_sSup` for jointly continuous functions on
  `Ω × shell`; the denominators do not vanish there, since vectors of the shell
  are nonzero and `|ℓ_a(z)| > 0` for `a ≠ 0` and `z ∈ Ω`.
- `isOpen_setOf_distRatio_reduction_lt`: for a point `y = [μ]` of the
  building and `r > 0`, the set of `z ∈ Ω` with `D(Res z, y) < r` is open.
  Here `D = distRatio` is the multiplicative Goldman–Iwahori distance, the
  product of the two suprema, so this set is the preimage of `(−∞, r)` under
  the product of the two continuous maps above.
- `isOpen_reduction_preimage_vertexNbhd`: `Res⁻¹(B(e, ε))` is the union over
  the points `y` of the star of `e` of the sets `{D(Res z, y) < exp ε}`, hence
  open.
- `isOpen_facetDomain`: for a finite set `f` of vertices, `U(f)` is the finite
  intersection of the open sets `Res⁻¹(B(e, ε))`, `e ∈ f`.

## The action of the stabilizer on `U(f)`

Assume `d ≥ 1` (`NeZero d`), as for `omegaAction`.

- `facetAnalyticDomain K hS ε`: `U(f)` as an analytic domain of `Ω`, by
  `openDomain` (open subsets are analytic domains, module
  `InvariantAnalyticDomains`); `facetAnalyticDomain_carrier` records its
  subset.
- `isInvariantDomain_facetAnalyticDomain`: for a subgroup `H ≤ S(f)`, every
  element of `H` maps `U(f)` into itself. The underlying map of the action of
  `γ` is `z ↦ γ · z` (`localizedSpaceFunctor_map_omegaAction`), and `γ` fixes
  `f`, so `γ U(f) = U(γ f) = U(f)` (`actionMap_mem_facetDomain_of_mem_stabilizer`).
- `facetAction K hS ε H hH`: the action of `H` on the analytic space `U(f)`,
  by restriction of the action of `GL_{d+1}(F)` on `Ω`.
- `facetInclusion`: the inclusion `U(f) → Ω` as an `H`-equivariant morphism
  to the restriction of `omegaAction` to `H`.
  `localizedSpaceFunctor_map_facetInclusion` says that its underlying map is
  the inclusion of the subset.
- `facetStabilizerAction K hS ε`: for a facet `f`, the action of the full
  stabilizer `S(f)` on `U(f)`.

## Scope

- The stabilizer `S(f)` here is the stabilizer of `f` in `GL_{d+1}(F)`. It
  contains the centre, so it is not compact. Harris's compact open `S(ê)`
  (1999) belongs to the domains `U(ê)` of the tower `ℳ_N`, which also record a
  connected component. For `Ω` alone the construction accepts any subgroup
  `H ≤ S(f)`, for example the elements of `S(f)` whose determinant has
  absolute value one.
- Continuity of the action of `H` on `U(f)`, that is, a `G`-space structure,
  is not proved here. It would follow from the published statement
  `OmegaActionContinuityStatement` (continuity on `Ω`) together with
  `InvariantDomainContinuityStatement` (continuity on invariant domains) and
  `invariantDomainGSpace`.
- That `U(f)` is distinguished and that the `U(f)` form an admissible covering
  with the nerve of the building is the published statement
  `DistinguishedCoveringStatement`; it is not used here.
