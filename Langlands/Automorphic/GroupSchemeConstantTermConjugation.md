# Constant terms along subgroups conjugate by a rational point

This internal module compares actual subgroup constant terms along a subgroup
functor and along its conjugate by a rational point. The input is a number
field `F : Type u`, an actual group scheme `G/F` and a rational point
`g : Over.mk (𝟙 (Spec F)) ⟶ G.X`, whose inner automorphism is the existing
`G.innerIso g`.

`innerAdelicPoint F G g` is the constant adelic point of `g`.
`innerAdelicPoint_eq_rational` uses `constantPoint_naturality` to identify
it with the principal image of the constant rational point of `g`.
`affinePointsTarget_innerIso_hom` specializes the published pointwise
formula `comp_innerIso_hom`: on adelic points, `innerIso g` is
`x ↦ γ * x * γ⁻¹` with `γ = innerAdelicPoint F G g`.

The remaining results assume that `G.X.left` is affine and that `G.X.hom`
is locally of finite type. They take a subgroup functor `V` of `G` whose
evaluated adelic subgroup is closed and whose actual rational quotient is
compact. The second subgroup functor `U` is supplied with its own closedness
instance and an equation `hU : U = V.comap (G.innerIso g).hom`. Supplying
the equation, instead of writing the inverse image inside the statement,
keeps the instances of a consumer's chosen `U` unchanged.

`constantTerm_comap_innerIso` proves, for every continuous rational-invariant
function `f` and every adelic point `y`, that the constant term along `V`
at `y` equals the constant term along `U` at `γ⁻¹ * y`. Both constant terms
use the intrinsic mass-one measures `normalizedRationalQuotientHaarMeasure`.
The Lean proof substitutes `hU` and rewrites the `V` integral with
`AdelicSubgroupPoints.integral_comp_rationalQuotientIso` for the isomorphism
`G.innerIso g`. That identity, from the `AdelicSubgroupQuotientTransport`
module, pulls the integral back along the rational quotient homeomorphism.
It is an equality of totalized Bochner integrals, so no integrability
premise is needed. Then the two integrands agree on every representative `u`
of the source quotient. The transported representative is `γ * u * γ⁻¹`.
By associativity, the function is evaluated at `γ * (u * (γ⁻¹ * y))`. Since
`γ` is the image of a rational point, left rational invariance of `f`
removes it.

`forall_constantTerm_eq_zero_comap_innerIso_iff` then shows that the
constant terms along `V` vanish at every adelic argument exactly when those
along `U` do. The forward direction evaluates at `γ * y`; the reverse
direction applies the hypothesis at `γ⁻¹ * y`.

The provenance is internal. The module combines the published inner
automorphism, constant point, constant term and rational invariance APIs
with the quotient measure transport for group-scheme isomorphisms. No
literature theorem is invoked. It does not identify rational parabolics or
their radicals up to conjugacy and proves no iterated-period formula.
