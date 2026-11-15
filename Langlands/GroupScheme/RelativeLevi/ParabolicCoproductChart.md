# Actual parabolic families on scheme coproducts

Let `S` be an arbitrary scheme in universe `u`, let `G` be reductive over `S`,
and let `V : I → Over S` be a family indexed by `I : Type u`. Suppose that
each `V i` carries an actual parabolic subgroup functor `F i` of the pullback
of `G`.

`coproductParabolic` constructs an actual parabolic subgroup functor over the
scheme coproduct `sigmaOver V`. Its restriction to the `i`th component is
exactly `F i`. `existsUnique_coproductParabolic` proves uniqueness with this
property. The family may be infinite and the base need not be affine.

The proof uses the published Zariski sheaf property of the actual parabolic
presheaf. First `parabolicSubsingleton_of_isEmpty` detects equality using the
empty open cover of an empty parameter scheme. To check compatibility on the
coproduct components, equal indices give equal restriction morphisms by
monicity of the component inclusion. Distinct indices force the common test
scheme to be empty, by disjointness of scheme coproducts, so its two parabolic
sections agree. The component inclusions generate a covering sieve, and the
sheaf condition then gives the unique glued family.

`coproductParabolicChart` is the natural transformation from the actual functor
of points of `sigmaOver V` to `parabolicPresheaf G hG` obtained from this
family by the lifted Yoneda correspondence. The theorem
`coproductParabolicChart_app_comp` computes its value on a parameter morphism
factoring through one component: it is the restriction of that component's
prescribed family.

This is an internal construction from the published actual parabolic sheaf
and scheme coproduct APIs. It introduces no additional mathematical premise.
It gives neither injectivity nor surjectivity of the total chart, and makes
no smoothness or properness assertion. Those require further hypotheses on
the component charts and their coverage.
