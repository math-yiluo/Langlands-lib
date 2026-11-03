# Containment from fixed rational cosets in one Borel quotient

`factorThroughBorelOfFixedQuotient` constructs an actual factor through any
Borel; `range_le_all_borels_of_fixed_quotient` records its consequence for
subgroup functors. These are internal conditional adapters for the flag step. Over an algebraically closed field in any universe, let `G` be
smooth, connected and affine, let `b₀ : B₀ ⟶ G` be one Borel subgroup, and let
`i : U ⟶ G` be a closed subgroup. Supply a relative scheme `Q`, a morphism
`q : G.X ⟶ Q`, the exact right-coset fiber criterion on every scheme test,
and an actual `SchemeAction G Q` satisfying the multiplication formula on
lifted cosets. If every rational point of `Q` is all-test fixed under the
restricted `U`-action, the exact `BorelConjugacyStatement` supplies a morphism
`f : U ⟶ B` with `f ≫ b = i` for any Borel `b : B ⟶ G`. Consequently
`range i` lies in every Borel subgroup functor on every test scheme.

The construction uses classical choice to choose a factor from the existence
argument. The proof uses conjugacy to write `b₀ ≫ int(g) = φ.hom ≫ b` for an arbitrary
Borel `b`. Fixedness of the rational coset `g ≫ q` gives the all-test coset
equation required by `factorOfFixedCoset`. The resulting morphism `f : U ⟶ B₀`
satisfies `f ≫ b₀ = i ≫ int(g⁻¹)`. Composing with `φ.hom` cancels the two inner
automorphisms and factors `i` through `b`. The existing
`SubgroupFunctor.range_le_of_factor` yields containment on all test schemes.

The provenance is internal: this is a composition of the published Borel
conjugacy interface, fixed-coset factorization, and inner-automorphism
identities. Conjugacy and fixedness remain explicit hypotheses. The result
does not establish quotient existence, properness, invariant affine
neighbourhoods, or the generic fixedness argument, and it does not complete
the unconditional flag-step target.
