# The subgroup of translations preserving a morphism

For a group scheme `G` over `S` and an `S`-morphism `f : G → Y`,
`Langlands.GroupScheme.translationStabilizer f` is a subgroup functor of `G`.
A parameter `a : T → G` belongs to the functor when for every `S`-scheme
`V` and maps `x : V → G` and `t : V → T`, the two composites of
`x · (t ≫ a)` and `x` with `f` are equal. The functor uses right translations,
without requiring that `G` be commutative or that `Y` be a group. Successive
translations preserve `f`, and testing at `x · (t ≫ a)⁻¹` proves closure
under inverses. Alternatively, membership is equality of the two maps
`G ×[S] T → Y` given by these formulas on the two projections
(`mem_translationStabilizer_iff_morphism`).

Suppose now that `S = Spec K` for `K` algebraically closed, `G` is
reduced and locally of finite type, and `Y` is separated over `K`.
By `mem_translationStabilizer_iff_rational`, one can test membership by
comparing the same maps on `T`-valued slices through the rational points
of any dense open of `G`. This is equality as scheme morphisms, even
when `T` is nonreduced. The rational-slice criterion compares the maps
on `G ×[K] T`, using the constant lift of each rational point in the first
factor.

`translationStabilizer_isClosedRepresentable` uses all rational points
of `G` to construct a simultaneous closed equalizer in the translation
parameter scheme `G`: the equation at `x` compares `f(x · a)` with
`f(x)`. The preceding criterion and the equalizer's universal property
identify all points of that closed subscheme with the subgroup functor.
`RepresentabilityTransfer` gives it its group law and makes the inclusion
a group homomorphism. If `f` is finite, evaluating the preservation
condition at the unit shows that the stabilizer inclusion factors through
the fibre of `f` over the rational image of the unit. This is a closed
immersion into the fibre: its composite into `G` is the closed subgroup
inclusion, and the fibre inclusion is separated. The fibre is finite
by base change, so the subgroup scheme is finite as well
(`exists_finite_translationStabilizer`). No étaleness is asserted.

This is an internal construction used in the proof of cubic separation.
It combines the Library's subgroup representability transfer with
scheme-theoretic rational-slice detection and simultaneous closed
equalizers. It represents the stabilizer of the actual morphism, not
the subgroup preserving only the isomorphism class of a line bundle.
