# Surjectivity of torus Iwahori subgroups

Author: Worker 1587.

`Langlands.Geometry.Building.torusIwahoriSurjectivity.{u}` proves exactly
`Langlands.Geometry.Building.TorusIwahoriSurjectivityStatement.{u}`. It uses
the actual maximal unramified extension `UnramifiedClosure F`, the given finite
Galois intermediate field `L`, its prescribed `intermediateValuation F L`,
and the Library subgroup `torusNormIwahori`. The field universe is arbitrary,
and the base local field may have either characteristic. The statement and
its imports are unchanged.

## Source and proof route

The source is Tasho Kaletha and Gopal Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`. Definition 2.5.13, printed
page 90 / PDF page 121, defines the Iwahori subgroup as the norm image of the
bounded subgroup over a finite Galois splitting field. Lemma 2.5.20(1),
printed page 91 / PDF page 122, asserts surjectivity for an exact sequence
of tori. Its proof on printed page 92 / PDF page 123 tensors the
cocharacter sequence with the coefficient group giving integral torus
points. The multiplicative calculation uses the units of the valuation
ring; the printed proof writes the valuation ring itself.

The published target retains the splitting and cocharacter-surjectivity
properties used by that argument. The implemented proof constructs a section
over the splitting field directly. This is a derived route to that target,
rather than a formalization of the tensor calculation.

The authors' corrections of 1 November 2024, registered as
`kaletha-prasad-2024-corrections`, PDF pages 24–25, were read. They do not
change Definition 2.5.13 or Lemma 2.5.20. The corrected sign of the
character-valuation map leaves its kernel unchanged. No project errata file
for these sources was found.

## Implemented proof

The auxiliary theorem
`IsSplitTorus.exists_section_of_surjective_cocharacters` works over an
arbitrary scheme base. For a commutative-group-scheme morphism `f : T → U`
with split target `U`, identify `U` with a finite product of copies of
`Gm`. Lift each coordinate cocharacter through `f`, using the given
surjectivity. Compose the coordinate projections with the chosen lifts,
sum these morphisms, and transport back to `U`. The Library identity
`splitTorus.sum_proj_comp_single` proves that this morphism followed by
`f` is the identity. The empty product is covered by the same finite-sum
identity. This argument requires no splitting assumption on `T`.

The second auxiliary theorem,
`map_torusNormIwahori_eq_of_cocharacter_surjective`, applies this construction
to the actual base change of `f` to a finite Galois extension `L/k`.
For any valuation `v` of `L`, the published
`map_torusNormIwahori_le` gives one inclusion. For the other, express a
target element as the norm of a point `x` in the target
`characterValuationKernel`. Apply the section to `x`.
`map_characterValuationKernel_le` places the result in the source kernel.
Its norm is the required preimage, because
`GaloisPointComparison.rationalNorm_naturality` and the section identity
identify its image with the original target norm.

The section is used only over `L`; no descent of that section to `k` is
asserted. No Galois invariance of `v` or valuation on `k` is needed for
this norm-image argument.

The final theorem specializes this result to `k = UnramifiedClosure F`
and the exact intermediate field and valuation in the published statement.
The source-splitting hypothesis is retained in its exact type even though
the stronger auxiliary result does not need it. No exact sequence,
kernel, smoothness, connectedness or additional splitting premise is added.
