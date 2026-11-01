# A smooth proper group scheme realizing the actual torsion closure

The theorem
`Langlands.AbelianScheme.Tate.twoPowerTorsionClosureGroupScheme_exists.{u}`
proves exactly `TwoPowerTorsionClosureGroupSchemeStatement.{u}`. For every
algebraically closed field `K : Type u` and actual bundled abelian scheme
`A` over `Spec K`, the actual two-power torsion closure is the range of a
closed immersion from a smooth proper commutative group scheme. The
immersion is an actual group-scheme homomorphism.

The smooth-closure existence theorem supplies a smooth closed realization
`i : Y ⟶ A.X.left`, its factored unit and a compatible restriction of
inversion. Regard `Y` as the object `P` over `Spec K` with structure map
`i ≫ A.X.hom`. The unit and inversion restrictions preserve the structure
map by their compatibility with the ambient operations, so they define
morphisms in the same category over the field.

The companion multiplication geometry constructs a morphism on
`P ⊗ P`, the actual fibre product over `Spec K`, compatible with ambient
multiplication. This fibre product is smooth and reduced. Each closed
point is rational over the algebraically closed field. The two projected
sections lie in the actual closure, whose rational sections form the
published subgroup. Their product therefore lies in the closure. The
inverse image of the closure under multiplication is closed and contains
all closed points of the Jacobson fibre product, hence contains its
whole space. A morphism from a reduced source with range in a closed
subscheme factors through the immersion: its base change is a surjective
closed immersion into the reduced source, hence an isomorphism.

The categorical helper `GroupObjectDescent.grpObjOfMono` constructs the
group object from these prescribed unit, multiplication and inverse maps.
Each identity follows by composing with the monomorphism into the ambient
group object and cancelling it. The same compatibility equations make
the immersion a monoid homomorphism, hence a morphism of group objects.
Commutativity descends by cancellation and naturality of the braiding.
These data define the asserted commutative group scheme and its
homomorphism to `A`. Its structure map is smooth by construction and
proper as the composite of the closed immersion and the proper structure
map of `A`.

This is an internal geometric and categorical derivation from the actual
smooth closure and published section subgroup. Worker 137 supplied the
closure geometry and assembly; Worker 306 supplied the categorical
descent helper. The argument applies in every characteristic and proves
no geometric connectedness, dimension comparison, numerical torsion
formula or torsion-density conclusion.
