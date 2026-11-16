# Actual finite Čech systems on compact objects with action lifts

This internal adapter constructs `compactCompatibleCechSystem` for the ordinary
quasi-étale topology. Its test objects are free module sheaves on the
`CompactLiftBasis`: compact quasi-étale objects that admit actual continuous
action lifts. Its covers are precisely `CompactCompatibleCover`, retaining
source and target lifts and their equivariance on a common open subgroup.

The construction assumes the target comparison's finite equivariant refinement
instance. It also assumes local smallness in the coefficient universe, module
sheafification, and the local-bijectivity characterization used for lifting
coefficients. The remaining geometric input `p` supplies an actual finite
coproduct presentation by representables from this same basis for every
presheaf nerve term of every compatible cover, in every nonnegative degree.
The construction does not assert the existence of these presentations.

The actual free Čech augmentation is a quasi-isomorphism by
`quasiIso_freeCechAugmentation_of_locally_surjective`: the underlying finite
cover is locally surjective. Consequently its zero component is epimorphic,
its augmented sequence is exact, and the chain complex is exact in every
positive degree. Thus no unproved Čech exactness proposition is an input.
Applying the free sheaf functor to `p` and using preservation of coproducts
supplies the finite chain-term presentations.

For local lifting through a short exact coefficient sequence, choose one of
the target object's existing action lifts. The previously constructed
compatible-cover lifting theorem provides a compatible cover and a lift on
its actual degree-zero Čech term. Its equality is exactly the local lifting
field of `FiniteCechSystem`. The selected target lift need not be uniform
across different lifting problems.

The provenance is internal: this is a specialization of the generic finite
test-system interface using the established compatible-cover refinement and
local exactness constructions. It restricts the cover family to compatible
covers rather than requiring all finite covers. Higher nerve presentations,
Hom acyclicity of restricted injective equivariant coefficients, and the
unconditional analytic comparison remain to be proved.
