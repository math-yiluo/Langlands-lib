# Adjusting a trivialization along a section

This is an internal categorical construction for actual rigidified line bundles.
It uses the published pullback functors, their composition and identity
comparisons, and the canonical pullback isomorphism for the structure sheaf.
It uses no geometric representability or rigidity assertion.

For a scheme morphism `f : X ⟶ S` and a section `ε : S ⟶ X` satisfying
`ε ≫ f = 𝟙 S`, `RigidifiedLineBundle.trivialIsoOfCarrierIso` takes an
actual rigidified line bundle `L` and an actual isomorphism of its underlying
module sheaf with `O_X`. It constructs an isomorphism with the canonically
rigidified trivial line bundle. The supplied ordinary isomorphism need not
already respect the rigidifications.

The auxiliary construction `RigidificationAdjustment.liftAutomorphism`
works for functors `F : C ⥤ D` and `G : D ⥤ C` with a specified natural
isomorphism `G ⋙ F ≅ 𝟭 D`. At an object `A` isomorphic to `G.obj B`,
it lifts any automorphism of `F.obj A` to an automorphism of `A`.
`map_liftAutomorphism` proves that applying `F` recovers the given
automorphism. Its proof is naturality of the specified natural isomorphism
followed by cancellation of inverse maps. The auxiliary `adjustIso`
postcomposes an isomorphism with that lift, and `adjustIso_compatible`
proves the prescribed compatibility after applying `F`.

For the line-bundle construction, `F` is pullback along the section and
`G` is pullback along `f`. The section law gives the required natural
isomorphism. The structure-sheaf pullback comparison identifies `O_X`
with `G.obj O_S`. Comparing the pullback of the supplied trivialization
with the two rigidifications gives an automorphism of `F.obj O_X`.
Lift that automorphism and postcompose the trivialization with it.
The proved recovery equation gives compatibility with the rigidifications,
so the published `RigidifiedLineBundle.isoMk` constructs the result.

This construction has no smoothness, properness, connectedness, field,
tensor-invertibility or Picard representability assumption. It does assume
the supplied ordinary trivialization; it does not prove the geometric
theorem of the cube or triviality of an arbitrary line bundle.
