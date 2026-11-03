# The all-test semigroup commutator weight bound

`Langlands.GroupScheme.RelativeRoot.semigroupCommutator` proves the unchanged
`SemigroupCommutatorStatement.{u}` at every universe `u`. For a smooth affine
group over any field with an actual split-torus action, the commutator of an
`A`-point and an `A'`-point on every test scheme lies in the actual semigroup
subgroup for `semigroupSum A A'`. This sum consists of one weight from each
additive subsemigroup. The semigroups may be empty and need not contain zero.

The source route is Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second
edition (2015), Lemma 3.3.4 and Proposition 3.3.5, printed pp.108–109 / PDF
pp.134–135, as used in Proposition 3.3.6. The registered source is
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.

The first lemma isolates the geometric argument, with pointed-image generation
and coordinate/Lie containment as explicit inputs. An admissible pair of
subgroup functors has smooth connected closed representatives `H` and `K`.
Their actual restricted actions have augmentation support in `A` and `A'`
by coordinate/Lie containment and equivariant monomorphism transport.

Apply pointed generation to the commutator on the original smooth connected
product `H.X ⊗ K.X`. This gives a smooth affine geometrically connected
representative `D` of its closed envelope and a dominant positive ordered
power. Equivariance makes the envelope stable. The actual affine commutator
image has augmentation support in the literal sum `A+A'`: the two identity
slices eliminate the pure tensor summands, leaving one augmentation weight
from each factor. The canonical pointed equivariant morphism from this image
to `D` comes from schematic source descent. Its corresponding ordered power
is dominant. Smoothness makes `D` reduced, so dominant pullback and the
finite-power support theorem give its augmentation support in the same sum.
Coordinate/Lie containment and monomorphism transport make the actual range of
`D.inclusion` an admissible generator. Every original commutator on every
test scheme factors through this range.

The final theorem supplies the proved `ImageGeneration.pointedImageGeneration`
and the containment component of `CoordinateWeights.coordinateSemigroupComparison`.
It then applies `semigroupSubgroup_commutator_of_generatorBound`, which extends
the bound through both subgroup closures. The literal sum absorbs an additional
weight from either semigroup, supplying normalization for that extension.
No proposition premises remain on the final theorem. Its field,
characteristic, universe and test-scheme quantifiers are the published ones.
