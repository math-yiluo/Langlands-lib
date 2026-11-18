# Actual roots of compatible tori in product factors

This derived internal comparison works with the actual factor maximal torus,
ambient-torus insertion and split projection constructed by
`SimplyConnectedAlmostSimpleProduct.factorMaximalTorus`. It identifies roots
as actual characters; no abstract replacement root system is introduced.

The original inclusion and projection remain a retraction on actual
Lie kernels. A projection to another factor kills the entire differential
image of a factor. Every ambient root weight lies in the Lie-image of the
unique factor carrying its root subgroup: the weight is contained in that
root subgroup's tangent space, then in the factor tangent space.

For a factor root `β`, pullback along the split torus projection is nonzero.
A nonzero `β`-weight vector lifts through the group-factor projection to a
vector of the same ambient weight, using the published split-torus coefficient
preimage theorem. Its nonzero projected image forces that ambient root to
belong to this factor. Conversely, a nonzero weight vector of any ambient
root assigned to this factor has nonzero projection to it. The actual
split-torus restriction theorem then recovers a factor root whose pullback
is the original character.

`FactorMaximalTorus.rootEquiv` packages the resulting full root bijection.
Its forward map is literal character pullback along the actual projection.
The all-test group retraction gives injectivity, and the reverse weight
argument gives surjectivity. The field, characteristic and universe are
unrestricted. Cartan/coroot and base comparisons are separate obligations.
