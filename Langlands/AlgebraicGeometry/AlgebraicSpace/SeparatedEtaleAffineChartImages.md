# Represented images of affine structurally etale charts

This internal consequence of `SeparatedEtaleImageDescent` represents the local
image of an affine etale chart whose composite to an affine scheme base is
etale. The target is an fppf sheaf with closed diagonal.

The graph of the chart into its pullback along that composite is open. To prove
this, the self-relation of the etale composite maps etale to the pullback, by
base change of the original chart. Its diagonal is open and composes to the
graph, making the graph etale. The graph is monomorphic because its second
projection is the identity. Every represented projection is thus a flat
monomorphism locally of finite presentation, hence an open immersion.

The compact image descent theorem applies to this affine open graph chart with
identity structural composite. Its image in the original sheaf equals the
original chart image, giving the claimed compact representation. All inputs
are published APIs or the separately submitted image descent extension.
