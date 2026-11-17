# Geometry of represented etale images in separated sheaves

This internal result is derived from the published diagonal and represented-image
APIs. It does not invoke the separated etale schemehood criterion being proved.

An affine scheme over the fixed base has closed diagonal. A fibre product of it
with a sheaf having closed diagonal also has closed diagonal, by the product and
monomorphism lemmas of `PullbackDiagonals`.

For a represented sheafified image of an affine etale chart, Yoneda supplies the
map to the scheme base and the etale surjective map from the original chart.
The representing scheme has closed diagonal because its image inclusion is a
monomorphism into the separated sheaf. Its induced base morphism is separated.
Since the base is affine, this representing scheme is absolutely separated; the
map from the affine chart is therefore quasi-compact. Smooth source descent and
formal-unramified source descent show that the induced base map is etale.
