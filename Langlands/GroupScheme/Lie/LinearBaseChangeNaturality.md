# Naturality of the linear Lie-kernel base-change comparison

`Lie.kernelBaseChangeLinearEquiv_target` is the existing ring-general theorem
moved from `CentralIsogeny.GeometricSemisimpleKernel` into shared Lie
infrastructure. Its declaration name, parameter order, hypotheses and proof
are unchanged. The field-specialized copy in `Geometry.Building.RootPointLieFieldExtension`
uses this common theorem.

For commutative rings `k` and `K`, an algebra structure `Algebra k K`, affine
group schemes `G` and `Q` over `k`, and a compatible coefficient-algebra tower
`k → K → A`, the linear comparison between the actual Lie kernel of a base
change and the original Lie kernel commutes with the differential of every
morphism `q : G → Q`. The proof applies `Additive.ofMul` to the existing
multiplicative tangent-kernel naturality identity.

This is an internal transport lemma with no new mathematical assertion or
literature claim. Both central-isogeny and root-point consumers retain their
original hypotheses and conclusions.
