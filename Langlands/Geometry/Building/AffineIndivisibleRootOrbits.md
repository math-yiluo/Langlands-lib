# Indivisible affine roots and chamber-simple roots

`IsSimpleRootConjugate Ψ C ψ` means that pullback of `ψ` by some
root-preserving affine automorphism is a simple affine root of `C` or
its negative. This predicate is defined for any set `C` of affine points.

This internal supporting unit refines the existing Library gallery proof:
a coroot reflection is conjugate, by chamber wall reflections, to a wall
reflection of any prescribed regular chamber. The proof follows the generic
hyperplane point, nearby regular point and gallery construction already
implemented in `AffineReflectionGalleryGeometry.affineReflection_mem_closure`,
retaining its intermediate conjugacy witness.

The coroot-integrality argument already implemented for proportional simple
roots in `AffineChamberCartanMarks` applies to all indivisible affine roots:
a positive proportionality factor is one. Negation and root-preserving
pullback preserve indivisibility. The conjugate-wall witness and this
proportionality result show that every indivisible affine root is carried,
up to sign, to a simple affine root of the prescribed regular chamber
by pullback along a root-preserving affine automorphism.

This is derived infrastructure on a supplied affine root system, including
rank zero and independent translation-space and torsor universes. It asserts
no actual-group or unconditional full derivative symmetry result.
