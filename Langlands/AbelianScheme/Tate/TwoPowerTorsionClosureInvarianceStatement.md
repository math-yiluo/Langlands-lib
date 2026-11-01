# Multiplication invariance of the actual two-power torsion closure

`TwoPowerTorsionClosureInvarianceStatement` asserts that, for every algebraically
closed characteristic-zero field `K : Type u` and every actual bundled abelian
scheme `A` over its spectrum, the Zariski closure of `twoPowerTorsionLocus A`
equals both its full inverse image and its image under the actual multiplication
by two morphism.

The locus and group operations are exactly those in
`FieldTwoPowerTorsionDensityStatement`: a point is represented by an actual
section over the identity test scheme that is killed by some power of two.
The first equality concerns every point of the scheme-theoretic morphism's
underlying topological inverse image, including points that were not given as
field-valued sections. The second equality concerns the underlying topological
image.

This is a derived intermediate statement motivated by the torsion-closure
argument in Edixhoven, van der Geer and Moonen, *Abelian Varieties*, Chapter V,
section 3, Theorem (5.30), printed page 84 / PDF page 88, registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`. It is not a transcription
of a separate assertion in that source. It isolates the invariance supplied by
actual section divisibility, Jacobson closed-point density, and finite étale
multiplication. The declaration defines a proposition and supplies no proof.
It asserts neither density, a numerical torsion formula, nor a closed subgroup
scheme structure on the closure.
