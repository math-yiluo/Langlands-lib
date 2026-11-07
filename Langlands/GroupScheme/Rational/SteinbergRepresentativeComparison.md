# Torus comparisons of supplied reflection representatives

Worker 1317. Internal supporting constructions derived from the published
split-torus character-separation, maximal-torus self-centralizer, actual vector
coordinates and canonical class-function quotient interfaces.

Two supplied representatives of the same simple reflection induce the same
actual torus automorphism, since characters of a split torus separate its
homomorphisms. Their quotient centralizes the entire torus. The published
maximal-torus self-centralizer theorem identifies that quotient with a unique
rational torus point. `SimpleReflectionRepresentative.torusRatio` chooses that
point and its compatibility theorem records equality in the actual group.

Root values of a family of rational torus points scale the standard affine
coordinates through an actual group-scheme isomorphism `torusScaleIso`. The
inverse uses the inverse torus points; naturality is checked on every test
scheme using global functions.

`CyclicTorusGauge` retains explicit successive torus points relating the two
ordered representative families, with equal first and last torus points.
Under these supplied data, multiplication telescopes: the scaled second
Steinberg product is conjugate to the original product. The implemented proof
uses the supplied root maps' full torus equivariance and an elementary ordered
group-product identity. Conjugation invariance of `ClassFunctions.rho` then
identifies the canonical quotient composites after the diagonal coordinate
isomorphism and proves equivalence of their isomorphism properties.

All results preserve arbitrary universes and fields, including finite and
imperfect fields in positive characteristic. Existence of a cyclic torus gauge
is not asserted. The unit does not prove independence for arbitrary reflection
families, invariant-algebra generation, or the split Steinberg quotient target.
