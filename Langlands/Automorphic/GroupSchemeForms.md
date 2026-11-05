# General reductive forms on the original finite-smooth carrier

This module constructs a broader finite-smooth form space on the existing
actual continuous rational-invariant adelic functions. Its carrier has
smooth infinite slices and one common open finite stabilizer. The
compact-open existence theorem proves that this stabilizer condition is
equivalent to actual compact finite level for affine groups locally of
finite type over the number field, by intersection with the constructed
compact open subgroup.

For a specified infinite subgroup, `IsAdelicInfiniteFinite` requires the
complex span of translates of the entire function to be finite
dimensional. The actual center is `Subalgebra.center` of the existing
complex identity-tangent universal enveloping algebra, acting through
the existing differential action with its explicit scalar-commutator
premise. `IsAdelicCenterFinite` requires one finite-dimensional global
center orbit. The linear orbit map and its kernel quotient prove the
equivalent formulation with one finite-codimensional ideal annihilating
the entire function. Separate slice-dependent ideals are not used.

`IsAdelicAutomorphicForm` combines these finiteness conditions with the
exact full adelic moderate-growth bound on the original finite-smooth
carrier. The subrepresentation takes explicit connected reductivity,
a closed matrix representation of positive dimension and a specified
maximal compact infinite subgroup. The bound and finiteness conditions
are motivated by GH Definition 6.3.3, printed p.163 (physical PDF p.177),
and Definition 6.3.1, printed pp.161--162.

This does not identify the construction with the literal GH form space.
GH (6.1), printed p.158 (physical PDF p.172), explicitly uses the algebraic
tensor of infinite and finite smooth functions, and p.162 defines
derivatives through finite tensor decompositions. The carrier here has
no global finite-tensor condition, and no theorem in this module shows
that the form conditions imply it. The geometric premises do not supply
that missing comparison. The declaration names refer to the broader
finite-smooth construction; literal GH smooth-space comparison remains
an exact construction/proof obligation.

Finite adelic translation commutes with the infinite-factor action,
intertwines the actual center action and preserves full adelic growth.
This gives a complex finite adelic subrepresentation with an injective
equivariant original-function realization. Connected reductivity
supplies local finite type through smoothness, so every vector has
actual compact finite level. The finite action is proved smooth through
open vector stabilizers. The theorem named `..._iff_source_conditions`
expands exactly the implemented compact-level, common-ideal and growth
conditions; it asserts no literal GH tensor membership. The optional
uniform refinement intersects with the earlier extended one-exponent
bound space on the same carrier.

This is a derived construction using the existing actual carriers,
finite-vector API, differential action, full growth and compact-open
results. It does not prove literal GH tensor comparison, automatic
uniform growth, full infinite translation stability, embedding
independence, maximal compact existence/conjugacy, admissibility or
comparison to the original matrix automorphic form space.
