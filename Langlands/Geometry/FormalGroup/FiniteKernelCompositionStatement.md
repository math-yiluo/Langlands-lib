# Finite-kernel composition and pointwise ranks: proof boundary

`Langlands.FormalGroup.ModuleLaw.Hom.FiniteKernelCompositionStatement`
is an internal proposition target, not an established theorem. It isolates
the substantial missing finite-kernel prerequisite for composition of
local quasi-isogenies and additivity of their eventual heights.

Fix any commutative coefficient ring O, any commutative O-algebra R and
three formal O-modules M, N, P with finite coordinate types. O and R may
occupy different universes. For actual formal maps f from M to N and g
from N to P, assume affine fppf local lifting for f, and take actual finite
projective algebra models K and L representing their kernel point functors.
The target asserts existence of an actual finite projective algebra model
H representing the kernel point functor of g composed with f. At every
base prime p, its rank must equal the product of the ranks of K and L at p.

The models here are exactly `Hom.FiniteKernelModel`: their coordinate
algebras come with a natural corepresentation of the actual point kernel,
not merely an assigned degree. Their ranks are actual finite-projective
module ranks at base primes. No model of the composite is an input, and
no locally constant rank is assumed constant. The target does not require
fppf local lifting for g. Both-kernel representations and lifting for f
are the hypotheses needed for the anticipated kernel extension.

The intended proof route, still unimplemented, is to construct the kernel
of the composite as the torsor over the represented kernel of g obtained
by pulling back f, and descend the actual finite locally free algebra
along affine fppf lifts. Its relative rank is the base pullback of the
rank of K; the resulting composite rank is their product. This route must
establish representability, finite projectivity and the natural kernel
comparison; composition of affine fppf lifts alone does not prove any of
these assertions. The proposition is an internal prerequisite formulated
from the existing formal-module point functors, not a quotation of a
numbered original-literature theorem or a claim of completed descent.

Three implemented conditional lemmas check the target's downstream
sufficiency. Under the explicit proposition premise they obtain isogeny
composition, multiplication of constant kernel ranks, and additivity of
heights defined by ranks q to a natural exponent. The first combines the
new model promised by the premise with the already proved composition of
fppf lifts. The second evaluates the pointwise rank formula. The third
uses the identity q^(i+j) = q^i*q^j. These lemmas do not discharge the
proposition and do not construct general local quasi-isogeny composition.

The statement does not assert nilpotent rigidity, rational-section base
change, Drinfeld or Rapoport–Zink representability, a universal object,
or any uniformization theorem.
