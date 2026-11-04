# Actual rational geometric compact comparison

This internal derived construction specializes the published compact split-stage
integral to the original rational-point parabolic intersections and identifies
its coefficient with the actual source-intersection Jacquet quotient. It retains
the actual subgroup-to-kernel Haar character. It is an unnormalized compact
comparison for the rational geometric lemma.

For the original standard subgroups P_I, M_I, U_I and P_J, M_J, U_J and every
actual torus-normalizer point n, put Q = P_I and L = M_I. Write
H = (P_I intersect n P_J n^-1).subgroupOf P_I and
K = (M_I intersect n P_J n^-1).subgroupOf M_I. Let r be the original I Levi
projection, s its original Levi inclusion, and P = geometricSplitIntermediate,
the inverse image of K under r. Let HP = H.subgroupOf P and phi be the
canonical equivalence HP to H. The homomorphism f : H to M_J is the original
J Levi projection after inverse conjugation. The restricted retraction is
rP = Induction.splitStagesRetraction r s ... P, with section
sP = s.subgroupComap P. The declarations geometricCompactKernel and
geometricCompactKernelIntersection name precisely N = rP.ker and
D = HP.comap N.subtype. These are the literal nested subgroups, with their
induced topologies.

Let S = (M_J intersect n^-1 U_I n).subgroupOf M_J and
Ls = (M_J intersect n^-1 M_I n).subgroupOf M_J. The source and target
intersection semidirect decompositions supply the actual projected map
p : K to Ls, including inverse conjugation. For a smooth complex
representation sigma of M_J, geometricCompactCoefficient is the representation
of the whole K

`twist chi ((Jacquet.action sigma S Ls hSource.levi_le_normalizer).comp p)`.

Here chi = geometricCompactHaarCharacter is literally the complex character of
Induction.splitKernelHaarRatio rP sP HP, pulled back along the inverse of
geometricSplitQuotientEquiv. That equivalence identifies P.comap s with K
without changing the original Levi point. For inverse conjugation by the
section, splitKernelHaarRatio is the automorphism Haar character on D divided
by that on N. The present construction keeps this character with this
orientation; it does not identify it with a half-modulus.

geometricCompactSource is the representation
`((compactInduced H (sigma.comp f)).toCoinvariants r.ker).comp s`, on the
actual ambient-kernel coinvariant module. geometricCompactTarget is
`compactInduced K geometricCompactCoefficient`. The entry definition
geometricCompactEquiv is an L-representation equivalence between these two
representations. Its forward map composes Induction.splitStagesCompactEquiv,
transport of the inducing subgroup along geometricSplit_comap_section, and
compact induction of the twist of geometricSplitCoefficientEquiv. The private
generic compactInducedSubgroupTwistCongr transports both the coefficient and
the character; its evaluation lemma says it preserves the original compact
function. Equality induction proves these two private declarations.

The structural scope retains an arbitrary field k, an affine structural
morphism for G, connected reductivity, the actual maximal split torus and
generic cocharacter, StandardCocharacterStatement, HasPointNormalizerComparison,
arbitrary I and J, every normalizer point n, both original Levi decompositions,
and the source and target intersection decompositions. The complex module
carrier universe is independent of the field universe. The rational-point
group has any Hausdorff locally compact topological-group topology. The
construction takes closedness of P_I, P_J and M_I and continuity of the two
original Levi projections. Closedness of P_I supplies local compactness of Q;
continuity of r into the Hausdorff Levi gives closedness of its kernel.
Smoothness of sigma.comp f follows from projection continuity and smoothness
of sigma by the private geometricCompactPullback_smooth.

The measure premises are local compactness and Borel structures for N, Borel
structures for D and D \ N, regular left Haar measures muN and muD that are
also right invariant, and a compatible quotient measure on D \ N finite on
compact sets. Regularity is supplied as named hypotheses and installed locally.
Compact open subgroup neighborhood bases are supplied for N and Q. These are
the hypotheses of the imported relative integral and compact comparison.
There is no local-field, minimal-representative, Coxeter, finite-length or
finite-dimensional premise here, and no representation comparison is assumed.

geometricCompactIntegrand F l is the finite-image simple function on D \ N
obtained from Induction.quotientCoinvariantSimple of the actual kernel slice
by the linear map of geometricSplitCoefficientEquiv. The theorem
geometricCompactIntegrand_mk states its exact value at the class of q : N:

`Jacquet.mk sigma S (eval H (sigma.comp f) F.val (((q : P) : Q) * s l))`.

Thus the vector before taking its Jacquet class is the identical original
value F(q*s(l)). The theorem geometricCompactEquiv_eval_mk_integral states
that geometricCompactEquiv applied to the ambient-kernel class of F, evaluated
at l, is exactly AlgebraicIntegral.integral of this simple function against
the supplied compatible quotient measure. The proof composes the explicit
subgroup-transport evaluation equality with
Induction.splitStagesCompactEquiv_eval_mk_integral. Finally
AlgebraicIntegral.integral_linearMap, using the finite-measure support theorem
for quotientCoinvariantSimple, moves the coefficient equivalence through the
integral. There is no additional scalar in this formula; the retained Haar
ratio occurs in equivariance of the target coefficient.

All declarations are internal compositions of published constructions, rather
than statements attributed verbatim to literature. Direct proof dependencies
are SplitStagesComparison, its representative integral formula,
RationalGeometricSplitCoefficient and its original-vector class formula,
compact coefficient postcomposition and twist transport, and the algebraic
simple-function integral linear-map theorem. Transitively the actual coefficient
comparison uses the stabilizer projection and kernel image, closed stable
dynamic limits and elementary image-coinvariant transport, as documented in
the imported pairs. Import closure is broader than these proof-body
dependencies. No proof invokes the geometric expansion, adjointness, character
independence, cuspidal-support or Langlands-classification theorem, or Aubert
Proposition 3.2 and its defective original application.

The two Haar corrections, balance of positive and inverse half-moduli on the
actual distinct radicals, compact/full induction, actual naturality and smooth
functor packaging, the ordered orbit filtration and the exact unapplied K0
expansion remain separate obligations. This pair establishes the compact
representation equivalence and its integral formula only.
