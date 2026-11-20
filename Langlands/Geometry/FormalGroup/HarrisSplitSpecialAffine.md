# Affine split-special polarized framed classes

The affine polarized framing problem uses the actual order
\(O_D^{\mathrm{op}}\times O_D\) with the exchange involution,
and the underlying \(\mathbf Z_p\)-formal law. The coefficient
ring is an \(O_F\)-algebra with compatible \(\mathbf Z_p\)-scalars.
Reduction uses the image of the specified element of \(O_F\),
which is the uniformizer in the moduli problem. The frame is a
specified polarized object over the residue coefficient ring.

`HasSplitSpecialTangent` imposes the special condition on the
image of \((0,1)\) on the actual target tangent. The central
\(O_F\)-action on that summand is structural over the entire test
ring, and the embedded unramified integer subfield has its
distinct characters with multiplicity one on geometric fibers.
The embedded integer ring is the one supplied by `SpecialModule`,
with the full reduced-degree and unramified condition. In
particular the dimension of the division tangent is the reduced
degree of \(D\).

`splitSpecialAffineFunctor` takes the classes in the affine
polarized framing functor with this special tangent condition.
Actual target isometries preserve the condition. The maps extend
the target and the actual framing section along the Nilp map.
The identity and composite isometries of the polarized functor
give the corresponding laws on these classes.

Harris (1997), Appendix, printed pp. 112–113 (PDF pp. 38–39),
uses the three polarized framing conditions. For the tangent
condition on the division factor this construction follows
Rapoport–Zink (1996), Definition 3.57 and §3.58, printed
pp. 109–110 (PDF pp. 123–124), and their use of the split
determinant condition in §6.43, printed pp. 308–309
(PDF pp. 320–321). The construction uses single finite-coordinate
objects on affine tests and a fixed supplied residue frame.
