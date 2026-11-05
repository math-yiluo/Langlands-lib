# First-order assembly of the actual auxiliary characters

Worker 84 implements a proof of the existing AuxiliaryCharacterStatement in
independent universes. The exact proof task has formal requirements on its
separate prerequisite proof tasks; all such dependencies are imported by Lean
name and must be independently public in the admitted Library. Development
compilation alone is not independent acceptance, publication or H2 completion.

Choose a nontrivial continuous additive unitary character on the base field and
a nonzero primitive intermediate coefficient b with exact trace stabilizer.
The constructed norm-coordinate family supplies an offset C and finite-order
characters at each positive level k, with chi(N(1+p^k*y)) equal to
psi_F(p^(C-k)*Tr(M/F)(b*y)) and actual norm subgroup membership. Integral linear
witnesses and finite coefficient separation give one threshold for all unwanted
trace differences. A separate nonzero weighted-trace functional gives a threshold
for detecting a nontrivial character value. This additional detector handles the
case with no unwanted automorphisms as well.

Choose k=C+N1+N2+r+1 and N=k-C. Both detection thresholds apply and r<k.
Transport the constructed character from its supplied intermediate topology to
the actual subtype topology in the target using the proved module-topology
comparison. The underlying homomorphism is unchanged, so its finite positive
annihilating exponent remains valid. The coordinate formula and unwanted
trace-difference detectors feed the exact actual valuation-unit stabilizer lemma.
Automorphisms fixing L preserve its actual norm; every unwanted automorphism
has a norm-one coordinate unit distinguishing its two pullbacks.

The independent weighted-trace detector supplies an integral y whose coordinate
unit z gives chi(Nz) nontrivial. Its norm x belongs to principalUnits(k*e_L).
The exact scalar valuation bounds v(x-1) by v(p^k). The actual integer-ring norm
comparison then bounds the canonical intermediate norm of x-1 by p^(-k).
The intermediate/ambient canonical norm comparison changes this to the actual
ambient norm in the target, and r<k gives the strict requested p^(-r) bound.
Thus the same finite-order character satisfies depth nontriviality and the exact
norm-pullback stabilizer.

This route uses first-order principal-unit coordinates and the integral quadratic
norm error, with no logarithm/exponential, division by two, odd-prime restriction,
reciprocity premise or assumed exact stabilizer. It retains every supplied field
and the target's actual norms, trace and pointwise fixing subgroup. The internal
route does not attribute a stronger proof to the original literature; original
source qualifications remain documented in the unchanged target Markdown.
All helper pairs describe their implemented arguments and separate dependencies.
