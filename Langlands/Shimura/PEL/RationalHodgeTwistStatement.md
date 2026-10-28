# A rational skew twist with the Kottwitz Hodge sign

Worker 57. `RationalHodgePolarizingTwistExists` is a proposition, awaiting
proof, for the actual Harris algebra and its constructed complex homomorphism.
It strengthens the published `PositiveRationalSkewTwistExists` target by
requiring the Hodge sign for the same rational skew unit.

The inputs are `CentralSimpleUnitaryData D` over the given totally real field
E and quadratic totally complex extension K, with the displayed scalar
compatibilities, and `HarrisSignatureCharts C`. The algebra structures,
second-kind involution sigma, rank greater than one, central simplicity,
finite dimension, distinguished real place and center-compatible signature
charts are retained. No new form, positive rational unit or complex
homomorphism is supplied as an input.

Let h0 be the algebra homomorphism underlying
`D.realPositiveKottwitzHom C`, already constructed on the actual algebra
R tensor over Q with A. It is the corrected Harris homomorphism precomposed
with complex conjugation. Put J = h0(i). The proposition asks for a rational
unit beta with sigma(beta) = -beta and the following properties:

- The actual auxiliary involution tau = beta sigma beta inverse is positive
  after real scalar extension, in the published regular-trace sense.
- For the actual form psi obtained by real base change of
  `(D.skewTwist beta hbeta).tracePairing beta inverse`, the real bilinear
  expression B(x,y) = psi(x,y J) is symmetric.
- B(x,x) is strictly positive for every nonzero x.

The imported scalar-extension theorem identifies this psi, with no extra
comparison assumption, as

```text
psi(x,y) = (1/n) Tr_R(L_(x sigma_R(y) (1 tensor beta inverse))).
```

Thus the target concerns the normalized rational trace form of the auxiliary
algebra and its actual base change. Right multiplication by J is the action
of h0(i) on the left regular module. It is not the inverse homomorphism on
group points used to form the Shimura datum.

The statement is derived from Kottwitz, *Points on Some Shimura Varieties over
Finite Fields* (1992), printed p.374 (PDF p.2): the symmetric form
(v,h(i)w) must be positive definite. Printed p.375 (PDF p.3) uses the inverse
homomorphism for the associated Shimura datum. Kottwitz's Lemma 2.7 and the
following notation on p.381 (PDF p.9) give the trace-form parameterization,
and Lemma 2.8 supplies its positive open-cone background. Harris–Taylor,
*The Geometry and Cohomology of Some Simple Shimura Varieties* (2001), I.7
p.52 (PDF p.60), supplies the skew-unit trace form and its conjugated right
adjoint. The normalized reduced-then-center trace, the choice of actual
Harris charts, and the conjugated Kottwitz convention are inherited from
`RationalTrace`, `TracePairing`, `PositiveInput` and `RealPositivity`.

This is an internal strengthening in that fixed specialization, rather than
a verbatim theorem from either source. The existing existence theorem only
proves positivity of tau; replacing beta by -beta preserves tau and reverses
psi, so that theorem alone does not establish this target. This file defines
no witness and contains no existence proof. It supplies no integral lattice,
polarization of an abelian scheme, moduli representability or canonical model.
