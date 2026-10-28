# Kottwitz's complex homomorphism on the regular PEL module

Worker 57. This derived construction realizes the published, chart-constructed
Kottwitz complex homomorphism as an actual real algebra homomorphism into the
endomorphisms of the left regular module. It proves compatibility with the
actual inverse-unit trace form, including its conjugate adjoint and norm-square
multiplier, and identifies the operators with the published similitude and
Hodge-form constructions.

## Original sources and provenance

Robert E. Kottwitz, *Points on some Shimura varieties over finite fields*,
J. Amer. Math. Soc. 5 (1992), 373–444, printed p. 374 (PDF p. 2), specifies a
left B-module V with alternating form, its left-adjoint identity, and the real
algebra homomorphism h from C to End_B(V_R). Its compatibility is
h(conjugate z) = adjoint(h(z)); positivity is a further condition on
(v,h(i)w). Printed p. 375 (PDF p. 3) distinguishes the moduli scheme and its
canonical-model description. Printed p. 381 (PDF p. 9), Lemma 2.7 and the
following notation, gives the trace identities and forms Tr(x b y*).
Registered source: `kottwitz-1992-points-shimura-finite-fields`; SHA-256
`c7cede3d0a5e201068e6100acbb3832adb67767d69248ec65458e7cc74ee46f1`.

Michael Harris and Richard Taylor, *The Geometry and Cohomology of Some Simple
Shimura Varieties* (2001), Section I.7, printed p. 52 (PDF p. 60), uses B as a
B tensor B-opposite module, the trace pairing Tr(x beta y*), and the right
adjoint beta(*)beta inverse. Registered source:
`harris-taylor-2001-geometry-cohomology-simple-shimura`; SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

The new declarations are deductions from the Library's `RealPositivity`,
`TracePairingBaseChange`, `HodgeTraceForm` and `TraceSimilitudesBaseChange`.
They construct the endomorphisms from the original algebra and complex
homomorphism. They do not assume an output PEL representation or comparison
identity. The trace form keeps the Library's explicit normalization by 1/n;
no equality with an unnormalized source trace form is asserted.

## Generic regular action

In `Langlands.Shimura.AlgebraInvolution.ComplexHom`, let B be a ring with a
real algebra structure, sigma a real algebra involution and h a `ComplexHom
sigma`. No finite-dimensionality is assumed. `rightRegular` has type

```text
C ->_R-alg Module.End B B,
rightRegular(h)(z)(x) = x h.hom(z).
```

The target consists of B-linear endomorphisms of the left regular module,
with multiplication given by composition. Its real algebra structure is the
central scalar action. Each operator is `LinearMap.mulRight B`.
`rightRegular_apply` is definitional, and `rightRegular_left` is associativity.
Composition reverses right multiplication; commutativity of C and the
multiplicative law for h prove the algebra-homomorphism law. The other laws
follow from distributivity, the unit and h's scalar compatibility.

`rightRegular_injective` additionally requires `Nontrivial B` and uses
injectivity of a unital ring homomorphism from the field C into a nontrivial
ring. `rightRegular_I_sq` proves h(i) squared is minus the identity
endomorphism, using multiplicativity and i squared = -1. Here h(i) denotes
the constructed operator. No nontriviality premise is needed for this identity.

## Actual Harris inputs and extended left adjoint

The actual declarations are in `Langlands.Shimura.CentralSimpleUnitaryData`.
Their ambient parameters are E, K and A in arbitrary universes u, v and w:
E is a totally real number field; K is a totally complex number field and a
quadratic E-algebra; A is a ring with E-, K- and Q-algebra structures. The
scalar towers E/K/A and Q/E/A are specified. The datum
`D : CentralSimpleUnitaryData E K A n` supplies 1 < n, central simplicity,
finite dimensionality over K and dimension n squared. Write sigma for its
original involution, restricted to Q when extending scalars.

For any commutative Q-algebra S in an arbitrary universe z and any unit
beta of A, `tracePairingBaseChange_left` proves

```text
psi_D,S,beta(b x,y) = psi_D,S,beta(x,sigma_S(b) y),
psi_D,S,beta(x,y) = map_Q,S(1/n) Tr_S(L_(x (1 tensor beta) sigma_S(y))).
```

This helper does not require the E/K/A scalar-tower instance, signature charts,
skewness of beta or positivity. The proof expands the published tensor trace
formula, applies multiplicative reversal and involutivity, and cyclically
moves b through the regular trace. No noncommuting factors are interchanged
outside that trace identity.

For the remaining declarations, specify
`Phi : (E ->+* R) -> (K ->+* C)` and
`C : HarrisSignatureCharts D.toSecondKindInvolution n Phi`. These are the
published actual CM-section/signature charts, with signature (n-1,1) at the
distinguished embedding and (n,0) elsewhere. The scalar tower E/K/A is retained.
Set T = R tensor_Q A and h0 = `(D.realPositiveKottwitzHom C).val.hom`, with the
published conjugate Kottwitz convention and positivity of its twisted real
involution. `kottwitzPELHom` is the actual algebra homomorphism

```text
C ->_R-alg Module.End T T,
h(z)(x) = x h0(z).
```

The application, left-linearity and square-minus-identity theorems specialize
the generic regular construction. The homomorphism depends on D and C alone.

## Inverse-unit form and comparisons

Now take a rational unit beta with `hbeta : D.involution beta = -beta`.
Let tau = beta sigma beta inverse, the involution of `D.skewTwist beta hbeta`.
The form used in the remaining theorems is exactly

```text
psi = (D.skewTwist beta hbeta).tracePairingBaseChange R beta inverse,
psi(x,y) = map_Q,R(1/n) Tr_R(L_(x sigma_R(y) (1 tensor beta inverse))).
```

The published cancellation theorem proves the second formula. Applying the
new left-adjoint helper to the auxiliary datum gives tau_R as left adjoint;
the published `skewTwist_tracePairingBaseChange_right` gives sigma_R as right
adjoint. Thus the left algebra and its involution differ from the original
right-adjoint Harris involution, although their underlying ring is the same A.

`kottwitzPELHom_adjoint` proves, for every complex z and x,y in T,

```text
psi(h(z)x,y) = psi(x,h(conjugate z)y).
```

It substitutes the actual right multiplications, uses the published
right-adjoint identity and then h0's involution compatibility. The notation
`star z` in Lean is complex conjugation.

`kottwitzPELHom_normSq` proves for all z, including zero,

```text
psi(h(z)x,h(z)y) = normSq(z) psi(x,y).
```

Its proof first transfers h(z) to the second argument by the adjoint formula,
combines the commuting complex factors using h0's algebra law, and rewrites
z times conjugate z as the real scalar normSq(z). Bilinearity extracts that
scalar. The multiplier need not be invertible when z is zero.

For z in the units of C, `kottwitzPELHom_units_comparison` identifies h(z)
with the underlying linear map of

```text
D.harrisTraceSimilitudesEquiv R beta hbeta
  (op ((D.realPositiveKottwitzHom C).val.toSimilitudes z)).
```

This equality is definitional. It retains the existing opposite group for
general right multiplications; it does not assert a new group-functor
comparison. Finally `kottwitzPELHom_hodgeForm` definitionally identifies
psi(x,h(i)y) with `D.kottwitzTraceHodgeForm beta hbeta C x y`.

No positivity premise on tau or this Hodge form is used in these identities.
The unit does not select a rational beta with the required Hodge sign, prove
that existence theorem, construct a polarization, or construct the PEL
moduli functor, representing schemes or canonical models. Those remain
separate obligations of the parent development.
