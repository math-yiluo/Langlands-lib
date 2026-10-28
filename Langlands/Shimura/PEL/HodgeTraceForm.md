# The actual trace Hodge form and its signed diagonal formula

Worker 57. This internal construction uses the published `TracePairingBaseChange`
and `RealPositivity` to form the real bilinear expression psi(x,y h0(i)) on
the actual real tensor algebra. It takes an arbitrary rational skew unit beta,
without assuming positivity of its auxiliary involution or its Hodge form.

For any positive compatible complex homomorphism h of a real algebra,
`PositiveComplexHom.signed_trace_pos` proves strict positivity of

```text
Tr_R(L_(h(-i) y h(i) sigma(y)))
```

for nonzero y. The proof applies positivity of h's actual twist to sigma(y),
which is nonzero by involutivity, and simplifies the double involution. No
finite dimensionality is required: the conclusion uses the same regular-trace
positivity assumption already carried by h.

For the actual central simple CM algebra D and any rational skew unit beta,
`skewTwist_tracePairingBaseChange_right` proves the right-adjoint identity

```text
psi(x b,y) = psi(x,y sigma_S(b)).
```

Here psi is the actual S-valued base change of the inverse-unit trace form
of the auxiliary algebra tau = beta sigma beta inverse. The coefficient
algebra S is any commutative rational algebra. The proof applies the published
cancellation formula, expands the extended involution on products, and uses
involutivity and associativity. It needs no positivity or nondegeneracy.

With the same actual Harris algebra and signature charts C as `RealPositivity`,
`kottwitzTraceHodgeForm` is Mathlib's `compRight` of the extended form with
right multiplication by J = h0(i), where h0 is `D.realPositiveKottwitzHom C`.
Its application formula is definitional. `kottwitzTraceHodgeForm_isSymm`
proves symmetry for every skew beta: sigma_R(J) = -J follows from star
compatibility of h0, the right-adjoint identity transfers J between the
arguments, and skew-symmetry of psi cancels the two minus signs.

Finally `kottwitzTraceHodgeForm_diagonal_mul` proves, for b = 1 tensor beta,

```text
B(b y,b y) = (1/n) Tr_R(L_(b y J sigma_R(y))).
```

It expands the actual inverse-unit scalar-extension formula, reverses the
product under the involution, uses sigma_R(J) = -J and sigma_R(b) = -b,
and cancels adjacent b and b inverse. No noncommuting factors are exchanged.
This formula removes inversion from the signed expression to which rational
approximation can later be applied. The generic signed positivity lemma
supplies a real positive witness at b = h0(-i); it does not claim that this
real element is rational.

Provenance is internal: the mathematical form, normalization, involution and
Kottwitz convention are those of the imported published modules. Every new
identity follows from their proved formulas, and the bilinear composition is
an actual Mathlib construction. This module does not choose a rational unit
with the Hodge sign, prove the rational existence target, or construct an
abelian-scheme polarization or PEL moduli scheme.
