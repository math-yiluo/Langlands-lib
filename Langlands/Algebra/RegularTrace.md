# Regular trace and duality for simple algebras

This internal algebraic construction extends Mathlib's linear-endomorphism
trace to the left regular representation of a possibly noncommutative algebra.
It supplies a prerequisite for the trace pairing in the unitary PEL construction.
It does not identify regular trace with reduced trace.

For a commutative ring R and a unital R-algebra A, `regularTrace R A` is the
R-linear map a ↦ Tr_R(L_a), where L_a(x) = ax on the actual R-module A.
`regularTraceForm R A` sends (a,b) to Tr_R(L_ab). Cyclicity of linear-map trace
and L_ab = L_a L_b prove `regularTrace_mul_comm`, so this bilinear form is
symmetric. These definitions and cyclicity do not require A to be commutative.
As with Mathlib's trace, the definition exists without a finite basis; all
nondegeneracy and duality conclusions below impose finite dimension.

`regularTraceRadical R A` is the two-sided ideal consisting of a such that
Tr_R(L_ab) = 0 for every b. Additive closure follows from trace linearity.
Right absorption follows from associativity. For left absorption, cyclicity
rewrites Tr_R(L_(cab)) as Tr_R(L_(abc)).

Now let K be a field of characteristic zero and A a finite-dimensional simple
K-algebra. Simplicity forces the radical ideal to be zero or the whole ring.
The whole-ring alternative would imply Tr_K(L_1) = 0. But L_1 is the identity,
whose trace is dim_K(A), a nonzero element of K because A is nontrivial and K
has characteristic zero. Thus `regularTraceRadical_eq_bot` proves the radical
is zero. This proves left separation; symmetry proves right separation, giving
`regularTraceForm_nondegenerate`.

`regularTraceDual K A` is the resulting actual K-linear equivalence
A ≃ Hom_K(A,K), sending a to b ↦ Tr_K(L_ab). Its construction uses Mathlib's
finite-dimensional bilinear-form duality. The theorem
`regularTraceDual_conj_mulLeft` proves that conjugating L_a by this equivalence
gives the transpose of R_a, where R_a(b) = ba. On functionals of the form
Tr_K(L_(xb)), this is exactly the cyclic identity
Tr_K(L_(axb)) = Tr_K(L_(xba)). Trace is unchanged by conjugation or transpose,
so `trace_mulRight_eq_regularTrace` proves Tr_K(R_a) = Tr_K(L_a).

All of these proofs are intrinsic derivations from Mathlib's multiplication
maps, trace cyclicity, simple-ring ideal dichotomy, and finite-dimensional
duality. No external theorem or chosen splitting is an input. In particular,
left and right regular traces are compared only under the stated simplicity,
finite-dimension and characteristic-zero hypotheses.

The source-normalized PEL trace, invariance under an algebra involution,
alternating forms, adjoint actions and the comparison of the resulting
similitude groups are subsequent obligations. None is asserted by this module.
