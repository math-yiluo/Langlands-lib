# Convolution duals through nilpotent scalar reduction

This internal algebraic prerequisite studies a coalgebra \(C\) over a
commutative ring \(R\), using its actual convolution dual
\(D=\operatorname{Hom}_R(C,R)\). The coalgebra need not be cocommutative;
its convolution algebra need not be commutative. All rings, coalgebras and
modules are allowed in the universes of the Lean declarations.

## Scalar reduction and orthogonal idempotents

`reduction I` is the \(R\)-algebra homomorphism
\[
 D\longrightarrow \operatorname{Hom}_R(C,R/I),\qquad
 f\longmapsto (x\mapsto f(x)\bmod I),
\]
where both spaces carry convolution multiplication. The codomain here consists
of \(R\)-linear maps on the original coalgebra, rather than an independently
chosen model of the scalar-extended coalgebra. Postcomposition with the scalar
quotient preserves convolution and its unit, the counit. `reduction_apply`
gives its evaluation formula.

If the underlying module \(C\) is projective, `reduction_surjective` follows
from the projective lifting property applied to the quotient map \(R\to R/I\).
No finite generation assumption is needed for this surjectivity.

`pow_apply_mem` proves that if \(f(C)\subseteq I\), then
\((f^n)(C)\subseteq I^n\). The induction expands convolution with a finite
Sweedler representation and uses membership in the product of ideals.
Consequently, when \(I\) is nilpotent,
`isNilpotent_of_reduction_eq_zero` proves that every element of the kernel of
`reduction I` is nilpotent.

`exists_lift_completeOrthogonalIdempotents` assumes projectivity of \(C\),
nilpotence of \(I\), and a finitely indexed complete orthogonal idempotent
family in the reduced convolution algebra. It lifts that family to a complete
orthogonal idempotent family in \(D\), with the same index set and the specified
reductions. The proof applies Mathlib's lifting theorem for complete orthogonal
idempotents along a surjective ring homomorphism with elementwise nilpotent
kernel. It does not assume commutativity of either convolution ring or that
any of the individual idempotents are nonzero.

## Lifting generation

The imported `Langlands.Algebra.eq_top_of_sup_smul_eq_top_of_nilpotent`
from `NilpotentModuleFiniteness` is a module lemma for an arbitrary \(R\)-module
\(M\), submodule \(N\), and nilpotent ideal \(I\). It proves
\[
 N+IM=M\quad\Longrightarrow\quad N=M.
\]
The published proof iterates the equality to \(N+I^nM=M\); nilpotence
then gives \(N=M\).
No finite generation, freeness, or local ring hypothesis is used in this lemma.

For a finite free underlying module \(C\), `ker_reduction` identifies the
linear kernel of reduction with \(ID\). One inclusion expands a functional in
the finite dual basis: if it vanishes modulo \(I\), every coefficient belongs
to \(I\). The other inclusion evaluates scalar multiples and uses the ideal
property.

`span_eq_top_of_reduction` therefore proves that any family in \(D\) whose
reductions span \(\operatorname{Hom}_R(C,R/I)\) as an \(R\)-module already
spans \(D\). Indeed the map of its span is the full reduced dual, so its span
plus the kernel is all of \(D\); the preceding nilpotent module lemma applies.
The family in this theorem need not be finite.

Finally, `exists_lift_spanning_completeOrthogonalIdempotents` combines these
results. For finite free \(C\) and nilpotent \(I\), a finite complete orthogonal
idempotent family spanning the reduced convolution dual as an \(R\)-module
lifts to a complete orthogonal idempotent family spanning \(D\), with each
prescribed reduction.

## Provenance and scope

Worker 626 derived this unit internally from the projective lifting property,
the convolution formulas, complete orthogonal idempotent lifting, finite dual
bases, and elementary module quotients. No additional literature assertion is
made. This is an auxiliary step towards the special-fibre multiplicative-type
lifting argument. It does not yet recover a group-like basis of the original
coalgebra, construct a group-scheme isomorphism, lift a splitting cover, or
prove the fibrewise central-isogeny criterion.
