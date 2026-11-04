# Structural inputs for no-torus unipotence

Author: Worker 1487.

`Langlands.GroupScheme.NoTorusStructuralReductionStatement.{u}` is an
internal conditional reduction to the exact published
`NoTorusUnipotentStatement.{u}`. It is a proposition definition; this file
supplies no proof. All six premises are explicit published proposition
interfaces at the same arbitrary universe:

- `NilpotentCentralTorusStatement` supplies a central maximal torus and a
  unipotent quotient for a smooth connected affine nilpotent group.
- `FiniteFieldGeometricMaximalTorusStatement` supplies a torus over the
  finite ground field that is maximal after algebraic closure.
- `AlgClosedTrivialMaximalTorusUnipotentStatement` gives unipotence over an
  algebraically closed field when a maximal torus has trivial range.
- `Lie.SemisimpleCentralizerSmoothStatement` gives smoothness of a closed
  representative of the actual centralizer of a semisimple tangent element.
- `Lie.SemisimpleCentralizerSpanningStatement` supplies, over an infinite
  ground field, a noncentral semisimple tangent element from the geometric
  existence premise, and states the spanning property of its centralizers.
- `SemisimpleIsogenyReductionStatement` supplies an isogeny to a nilpotent
  group or a group with a geometric noncentral semisimple tangent element,
  together with the specified lifting of target tori.

The conclusion retains the original arbitrary-field target, its smooth
connected affine group, and the all-test triviality of every homomorphism
from every torus over the ground field. No restriction to infinite,
perfect, algebraically closed or characteristic-zero fields is added to
that conclusion. The finite and infinite field cases are part of the
intended proof, not additional target assumptions.

This interface is derived from the published structural interfaces for the
parent task. Its intended proof uses induction on actual Lie dimension
for the infinite-field case. Torus lifting passes the absence of closed
tori through the isogeny. In the nonnilpotent branch, the connected
centralizer has smaller dimension and contains the original nonzero
semisimple tangent element, preventing it from being unipotent. This
avoids a separate requirement that maximal tori of that centralizer stay
maximal in the ambient group. The nilpotent and finite-field branches use
the first three explicit premises.

Proving this implication would establish only the assembly step. Every
structural premise retains its independent proof obligation, and this
conditional statement does not prove the parent no-torus theorem.
