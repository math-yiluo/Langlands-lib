# Maximality of tori under field extension: statement

Worker 1336.

`MaximalTorusBaseChangeStatement.{u}` concerns any field extension
`K/k` with both fields in `Type u`, any smooth affine group scheme
`G` over `k`, and any closed torus embedding `i : T.toGrp ⟶ G`.
It asserts that `IsMaximalTorus i` is equivalent to
`IsMaximalTorus` for the actual base-changed homomorphism
`T_K.toGrp ⟶ G_K`.

The hypotheses `IsTorus T.toGrp` and `IsClosedSubgroup i` express that
`T` is a torus in `G` before maximality is tested. The right-hand side
uses the published commutative and ordinary group-scheme base-change
functors along `Spec K ⟶ Spec k`. Thus it tests maximality against
all closed tori over `K`, including tori that are not supplied as base
changes of tori over `k`.

The source is Milne, *Algebraic Groups* (2017), source ID
`milne-2017-algebraic-groups`, Theorem 17.82 and its proof, printed
p.379 (one-based PDF p.395, zero-based page 394). We specialize the
source's group-variety setting to smooth affine groups. Such a group
is of finite type: the structure morphism is smooth and
quasi-compact. Connectedness of `G` is not required, as the source
first passes to the identity component. The extension can be
inseparable or transcendental; neither field is required to be
perfect, and there is no restriction on characteristic. The author's
registered errata snapshot of 2026-11-02 has no correction to this
theorem.

This is the full maximal-torus predicate, rather than maximal
split-torus rank or preservation of the torus property alone.
In particular, proving the forward implication requires controlling
larger tori after extension. Milne's proof uses the centralizer of
the torus, its quotient by the torus, and the equivalence between
unipotence of that quotient and the absence of a nontrivial torus.

This file only defines a proposition. It proves neither implication.
Torus base change, isomorphism descent, and elementary maximal-torus
transport are useful inputs, but none of them by itself establishes
this structural theorem or `ParabolicMaximalTorusStatement`.
