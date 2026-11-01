# Canonical additive associativity of original balanced tensors

Worker 695 proves the published closed proposition
`Langlands.Algebra.NonUnitalTensorAssociativityTheorem` without changing its
statement or dependencies. The eight ring and carrier universe parameters are
independent. The proof uses the original balancing quotients and their inherited
additive groups, with the published residual `rightModule` and `leftModule`.

The forward map is the actual `lift S` of `forwardPairing`; the inverse is the
actual `lift R` of `inversePairing`. Their triple pure-tensor values hold by
reduction through both nested lifts. Two extensionality lemmas apply the published
`hom_ext` twice, fixing the third or first variable and comparing additive maps
out of the inner quotient. They prove that both composites are the identity on
the whole quotient. These identities construct `associator` as an additive
equivalence. `associator_canonical` establishes both pure-tensor formulas, equality
of both complete additive maps with the prescribed nested lifts, and both complete
inverse identities. `existsCanonical` supplies the witness at any original triple.

For arbitrary canonical witnesses at two independent triples, `naturality` proves
both whole-map squares by the same two extensionality lemmas. The maps are exactly
the tensor map of `rightMap hY hY' f g` and `k`, and the tensor map of `f` and
`leftMap hY hY' g k`. Evaluating on a triple reduces these maps to `f x`, `g y`,
`k z`; the canonical formulas on both witnesses complete each square. The closed
theorem supplies existence at both independent triples as well as this naturality.
No unit, nondegeneracy, idempotentedness, coefficient or resizing assumption is used;
degenerate actions, zero actions and trivial carriers are included.

This is an internal additive proof motivated by David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026,
registered as `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 695 read the conventions at printed pages 5–7 / PDF11–13, I.2.1 at
printed page 14 / PDF20, and the full associativity theorem, corollary, corollary
proof and three-variable naturality remark at printed pages 15–16 / PDF21–22,
visually checking PDF21. Renard's I.2.2.4 is complex-linear over complex
unitizations, and I.2.2.7 specializes to nondegenerate modules over complex
idempotented algebras using I.2.1.2. The arbitrary-ring additive result proved
here does not supply the coefficient-linearity or unitization comparisons.
The book refers its proof to bibliography [34], pages 97–98; this contribution
does not rely on that unread reference.

The supplementary `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`, was
read at PDF1–2. These pages correct induction adjunctions and explain a nonunital
corner tensor argument using a balanced additive pairing. They do not alter this
intrinsic additive associativity construction. The 2026 edition remains governing.

Coefficient comparisons, additional outer actions, pentagon coherence, tensor-Hom
equivalences, exactness and categorical adjunctions remain separate obligations.
