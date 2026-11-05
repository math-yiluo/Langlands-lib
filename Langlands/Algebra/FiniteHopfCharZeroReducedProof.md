# Proof of finite Hopf reducedness in characteristic zero

Author: Worker 16.

`Langlands.finiteHopfCharZeroReduced.{u,v}` proves exactly the published
proposition `Langlands.FiniteHopfCharZeroReducedStatement.{u,v}`:

```lean
∀ (k : Type u) [Field k] [CharZero k] (H : Type v)
  [CommRing H] [HopfAlgebra k H], Module.Finite k H → IsReduced H
```

The field and Hopf algebra have independent universes. Commutativity concerns
the multiplication of `H`; the coalgebra has no cocommutativity hypothesis.
The conclusion says that every nilpotent element of `H` is zero.

The implemented proof introduces the field, the Hopf algebra and their
structures, installs the implication premise `Module.Finite k H` as a local
instance, and applies the published theorem
`Langlands.FiniteHopfCharZero.isReduced (k := k) (H := H)`.

This is a direct reuse of the proof in
[`FiniteHopfCharZero.lean`](FiniteHopfCharZero.lean), whose
[paired explanation](FiniteHopfCharZero.md) describes preservation of
nilpotents by derivations, translation of tangent vectors through dual-number
points, the Artinian nilradical criterion, and descent from an algebraic
closure. That proof is by Worker 16, using Worker 1575's Artinian criterion.

The original mathematical provenance, as documented in the published
[statement](FiniteHopfCharZeroReducedStatement.md) and proof, is the
finite-dimensional coordinate-algebra consequence of J. S. Milne,
*Algebraic Groups* (2017), Theorem 3.23 (Cartier), printed p.71
(PDF p.87), and Corollary 3.24, printed p.72 (PDF p.88), registered as
`milne-2017-algebraic-groups`. This wrapper supplies the proof of the named
proposition by the existing algebraic theorem.
