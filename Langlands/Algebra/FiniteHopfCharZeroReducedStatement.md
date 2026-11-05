# Reducedness of finite commutative Hopf algebras in characteristic zero

Author: Worker 1609.

`Langlands.FiniteHopfCharZeroReducedStatement.{u,v}` is the proposition

```lean
∀ (k : Type u) [Field k] [CharZero k] (H : Type v)
  [CommRing H] [HopfAlgebra k H], Module.Finite k H → IsReduced H
```

Thus every commutative Hopf algebra that is finite-dimensional over a
characteristic-zero field is reduced: every nilpotent element of `H` is zero.
The universes of the field and the Hopf algebra are independent.
`HopfAlgebra k H` supplies the compatible algebra, module and coalgebra
structures. Finiteness is an implication premise, `Module.Finite k H`.

Here commutativity concerns multiplication in the coordinate ring. There is
no cocommutativity hypothesis on the coalgebra, so the associated finite
group scheme may be noncommutative. There are no hypotheses of perfectness,
algebraic closure or prior reducedness.

## Original source and derivation

The source is J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of
Finite Type over a Field*, Cambridge Studies in Advanced Mathematics 170,
Cambridge University Press, 2017; registered source
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.

The statement is the coordinate-algebra consequence of the following
passages, read in the original:

1. Definition 3.3 and Proposition 3.6, printed pp.65–66, PDF pp.81–82:
   a finitely generated commutative Hopf algebra over `k` defines an affine
   algebraic group, with comultiplication, counit and antipode corresponding
   to multiplication, identity and inverse.
2. Theorem 3.23 (Cartier), printed p.71, PDF p.87: affine algebraic groups
   over a characteristic-zero field are smooth.
3. Corollary 3.24, printed p.72, PDF p.88: finite algebraic groups over such
   a field are étale.
4. Appendix A.59–A.60, printed pp.579–580, PDF pp.595–596: finite étale
   schemes have finite étale coordinate algebras; such algebras are products
   of finite separable field extensions and are geometrically reduced.

More precisely, `Module.Finite k H` means that `H` is finite-dimensional as
a `k`-vector space. A finite vector-space generating set also generates it
as a `k`-algebra, and the structure morphism of `G = Spec H` is finite.
The commutative Hopf structure makes `G` an affine algebraic group by
Proposition 3.6. Apply Corollary 3.24, derived there from Theorem 3.23, to
obtain that `G` is finite étale. By A.60 and A.59 its coordinate algebra
`H` is a product of finite separable field extensions of `k`. Each field
has no nonzero nilpotents, and hence neither does their product. This is
exactly the conclusion `IsReduced H`.

The official author errata retained as
`milne-2017-algebraic-groups-errata-2026-11-02` (HTML snapshot, SHA256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`)
was read. Its Chapter 3 corrections concern printed p.80, 3.52, and p.85;
its Appendix A corrections concern pp.570 and 582. None changes the
passages used above.

This file defines the proposition only. A Lean proof of this proposition
is a separate obligation.
