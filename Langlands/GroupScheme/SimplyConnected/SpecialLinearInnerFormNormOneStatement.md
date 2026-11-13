# Inner forms of the special linear group are reduced-norm-one groups: statement

Author: Worker 93, for Task 5703 (`897f230f-d15d-48df-9d7a-63d2e4635fa8`). The module
contains one `Prop`-valued definition and no proof.

## Statement

`Langlands.GroupScheme.SpecialLinearInnerFormNormOneStatement.{u}` quantifies over

- a field `K : Type u`;
- a group scheme `G` over `Spec K`, with no further hypothesis;
- a natural number `n`;
- an actual quasi-split inner-form presentation `e : QuasiSplitInnerForm G`.

Assume that the model group `e.model` of the presentation is isomorphic, as a group scheme
over `Spec K`, to `SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of K)`, the actual
special linear group scheme `SL_{n+1}` over `K`. The statement then asserts that there is a
`K`-algebra `A : Type u`, with a ring structure, which is finite-dimensional, central and
simple, such that

- `Langlands.CentralSimple.reducedDegree K A = n + 1`, that is, `A` has dimension
  `(n + 1)^2` over `K`;
- `G` is isomorphic, as a group scheme over `Spec K`, to
  `CentralSimpleUnits.normOne K A`, the kernel of the reduced norm on the unit group of
  `A`.

The conclusion has exactly the form of the conclusion of the published
`InnerTypeANormOneStatement`.

## What the presentation contains

`QuasiSplitInnerForm G` (module `Rational/QuasiSplitInnerForm`) records a quasi-split model
group, an adjoint quotient `model ⟶ adjoint` with `IsAdjointQuotient`, a finite Galois
extension `L/K` (the field `carrier`), an actual local isomorphism `model_L ≅ G_L` over
`Spec L`, and a cocycle of the adjoint group on that cover, related to the local isomorphism
by `hasDiscrepancy`. The statement uses all of these data but asks for no condition on them
beyond the isomorphism `e.model ≅ SL_{n+1}`. In particular the adjoint quotient is the one
carried by `e`, not a chosen `PGL_{n+1}`; the cocycle takes values in that adjoint group.

## Intended proof (not part of the statement)

Classically, the adjoint quotient of `SL_{n+1}` is `PGL_{n+1} = Aut(M_{n+1})`, so the cocycle
of `e` twists the matrix algebra `M_{n+1}(L)` by inner automorphisms. Galois descent gives a
central simple `K`-algebra `A` of degree `n + 1` with `A ⊗_K L ≅ M_{n+1}(L)`. The reduced norm
is compatible with the twist, so `normOne K A` and `G` are both obtained from `SL_{n+1}` by the
same cocycle, and descent of the local isomorphisms gives `G ≅ normOne K A`. Formalizing this
needs Galois descent for algebras over a finite Galois extension, the action of the adjoint
quotient of `SL_{n+1}` on `M_{n+1}` by conjugation, and the published splitting isomorphism of
`normOne`. These are proof obligations.

## Role

This is one of the prerequisites in the planned proof of `InnerTypeANormOneStatement`
(Task 5703). That proof shows that the inner-type-A hypothesis yields a quasi-split inner-form
presentation with model `SL_{n+1}`, and then applies this statement.

## Source and provenance

Provenance: derived.

1. M.-A. Knus, A. Merkurjev, M. Rost and J.-P. Tignol, *The Book of Involutions*, AMS
   Colloquium Publications 44, 1998, source `knus-merkurjev-rost-tignol-1998-book-of-involutions`,
   SHA-256 `e21641aeb1425b63bec70032352f0cb33275f7bd1ddf682c3bea62b798654fe0`, §26,
   Theorem (26.9), printed p.366 (PDF p.389), with Remark (26.11), printed p.368 (PDF p.391).
   Over an arbitrary field `F`, the functor `A ↦ SL_1(A)` (through `SU(A × A^op, ε) = SL_1(A)`)
   and `SU(B, τ)` give an equivalence onto simply connected absolutely simple groups of type
   `A_n`. Its inner part is the classical statement that the simply connected inner forms of
   `SL_{n+1}` are the groups `SL_1(A)` with `A` central simple of degree `n + 1`.
2. V. Platonov and A. Rapinchuk, *Algebraic Groups and Number Theory*, Academic Press, 1994,
   source `platonov-rapinchuk-1994-algebraic-groups-number-theory`, SHA-256
   `c333b953ca0ace6306663f648cd853a75da55023bf873e0ef2688d997216717f`, §2.3.4,
   Proposition 2.17, printed p.87 (PDF p.97). "The simply connected groups pertaining to inner
   forms of type `A_{n-1}` are the groups `SL_m(D)`, where `D` is a central skew field of index
   `d` over `K` and `n = md`." The proof preceding it twists `M_n` by a cocycle of
   `PGL_n = Aut(M_n)` and takes Galois invariants, which is the route sketched above.

The Lean statement is derived from these sources as follows. "Inner form of `SL_{n+1}`" is the
actual published `QuasiSplitInnerForm` presentation (twisting over a finite Galois extension,
by a cocycle in the adjoint quotient) with model isomorphic to `SL_{n+1}`. `SL_1(A)` is the
published `CentralSimpleUnits.normOne K A`. `SL_m(D)` of Platonov–Rapinchuk is `SL_1(M_m(D))`,
and the statement does not ask for `A` to be a division algebra. Platonov–Rapinchuk twist by
cocycles of the Galois group of an algebraic closure, and their chapter often assumes
characteristic zero. The finite-Galois form used here is the same twisting procedure restricted
to the splitting extension carried by the presentation. Knus–Merkurjev–Rost–Tignol state the
classification over an arbitrary field, in every characteristic.
