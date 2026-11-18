# Operations on Mathlib's actual Brauer quotient

For every field `K : Type u`, this module gives Mathlib's actual quotient
`BrauerGroup.{u,u} K` an additive abelian group structure, with representative
algebras also in `Type u`. It applies in every universe and every
characteristic, including imperfect fields of characteristic two.

`Langlands.Brauer.classOf A` is the quotient class of an actual `CSA K`.
The instance `instAddCommGroupBrauerGroup` has the following computation laws:

- `classOf_groundField`: the ground field has class zero;
- `classOf_tensor`: `classOf (tensor A B) = classOf A + classOf B`;
- `classOf_opposite`: `classOf (opposite A) = -classOf A`;
- `classOf_matrix`: a positive-size matrix algebra over `A` has class
  `classOf A`.

`classOf_eq_iff` identifies equality with Mathlib's matrix-stable
`IsBrauerEquivalent`; `classOf_eq_of_algEquiv` gives equality from an actual
algebra equivalence. No alternative formal group or extra group-law
hypothesis is supplied.

Matrices commute with tensoring by the associativity and commutativity
equivalences and `matrixEquivTensor`. This proves tensor well-definedness.
Transpose identifies matrices over the opposite algebra with the opposite
matrix algebra and proves opposite well-definedness. The group laws descend
the actual tensor associator, symmetry and unit equivalences. The inverse
law uses the canonical enveloping equivalence and a finite basis to identify
endomorphisms with a positive-size matrix algebra. The matrix size is
`Module.finrank K A`, which is positive because a simple ring is nontrivial.
The resulting actual matrix equivalence proves
`tensor_opposite_equivalent`.

`matrixOneEquiv` is the one-by-one chart using the standard `Fin 1` matrix
instances. Its entry evaluation and constant-matrix inverse are checked
directly. This avoids a different finite-enumeration instance in Mathlib's
generic unique-index chart.

The quotient implementation uses the same universe for the field and its
representative algebras, for every universe. The representative constructors
and matrix-tensor compatibility retain independent algebra universes.

The original source is Knus–Merkurjev–Rost–Tignol, *The Book of Involutions*
(1998), §1, printed pp.3–4 / PDF pp.26–27, registered as
`knus-merkurjev-rost-tignol-1998-book-of-involutions`, content SHA256
`e21641aeb1425b63bec70032352f0cb33275f7bd1ddf682c3bea62b798654fe0`.
The construction follows the tensor-product group and opposite inverse
following Definition (1.3), using the enveloping equivalence of Theorem
(1.1)(2). These original pages and the relevant retained author errata were
read; no correction to these constructions was present.

The matrix-tensor chart and representative well-definedness lemmas are
internal implementations using canonical algebra equivalences. Neutral-class
splitting and scalar-extension homomorphisms are subsequent construction
units.
