# Algebraic invariant sesquilinear forms and finite tensor products

This is an internal algebraic prerequisite for the weak product-factor
unitarity theorem. The constructions and lemmas are derived directly from
complex sesquilinearity, irreducibility, and the universal property of the
finite tensor product. They introduce no representation-theoretic hypothesis
or assertion from external literature.

All forms are conjugate-linear in their first variable and complex linear in
their second. Evaluating on `x + y` and `x + I y` shows that a form with zero
diagonal vanishes, so every nonzero form has a nonzero diagonal value.
The radical of an invariant form is a subrepresentation; irreducibility and
nonvanishing force it to be zero. The symmetric part `b + b*`, or the
Hermitian form `I (b - b*)` when the symmetric part vanishes, supplies a
nonzero invariant Hermitian form. Nondegeneracy is a separate conclusion
requiring irreducibility.

`tensor` composes the published conjugate-linear map `tensorConj` with
Mathlib's `PiTensorProduct.dualDistrib`. Its value on two pure tensors is
the product of their factor pairings. Induction on each tensor variable
shows that pure-tensor values determine a sesquilinear form. This proves
Hermitian symmetry and invariance under the actual external tensor action
from the corresponding factor identities. Nonzero factor diagonals have
nonzero product, proving nonvanishing, including the empty-index case.
No factor is assumed finite dimensional, and group, index, and vector-space
universes are independent.

For `factors_unitarizable_of_external`, fix vectors with nonzero factor
diagonals. Inserting a vector in one coordinate of their pure tensor gives
an intertwiner from that factor to the restriction of the external action
along the corresponding group coordinate. The intertwiner is nonzero since
the chosen pure tensor has nonzero tensor pairing. Irreducibility makes
the intertwiner injective. Restriction and pullback of the supplied invariant
positive form then unitarize the factor. The supplied factor forms need
neither Hermitian symmetry nor invariance for this last argument.
