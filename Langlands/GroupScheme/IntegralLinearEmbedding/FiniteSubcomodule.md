# Finite subcomodules of a flat coalgebra over a noetherian ring

Construction following J. S. Milne, *Basic Theory of Affine Group
Schemes*, version 1.00 (2012), Chapter VIII, Aside 4.7, printed p.117. The source
is registered as `milne-2012-basic-affine-group-schemes`; its SHA-256 is
`6e252b8fe636dd2aaabd97415a8b2a1ab83e84a38a1b4a46db5301d4c43dabc7`.
The specialization here is the regular right comodule of a coalgebra.

For a submodule W of a coalgebra B over a commutative ring R,
`subcomoduleCore W` is the kernel of comultiplication followed by the tensor
of the quotient map B → B/W with the identity of B. Right exactness identifies
membership with comultiplication lying in the image of W tensor B. The counit
shows that the core is contained in W. If B is flat over R, coassociativity and
preservation of exact sequences after tensoring show that the core is a right
subcomodule. Every right subcomodule contained in W is contained in this core.

Given a finite subset S, finite tensor expansions of its comultiplications give
a finitely generated submodule W whose tensor with B contains those images.
The core of W contains S. If R is noetherian, that core is finitely generated.
`finiteSubcomodule S` chooses such a submodule, and `finiteSubcomodule_spec`
gives finite generation, containment of S, and the right-subcomodule property.
No canonical choice is asserted.

For a principal ideal domain R, a finite submodule of a flat module is torsion
free and hence free. `exists_matrix_coefficients_of_flat` chooses a finite basis
of `finiteSubcomodule S` and applies the published coefficient-matrix API. It
produces a square matrix whose entries span S, whose comultiplication follows
matrix multiplication, and whose counit is the identity matrix. This deduction
is internal: it combines the finite-subcomodule construction above with the
existing basis and coefficient theorems in `IntegralLinearEmbedding.Comodule`.
It requires no separation by R-valued dual functionals and does not assert that
S lies in a finite subcoalgebra. The existing separation-dependent API remains
valid and is not modified.

The existing `Langlands.Algebra.FiniteSubcomodule.core` uses the range-comap
definition. Its `core_eq_ker` identifies that submodule with the quotient-kernel
`subcomoduleCore` used here. Both definitions are retained: replacing one with
the other would require propositional transport, rather than a change of names.
Their finite-subset and matrix interfaces also remain distinct.
