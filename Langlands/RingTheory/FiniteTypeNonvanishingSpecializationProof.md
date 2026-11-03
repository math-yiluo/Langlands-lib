# Proof of finite-type specialization with prescribed nonvanishing

`Langlands.RingTheory.finiteTypeNonvanishingSpecialization.{u,v}` proves
the published proposition
`Langlands.RingTheory.FiniteTypeNonvanishingSpecializationStatement.{u,v}`.
The field and algebra have independent universes. The theorem adds no
hypotheses to that statement.

The proof gives the finite-type algebra `A` a Jacobson-ring instance
using `isJacobsonRing_of_finiteType`. By
`Ideal.radical_eq_jacobson`, the nonnilpotent product is outside the
Jacobson radical of the zero ideal. Expanding that radical as an
intersection of maximal ideals gives a maximal ideal `m` which does
not contain the product.

The quotient `A ⧸ m` is a field and a finite-type `k`-algebra.
`finite_of_finite_type_of_isJacobsonRing` shows that it is finite
over `k`. `IsAlgClosed.lift` then gives a `k`-algebra homomorphism
from this algebraic residue-field extension to `k`. Compose it
with `Ideal.Quotient.mkₐ` to obtain `φ : A →ₐ[k] k`.

The field homomorphism from `A ⧸ m` is injective. Therefore the
product, whose quotient class is nonzero, has nonzero image under
`φ`. The homomorphism preserves the finite product, and
`Finset.prod_ne_zero_iff` gives simultaneous nonvanishing of all
prescribed elements.

This implements the internal commutative-algebra argument explained
in the published statement's Markdown. It includes the empty finite
set, nonreduced algebras and arbitrary characteristic. It proves only
the specialization result; the group-scheme spreading and
unipotent-radical arguments in the parent task remain separate.
