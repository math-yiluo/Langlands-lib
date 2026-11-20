# The convolution dual of a finite projective Hopf algebra

For a finite projective module `A` over a commutative ring `R`, `Dual R A`
is its linear dual with the `WithConv` type tag. The equivalence
`tensorDual` sends `f ⊗ g` to the functional taking `a ⊗ b` to
`f(a) g(b)`. The map `bidualLinear` sends `a` to evaluation at `a`.

For a commutative algebra `A`, the dual comultiplication is the
transpose of multiplication, transported through `tensorDual`. The
dual counit evaluates at `1`. Pairing against pure tensors proves
coassociativity from associativity of multiplication, the counit
identities from its unit laws, and cocommutativity from commutativity.

For a cocommutative bialgebra `A`, the dual uses Mathlib's convolution
algebra structure. The tensor pairing respects convolution by the
exterior convolution product formula on pure tensors and additivity.
Pulling back along the coalgebra map given by multiplication then
proves multiplicativity of the dual comultiplication. The dual
comultiplication preserves `1` because the original counit is
multiplicative. The dual counit preserves multiplication and `1` by
the corresponding identities at `1` in the original algebra.

For a Hopf algebra `A`, the transpose of its antipode satisfies the
dual antipode identity. Evaluation of this identity at `a` reduces it
to the original antipode identity at `a` followed by the functional
in the dual. Cocommutativity and commutativity give the other
convolution inverse identity.

Finally, `bidualEquiv` upgrades `bidualLinear` to a bialgebra
equivalence for a commutative and cocommutative bialgebra. The
transposed multiplication formula proves multiplicativity after
evaluation. Pairing against two functionals and applying the original
convolution formula proves preservation of comultiplication.

These are coordinate algebra constructions for the Cartier duality
proof. They implement the module dual and double dual calculations in
Demazure and Gabriel, *Groupes algébriques*, Tome I (1970), Chapter II,
§1, no. 2, 2.10(a) and 2.10(d), printed pp. 156–158.
