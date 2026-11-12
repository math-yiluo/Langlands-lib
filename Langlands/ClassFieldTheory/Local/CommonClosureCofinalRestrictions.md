# Cofinal finite Galois restrictions of actual fixing subgroups

Worker 125. Internal infrastructure for Task 4919.

Let `K` be a perfect field and `E` an actual finite intermediate field of
`AlgebraicClosure K`. The cofinal-existence and separation results below
assume `PerfectField K`, as satisfied by the intended p-adic base fields.
The target `A` of a discrete-group homomorphism carries the discrete topology.

Every continuous homomorphism from a literal finite-intermediate-field
fixing subgroup to a discrete group has a kernel containing the fixing
subgroup of a finite Galois overfield of the original base. View the open
kernel as an open subset of the ambient absolute Galois group. The finite
Galois Krull neighborhood basis supplies a finite Galois field whose fixing
subgroup lies in it. Galois correspondence then proves that this overfield
contains the specified intermediate field. No normality of that
intermediate field is required.

`finiteRestrictionFactor` uses this kernel containment and the proved
surjectivity of finite restriction to descend a homomorphism through the
actual finite Galois group, via the first isomorphism theorem. Its action
formula states that the factor agrees with the original homomorphism on
each fixing automorphism. These are derived group and field constructions,
with no arithmetic reciprocity input.

For abelian discrete targets the same factor descends through the actual
finite algebraic abelianization. Under the perfect-base hypothesis, applying
this factorization to every open
finite quotient of the compact fixing subgroup's topological abelianization
shows that all finite Galois overfield restrictions together separate its
elements. The proof uses the actual profinite finite-quotient limit and
injectivity of its canonical map. It retains the original base's finite
Galois overfields as its indexing family, including for nonnormal
intermediate bases.
