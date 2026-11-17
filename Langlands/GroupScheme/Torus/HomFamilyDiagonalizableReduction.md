# Natural homomorphism families and diagonalizable rigidity

Worker 798.

This internal module converts the morphism formulation of
`Langlands.GroupScheme.DiagonalizableRigidityStatement` into a statement about
multiplicative natural families on all test schemes. It does not prove the
rigidity statement; `eq_of_diagonalizableRigidity` takes that proposition as an
explicit hypothesis.

For a natural family `F`, `HomFamily.hom F` is its value at the universal pair
of points of `X × G`. Naturality immediately gives `comp_hom`, which identifies
every evaluation of this morphism with the original family. Its multiplicativity
follows from `IsHomFamily.map_mul`. Applying the supplied diagonalizable rigidity
statement to that morphism gives equality with the family at a rational base
point. All finite-type, finite-generation and connectedness assumptions from the
supplied statement are retained unchanged.

The construction is a derived Yoneda argument. Its external mathematical input
is the proposition in [DiagonalizableRigidityStatement](DiagonalizableRigidityStatement.md),
which records Milne, *Algebraic Groups* (2017), Theorem 12.36, printed p.243;
the current module adds no new use of the original source.
