# Finite augmented test systems and coefficient lifting

This internal construction packages explicit categorical hypotheses for a
finite-basis Čech acyclicity argument. It does not construct an analytic basis.

Let `D` be an abelian category and `B : ι → D` a family of test objects.
`FiniteCechSystem B` consists of a family of nonnegative chain complexes for
each test object, an epimorphic augmentation to that object which is exact
at degree zero, and exactness in every positive chain degree. Every chain
term has a specified isomorphism to a finite coproduct of test objects.
For every short exact coefficient sequence and map from a test object into
its quotient, some augmented complex admits a lift of that map along its
degree-zero augmentation.

For any commutative ring `R`, with `D` an `R`-linear category, `K.HomAcyclic R F` means that every cochain complex
`Hom_R(K.complex i c, F)` is exact in every positive degree.

Injective coefficients satisfy this predicate by exactness of the chain
complexes and the injective Hom exactness lemma. If the first coefficient
of a short exact sequence satisfies the predicate, local lifting and
`liftByCechExactness` give a lift of every quotient-valued map from every
test object. The proof subtracts the degree-one obstruction boundary and
descends through the epimorphic augmentation. The finite coproduct
presentation then supplies lifts from every chain term: lift its
components, assemble them by the coproduct universal property, and
transport along the specified isomorphism. Finally,
`exactAt_linearYonedaObj_quotient_all` shows that the quotient also
satisfies the predicate when the middle coefficient is injective.

These are categorical consequences of the supplied data, with internal
provenance from the stated universal properties and coefficient diagram
chases. A site specialization must construct the exact augmentations,
finite presentations, and local lifts and establish the coefficient
predicate. A bare free presheaf nerve does not supply these hypotheses.
Higher right-derived vanishing is a separate subsequent result.
