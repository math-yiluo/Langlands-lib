# Sections represented by free module sheaves

This internal construction composes Mathlib's
free-module adjunction, its extension to presheaf categories, the
sheafification adjunction, and the small Yoneda equivalence. It specializes
the free sheaf functor already used in the general-site Čech nerve.

For any site (C,J), commutative ring R in Type w, and module sheafification,
`freeSheafAdjunction` makes `freeSheafFunctor J R` left adjoint to the
functor sending a module sheaf to its underlying presheaf of sets.

If C is locally small in universe w, `freeRepresentableHomEquiv` identifies
morphisms from the free module sheaf on `shrinkYoneda.obj U` into F with
sections F(U). `freeRepresentableHomLinearEquiv` promotes this bijection to
an R-linear equivalence. The evaluation formula
`freeRepresentableHomEquiv_apply` is definitional: it evaluates the
underlying module morphism on the image under sheafification of the
free module's identity generator. Addition and scalar multiplication of
sheaf morphisms are pointwise, so both linearity identities are
definitional as well.

The two naturality lemmas show that this equivalence commutes with
coefficient morphisms and restriction along arrows of C. Coefficient
naturality is definitional. Restriction naturality composes the
adjunction's naturality in its left argument with Mathlib's small
Yoneda naturality identity.

No subcanonical assumption or finite products in C are required. The
construction identifies degree-zero sections; it does not establish a
Čech-to-derived comparison or an acyclicity criterion.
