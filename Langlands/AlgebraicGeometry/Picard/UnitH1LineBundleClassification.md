# Actual unit H¹ and line bundles on compact schemes

This internal construction uses the published actual unit-sheaf comparison,
ordered-unit refinement, and finite line-bundle presentations. Its current
implemented declarations work on arbitrary schemes at universe `u`, with finite
full open covers indexed in `Type u`.

`classOfCocycle_refine` applies the published `comparisonHom_refine` to the
quotient class of a closed ordered unit cochain. Hence a finite full refinement
preserves its class in Mathlib's actual Ext-defined `Sheaf.H` of the
structure-sheaf unit sheaf.

`nonempty_iso_glued_iff_class_eq` compares two possibly different finite full
covers. Their product intersection cover is finite and full. Refinement preserves
both actual H¹ classes, and equality on that common cover means exactly that the
second restricted cocycle minus the first is a coboundary. The published
cross-cover gluing criterion identifies that relation with an isomorphism of
the actual glued module sheaves.

`FinitePresentation.cohomologyClass_eq_iff` transports this equivalence through
the two presentation recovery isomorphisms. Two chosen presentations therefore
give the same actual H¹ class exactly when their presented module sheaves are
isomorphic. `cohomologyClass_eq` specializes to independence of presentation for
one module sheaf. These results require no compactness, separatedness or
affineness of the common intersection cover.

For the remaining declarations assume that the underlying space of `X` is
compact. `LineBundle.finiteUnitPresentation` chooses a finite affine
presentation using the published existence theorem.
`LineBundle.unitCohomologyClass` is its actual H¹ class. The preceding
independence theorem proves that every other finite presentation computes the
same class. Equality of these classes is equivalent to an actual module-sheaf
isomorphism, or equivalently an isomorphism in the category of line bundles.

`unitCohomologyClass_glued` computes the class of the actual line bundle glued
from any closed unit cochain on a finite full open cover, which need not be
affine. It compares that cover with the chosen finite affine presentation.
`LineBundle.unitCohomologyClass_surjective` uses the published finite-cover
coverage of actual H¹ on compact spaces. Choose a cocycle representative in
the resulting Čech quotient and glue it; the computation just proved gives
the prescribed actual H¹ class.

`Group.unitCohomologyClass` applies this construction to the published chosen
line-bundle representative of an element of the existing scheme Picard
`Group X`. Its value on the class of a line bundle is that line bundle's
class. The actual isomorphism criteria for Picard classes and H¹ give
injectivity, and the preceding realization theorem gives surjectivity.
`Group.unitCohomologyEquiv` packages the resulting equivalence of underlying
types, with its computation on actual line bundles.

The construction is internal: it composes the published
`UnitCechH1Comparison`, `UnitCechRefinement`, `UnitCechPresentation`,
`AbelianSheafH1Refinement` and `LineBundleInverse` APIs. The target is the
actual Ext-defined cohomology of the actual structure-sheaf units, and the
source is the existing categorical Picard group. No substitute quotient or
cohomology theory is introduced. All constructions preserve arbitrary
universe `u`; compactness is the only geometric hypothesis for the
classification equivalence. The result is an equivalence of underlying
types. Tensor/addition compatibility, naturality under morphisms of schemes,
line-bundle deformation and Picard-sheaf representability remain open.
