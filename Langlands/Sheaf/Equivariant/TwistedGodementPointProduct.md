# Actual smooth Godement terms and coefficient diagrams

This is an internal factorization of the existing twisted-site Godement construction.
It works for a translation-invariant topology `J` on `P.Over ⊤ X`, a local action
system `L` with admissible refinements, actual points `points : I → J.Point`, and
module coefficients. The category objects, morphisms, group, and point fibers use
the independent universes `u`, `v`, `uG`, and `w`; the index and coefficients use
`w`. The pointwise right Kan extensions used by actual induction are explicit
hypotheses. Neither sheafification nor analytic or topological separation
hypotheses are needed for this identification.

`smoothGodementCoefficientFunctor` first includes a locally discrete sheaf in the
twisted site, restricts it to the ordinary site, and takes its actual fibers at
the points. The existing equivalence with diagrams on `Discrete I` changes the
presentation of this family.

`restrictedSmoothGodementPointProductIso` is a natural isomorphism from
`exactZeroFunctor` followed by inclusion and restriction to this coefficient
functor followed by `coefficientRestrictedSmoothPointProductFunctor`. Both sides
use the existing point product, right Kan induction, locally discrete
coreflector, and restriction.

The proof applies `PointProduct.godementZeroIso` after restriction and before
induction, coreflection, inclusion, and restriction. Whiskering this published
natural isomorphism gives the asserted identification. The family-to-diagram
equivalence followed by its inverse is definitionally the identity on families,
so it introduces no new mathematical comparison.

This identifies the actual functors and their maps. It asserts no preservation
of injectives by restriction and no compact-support derived vanishing.
