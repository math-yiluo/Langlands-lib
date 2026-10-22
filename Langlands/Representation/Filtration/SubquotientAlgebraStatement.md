# Algebraic closure of actual smooth subquotients

This internal statement records two facts about the existing `SmoothRep.IsSubquotient` relation, over every field and every group with any supplied topology. The field, group, and common representation-carrier universes are independent. The common carrier universe is required by the existing subquotient relation.

`SmoothSubquotientTransitivityTheorem` says that an actual smooth subquotient of an actual smooth subquotient is an actual smooth subquotient of the original representation.

`SmoothSubquotientArtinianTheorem` says that group-algebra Artinianness passes from an ambient smooth representation to each of its actual smooth subquotients. It does not require finite dimensionality, finite length, or Noetherianness.

`SmoothSubquotientAlgebraTheorem` bundles these statements. These are proposition definitions, not proofs.

The provenance is internal algebra. The published presentation criterion in `Classification.SupercuspidalSupport` presents a subquotient by a smooth object embedding into the ambient object and surjecting onto the subquotient. To compose presentations, pull the second presentation's subrepresentation back along the first surjection, restrict that surjection, and then take the second quotient. For Artinianness, apply the standard injective and surjective transfer facts to the group-algebra linear maps underlying such a presentation. These facts support the extraction of simple constituents after Jacquet descent without asserting any analytic association theorem.
