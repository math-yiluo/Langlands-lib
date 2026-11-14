# Canonical maps between the actual integral root models

This internal supporting module works over an arbitrary domain `R` with
fraction field `K`, in arbitrary universe `u`. The data are an actual compatible
model morphism `φ : RelativeComponentModelHom source target`, an integral
torus `T : IntegralTorusData source S i`, and a witness that `T.torus` is split.
The neutral models are smooth by their supplied model data.

`integralRootMap` constructs a morphism between the actual root models obtained
from `T` and `φ.mapIntegralTorus T`, for every nonzero generic character `a`.
The two integral tori and their generic identifications are the same, so the
integral characters are definitionally equal. The source root inclusion
followed by `φ.neutral.hom` lands in the full target root subgroup functor.
The arbitrary-base construction `RelativeRoot.SmoothQuotient.rootMap` factors
that composite uniquely through the target root representative. The
representatives here are the actual integral root model inclusions, on all
scheme tests. `integralRootMap_comp` is the resulting equality in the actual
target neutral model.

Over a local domain, `mapIntegralTorus_specialFibreInclusion` identifies the
residue inclusion of the transported torus with the original residue inclusion
followed by `φ.neutralSpecialFibreMap`. The character specialization of the
transported torus is definitionally the same equivalence as that of `T`, as
recorded by `mapIntegralTorus_characterSpecialization`.

`residueRootMap` is residue base change of `integralRootMap`, and
`residueRootMap_comp` base-changes its integral factorization square.
`residueRootMap_eq_rootMap` identifies this very map with the canonical
full residue-root map for `φ.neutralSpecialFibreMap` and the exact character
`T.characterSpecialization hT a`. The proof cancels the target root inclusion
using its full all-test representability and the two factorization equalities.

For any supplied target quotient data `Q`, `residueRootMap_quotient_comp`
then factors the original source-root composite into `Q.quotient` through
the target root's actual `rootReductiveQuotientMap`. It uses only associativity
and the residue factorization square.

These are internal deductions from the imported root-functor
representability and base-change constructions. No smoothness or surjectivity
of the model morphism or the induced root map is asserted. In the incident-facet
application, determining root survival from facet directions, proving the full
incident kernel smooth, and computing the full schematic-image weight support
remain separate obligations.
