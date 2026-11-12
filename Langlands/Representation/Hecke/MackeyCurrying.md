# Categorical currying for the Mackey comparisons

This internal supporting unit packages the published smooth tensor–Hom currying
map of Renard III.1.15 as an equivalence of morphisms for the actual tensor and
smooth Hom bifunctors in `MackeyModels`. It proves naturality in the source,
the tensor factor, and the target, and the corresponding inverse formulas.
Pullback commutes with the actual diagonal tensor by the identity on the carrier.

`isoOfNaturalHomEquiv` is the usual representability argument: a family of Hom
equivalences natural in both arguments determines an isomorphism of functors.
Its components apply the equivalence and its inverse to identity maps; the
naturality equations prove both inverse identities and parameter naturality.
These are derived categorical helpers for Renard III.2.11, not additional
statements attributed to the source.
