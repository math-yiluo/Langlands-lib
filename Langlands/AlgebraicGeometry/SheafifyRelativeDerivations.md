# Sheafification of relative derivations

This file is internal infrastructure for the construction of the relative
cotangent sheaf. It does not construct the required universal presheaf
derivation or assert its existence. That is a separate prerequisite.

`moduleSheafification X` is Mathlib's module-sheafification functor, with
unchanged coefficient sheaf `X.ringCatSheaf`. Its objects belong to the actual
category `X.Modules`. `moduleSheafificationUnit` and
`moduleSheafificationHomEquiv` expose the adjunction unit and the bijection
between morphisms out of the associated sheaf and presheaf morphisms into
the underlying presheaf of a sheaf.

Given any relative presheaf derivation `d`, `sheafifyRelativeDerivation d`
postcomposes it with this unit, obtaining a relative derivation into the
associated module sheaf. If `h : d.Universal` has been proved for that
presheaf derivation, `presheafDerivationHomEquiv` packages its factorization
and uniqueness into an equivalence. `sheafifyRelativeDerivationHomEquiv`
composes this with the sheafification adjunction. Its forward map is proved
to be postcomposition of the sheafified derivation, so its naturality follows
from associativity of postcomposition. The resulting
`sheafifyRelativeDerivationCorepresentable` is Mathlib's
`Functor.CorepresentableBy` structure for `relativeDerivationFunctor f`;
it includes the naturality law.

The equivalence's inverse is constructed by first descending a derivation
using `h.desc`, then applying the inverse adjunction equivalence.
The inverse laws use `h.fac` and `h.postcomp_injective`.
The formula for the forward map follows by extensionality on local sections.
These are conditional transfer constructions. Passing an arbitrary unproved
universal property as input to these definitions cannot establish the
existence of relative differentials.

## Provenance

This is derived categorical infrastructure for the sheafification construction
described by the Stacks Project, Section 17.28, Lemma 17.28.4, and the universal
derivation functor of Definitions 17.28.1 and 17.28.10 and Section 29.33,
Lemma 29.33.2. The implemented route uses the sheafification adjunction, not
an exactness argument applied to the generators-and-relations presentation.
The source does not state this general transfer interface in Lean's terms.

Registered source: `stacks-relative-differentials-internal-hom-2026-10-21`,
content SHA256
`9c075370ba97d8876785c5486425c6c661765e747452c026583f4dc51f1e1133`,
files `08RL.html` and `01UM.html` at the locations above.
Implementation uses Mathlib
`Algebra/Category/ModuleCat/Presheaf/Sheafification.lean` and
`Algebra/Category/ModuleCat/Differentials/Presheaf.lean` at commit
`5ed2965256430c3649e86755f9576b54eca72435`.
