# The actual quotient-Hom presheaf on original-chart domains

This derived construction realizes the actual original-chart domain category in
the constructed source-quotient category and restricts its representable
presheaves to that domain category. It proves separatedness for every sieve in
the quasinet topology, including sieves on a proper domain. Separatedness means
that a matching family has at most one glue. Existence for arbitrary matching
quotient families remains open.

The source motivation is Berkovich, *Étale cohomology for non-Archimedean
analytic spaces* (1993), Definition 1.3.1 (printed p.23 / PDF p.20),
Proposition 1.3.2 (printed p.24 / PDF p.21), and the G-topology paragraph
(printed p.25 / PDF p.22). The registered original is
`berkovich-1993-etale-cohomology`, SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
Those passages motivate actual subspace domains, morphism descent, and quasinet
coverings. This unit gives the uniqueness part of descent for the existing
original-chart model, without claiming full identification with all analytic
spaces or domains.

`domainMap` factors the actual source-domain inclusion through a larger target
domain using the previously proved image-only universal property. Its image
condition follows from literal subset containment. Monicity of the ambient
domain inclusion proves identity and composition laws. Thus `domainFunctor`
constructs a functor from actual domains to actual saturated subspace objects
in the source quotient.

`domainHomPresheaf` composes the opposite domain functor with the actual Yoneda
presheaf of the target. Its values are precisely all source-quotient arrows
from each actual domain, and restriction is precomposition by `domainMap`.
`domainHomPresheafMap` gives natural postcomposition by any quotient arrow.
No literal strong representative is required as input.

`relativeDomainCover_subspace` moves a covering family contained in a domain
to that domain's actual induced subspace topology. The quasinet witnesses
give the same finite sets of contained subspace members and the same
neighborhood unions.

`relativeDomainComparison` factors the double-subspace inclusion through the
corresponding ambient domain using the proved image-only universal property.
Its composite with `domainMap` is the actual inclusion into the intermediate
domain, by monicity of the latter's ambient inclusion. Precomposing a local
equality with this comparison therefore yields equality on the actual nested
domain. `eq_of_relativeDomainCover` applies the existing separation theorem
for arbitrary source-quotient arrows to these nested domains and the
transported cover.

For a covering sieve, index all its source domains together with their
membership witnesses. Its defining finite neighborhood witnesses form a
relative covering family of precisely those domains. The preceding theorem
then gives `eq_of_domainCoveringSieve`. Applying it to two amalgamations of
the same family proves `domainHomPresheaf_isSeparated` in Mathlib's ordinary
presheaf sense.

The field, ambient-space, chart-index and relative cover-index universes are
independent. Empty domains and empty covers are governed by the actual
quasinet condition; no nonemptiness hypothesis is added. The proof compares
complete quotient arrows through proved domain factorization and monicity,
and never infers bounded algebra maps from their spectrum-point values.
Arbitrary quotient matching gluing, full analytic identification, and the
étale and equivariant site constructions remain separate obligations.
