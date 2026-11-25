# Openness of étale morphisms of analytic spaces

This module states
`Langlands.Analytic.SaturatedAtlasPresentation.EtaleOpenMapStatement`.
For every complete ultrametric normed field `K`, the proposition says that
every étale arrow `f : U ⟶ V` in
`LocalizedCategory.{u, v, v} (K := K)` induces an open map
`localizedSpaceFunctor.map f`. It is a proposition definition without a proof.

The objects, morphisms, and the predicate `etale` are the existing analytic
space and étale-site constructions. In particular, `etale f` requires a strong
representative that is étale over every recognized affinoid piece, up to an
isomorphism of arrows. Openness concerns the existing descended underlying
space functor; it is not included in that definition of étaleness.

## Provenance

The registered source is Vladimir G. Berkovich, *Étale cohomology for
non-Archimedean analytic spaces* (1993),
`berkovich-1993-etale-cohomology`, SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.

Proposition 3.2.7, printed p.59 / PDF p.56, asserts that a flat quasifinite
morphism is an open map. Definition 3.3.4, printed p.63 / PDF p.60, defines an
étale morphism as a quasifinite morphism that is unramified and flat. The
statement here is the resulting étale specialization, in the Library model.
No stronger claim about arbitrary flat morphisms is made. No corresponding
source erratum was found in the Library's errata notes.

## Role and scope

This is a missing geometric prerequisite for compact degree-zero smoothness
in the étale case of Berkovich's Theorem 1.6.1(ii). The image of an étale
structure map is open, so compactness can select finitely many images from a
jointly surjective family. Covering sieves being jointly surjective is a
separate prerequisite. Neither this openness statement nor the global
cohomology comparison is proved here.
