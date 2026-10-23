# Naturality of homomorphism pullback

For an abelian-scheme homomorphism `f : A ⟶ B` and a morphism
`h : T ⟶ U` of parameter schemes over the base, the two actual
pullback functors from rigidified families on `U ×_S B` to families
on `T ×_S A` are naturally isomorphic.

`homFamilyPullbackNaturality` constructs this isomorphism under the
explicit `RigidifiedModule.PullbackCoherenceStatement` hypothesis.
Each two-step pullback is compared with pullback along its composite
using `RigidifiedLineBundle.pullbackComp`. Naturality of
`homFamilySpaceMap` identifies the composite total-space maps; the
identity laws identify the maps on parameter schemes. The existing
`pullbackCongr` joins these comparisons. Thus the comparison respects
the actual rigidifications, as well as the underlying sheaves.

`homClassesPullback_naturality` descends this comparison by quotient
induction. `homClassesPullbackNatTrans` packages the resulting maps
as a natural transformation from the class presheaf of `B` to that
of `A`.

Under the additional, explicit `HomPicardZeroPullbackStatement`
hypothesis, `homPicardZeroClassesPullback` restricts the same
quotient map to the subtype of geometric Picard-zero classes. Its
membership proof is quotient induction followed by that hypothesis.
The identity and contravariant composition laws are the ambient
class equalities, lifted by subtype extensionality.

Finally, with the explicit parameter-pullback stability proposition
`PicardZeroPullbackStatement`, the actual Picard-zero presheaves are
available. `homPicardZeroPullbackNatTrans` gives the restricted
natural transformation between them. Its naturality follows from
the ambient equality, again by subtype extensionality.

## Provenance and scope

This module is derived infrastructure, not an assertion of any of
its preservation hypotheses. It applies the rigidified pullback
interpretation of Edixhoven, van der Geer and Moonen, *Abelian
Varieties*, preliminary draft, Chapter VI paragraph (6.2), printed
p.88 (PDF p.92), to the commuting fibre-product diagram determined
by `f` and `h`. The registered source is
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
The geometric predicate and the distinct homomorphism-preservation
obligation retain the provenance documented in their existing pairs.

Everything is over an arbitrary base scheme. This module constructs
maps on actual isomorphism classes and natural transformations; it
does not supply dual existence, tensor operations, or additivity
in the homomorphism.
