# Whole-domain stabilizers and actual global spectrum actions

Authors: Worker 56 and Worker 36.

Let `K : Type u` be a complete ultrametric normed field, let `P` be an
actual presented positive-polyradius affinoid algebra, and let `G : Type v`
be a topological group in an independent universe. The input
`DomainSpectralAction G P` consists of actual bounded algebra
automorphisms and continuity into the explicitly constructed topology
testing sections on full represented domains.

## The actual whole represented domain

The existing `Domain.whole K P` has algebra literally `P`, structural
map the bounded identity, and locus the whole spectrum.
`mem_wholeLocusOpenSubgroup` proves that every group element belongs to
its constructed locus stabilizer. The spectrum action of each bounded
automorphism is surjective because it is a group action, so its image
of the whole spectrum is the whole spectrum. This also holds for an
empty spectrum.

`wholeStabilizerHom` sends `g : G` to the same element with this
stabilizer membership proof. It is a continuous monoid homomorphism:
the subtype inclusion is built from the continuous identity map.
`wholeStabilizerHom_coe` records that its underlying element is
unchanged.

`sectionAction_whole` proves equality of the actual constructed section
automorphism with the original automorphism:

`ρ.sectionAction (Domain.whole K P) (ρ.wholeStabilizerHom g) = ρ.toMonoidHom g`.

The proof applies the published structural section equation to each
element of `P`. Its structural map is the identity. Extensionality of
bounded maps and automorphisms then gives full algebra-map equality;
no equality of algebra maps is inferred from their values at spectrum
points. The whole algebra already is the base algebra, so no quotient
comparison equivalence is needed.

## The original inverse-pullback action

`globalSpectrumAction` packages the original inverse bounded maps as an
`Action TopCat G` on the actual `BanachSpectrum P`. Each group element
acts continuously because its inverse is a bounded ring map.
The unit and multiplication equations follow from the existing
inverse-pullback left action and the supplied homomorphism law.
`globalSpectrumAction_apply` exposes its concrete evaluation formula:

`(g • x)(a) = x ((ρ.toMonoidHom g).inv.toAlgHom a)`.

This constructs an action by continuous maps. Joint continuity in the
group and spectrum variables is a separate obligation; it is not
asserted or assumed here. The local identity proved above supplies the
full-map comparison needed to derive that continuity later from the
whole-domain local theorem.

## Provenance and scope

This is an internal consequence of `Domain.whole`,
`DomainSpectralAction.sectionAction_baseMap`, and the actual bounded
spectrum pullback construction. It adapts the whole-stabilizer and
global categorical-action portions of Worker 36's published
`StrictTestDomain/SpectralGlobalAction` to full represented
positive-polyradius domains. The strict construction uses an empty
rational quotient comparison; here the whole-domain structural map
is already the bounded identity.

The argument assumes no norm-continuous algebra orbit, reducedness,
nonempty spectrum, nonzero quotient or nontrivial scalar valuation.
It asserts neither comparison with all compact analytic-domain tests
nor a construction of general analytic spaces or étale sites.
