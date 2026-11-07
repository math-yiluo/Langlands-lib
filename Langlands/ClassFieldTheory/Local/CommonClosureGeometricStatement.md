# Normalized common-closure reciprocity families are geometric

Statement only; no proof is claimed.

Let `F` be a p-adic field and `eC : LocalFactor.CommonClosure.ReciprocityFamily F` a
candidate reciprocity family. Such a family gives, for every finite intermediate field `L` of
the common algebraic closure of `F`, a topological isomorphism from the abelianized
Weil subgroup fixing `L` to `Lˣ`. Assume `eC` satisfies
`LocalFactor.CommonClosure.NormalizedReciprocity F eC`, the Library's
`NormalizedSystemRelation`: the norm, transfer, conjugation, density and completion
relations, with the geometric normalization `‖e_L(w)‖_L = q_F^{-deg w}`.

`LocalClassField.CommonClosureGeometricStatement.{u, v}` asserts two things.

1. Every candidate `e : LocalFactor.RankOne.ReciprocityCandidate F` with
   `Correspondence.IsBaseReciprocity F e eC` satisfies
   `GeometricWeilReciprocityRelation F F.canonicalTopologicalData e`. Such an `e`
   agrees with the bottom component of `eC` under the isomorphism `⊥ ≃ F`.
   The Library's `Correspondence.baseReciprocityCandidate F eC` is one such `e`.
2. For every p-adic field `E : PadicField.{v} p` and every `g : F →ₐ[ℚ_p] E`,
   the candidate `LocalClassField.extensionReciprocityCandidate F E g eC` satisfies
   `GeometricWeilReciprocityRelation E E.canonicalTopologicalData`. This candidate is
   the component of `eC` at the image of `E` in the common closure, transported to `E`.

`GeometricWeilReciprocityRelation` consists of the geometric order normalization and the
geometric profinite reciprocity relation. The latter includes the norm-residue
isomorphisms for all finite abelian extensions and the Frobenius normalization on
unramified elements.

## Provenance and literature

The provenance is derived. Tate, *Number theoretic background* (Corvallis 1979), §1.1,
printed pp. 3–4 (PDF pp. 12–13), defines a Weil group by isomorphisms
`r_E : C_E → W_E^ab` for all finite extensions `E` of `F` in a fixed closure. They
satisfy the conjugation axiom (W2), the transfer axiom (W3) and the projective-limit
axiom (W4), and the norm diagram (1.2.2) follows. In §1.4.1, printed p. 6 (PDF p. 15),
for `F` local nonarchimedean, he states that the maps `r_E` are the reciprocity law
homomorphisms. He uses the geometric convention: `r_E(a)` acts on the residue field
through `‖a‖_E`, so uniformizers correspond to inverse Frobenius. The Library's
`NormalizedSystemRelation` formalizes the family relations, with inverse maps
`W_L^ab → Lˣ`, at all finite intermediate fields of one closure, including non-normal
ones. The Library's `GeometricWeilReciprocityRelation` formalizes the geometric local
reciprocity law of a single field. This statement asserts Tate's identification of the
two at every finite extension. For a standalone extension `E`, it uses the Library's
transport of the family component through `extensionImageWeilEquiv` and
`extensionIntermediateUnitsEquiv`.

The order part of clause 2 is already a Library theorem,
`extensionReciprocityCandidate_geometricOrder`, and uniqueness of normalized families
is the Library theorem `commonClosureReciprocityUniqueness`. What remains are the
profinite norm-residue and Frobenius clauses at each field.

## Use

With `geometricWeilReciprocityUniqueness`, the statement identifies these transported
components with any geometric candidate supplied elsewhere, for example the candidates
`e_u` in `IsLocalRelativeWeilMap` and in the transfer clauses of the local restriction
statements. The local epsilon algebra for the twisted relative Weil functional equation
(task cc3ec74b) writes its rank-one factors through these transported components
(`RelativeWeilLocalEpsilonTransport`). It therefore needs this comparison to identify
those factors with the local epsilon factors of Hecke characters.
