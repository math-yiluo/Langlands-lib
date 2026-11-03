# Reflection of finiteness of the full scheme-theoretic centre

Author: Worker 1347.

In arbitrary universe `u`, this helper constructs a finite representative of
the full scheme-theoretic centre over a field from a finite representative
after any field extension, provided the extended group is affine. It also
constructs the actual comparison isomorphism after extension, preserving the
inclusion into the ambient group.

## General fpqc reflection

For any base scheme `S`, `IsSchemeTheoreticCenter z` means that the actual
homomorphism `z : Z ⟶ G` is a closed immersion and its range is the full
`center G`. This centre condition quantifies all test schemes and all further
test morphisms. `HasFiniteCenter G` means there exists such a representative
with finite structural morphism `Z.X.hom`. Neither predicate discards
nilpotents.

`IsSchemeTheoreticCenter.isFinite_of_hasFiniteCenter` proves that every
representative of this centre is finite whenever one is finite. Both
representatives represent the same subgroup functor, so the existing
`isoOfIsRepresentedBy` gives an actual isomorphism between their group
schemes over `S`. The original structural morphism is the composite of the
isomorphism and the finite representative's structural morphism and is
therefore finite.

For any `b : S' ⟶ S` that is surjective, flat and quasi-compact,
`IsSchemeTheoreticCenter.isFinite_of_baseChange` detects finiteness of an
existing centre representative from `HasFiniteCenter` of the base-changed
group. The centre base-change theorem identifies the actual pullback
representative as a full centre. The preceding comparison makes its
structural morphism finite. Fpqc descent of finite morphisms then proves
finiteness of the original structural morphism.

`hasFiniteCenter_of_baseChange` consequently proves `HasFiniteCenter G`
assuming that a centre representative exists over `S` and that the
base-changed group has finite centre. The existence hypothesis is explicit
in this general-base helper.

## Field-extension construction

Let `k K : Type u` be arbitrary fields with an `Algebra k K`, and let
`b = Spec.map (CommRingCat.ofHom (algebraMap k K))`. Write
`G_K = (GroupScheme.baseChange b).obj G`.

`schemeTheoreticCenterExistence_of_isAffineHom` constructs an actual closed
representative of the full centre of any affine group scheme over a field.
Apply the published `fieldFixedSubgroupRepresentability` to self-conjugation
by `G`, and use `conjugation_id_fixedSubgroup_eq_center`. This reuses the
implemented centre-existence argument under the affineness hypothesis that
its proof actually needs.

`HasFiniteCenter.of_fieldExtension` assumes `IsAffineHom G_K.X.hom` and
`HasFiniteCenter G_K` and concludes `HasFiniteCenter G`. It first applies
`fieldExtensionAffineDescent` to reflect affineness of the underlying scheme.
The preceding centre-existence construction then supplies a representative
over `k`. Every extension of fields is fpqc, so the general reflection
helper makes this representative finite. There is no premise of affineness,
smoothness, connectedness, reductivity or centre representability on the
original group.

`FiniteCenter.of_fieldExtension` supplies actual `FiniteCenter G` data from
`IsAffineHom G_K.X.hom` and supplied data `C : FiniteCenter G_K`. It uses
classical choice on the existential conclusion just proved. This choice
supplies the actual group, its inclusion, its full-centre property and its
finite structural morphism.

`FiniteCenter.fieldExtensionIso` compares the pullback of this constructed
centre to `C.group` by the existing isomorphism between representatives.
`FiniteCenter.fieldExtensionIso_hom_comp` proves the exact recovery equation:

```text
fieldExtensionIso.hom ≫ C.inclusion =
  (GroupScheme.baseChange b).map (C.of_fieldExtension hGAff).inclusion.
```

Thus recovery respects the actual inclusion, and is more than an abstract
isomorphism of the underlying groups.

Finally `IsSemisimple.hasFiniteCenter_of_fieldExtension` derives the
finite-centre conclusion for an original group from semisimplicity of its
scalar extension. Its only premise is `IsSemisimple G_K`; that predicate
supplies both affineness and finite centre after extension.

## Provenance and retained obligations

This is an internal derivation from the implemented Library centre
representability, full centre base change, isomorphism of subgroup
representatives, arbitrary field-extension affineness descent, and fpqc
descent of finite morphisms. The latter helper is imported from
`Langlands.AlgebraicGeometry.Morphisms.FpqcFiniteDescent`. No unproved
reflection assertion is supplied as a hypothesis, and no new external
literature assertion is introduced.

All fields and their extensions are unrestricted. Inseparable and
transcendental extensions, imperfect fields, positive characteristic and
finite nonreduced centres remain in scope. No chosen centre over the
original field is supplied to the field-extension construction.

The result proves the finite-centre component of semisimplicity reflection.
Reflection of connected reductivity, full semisimplicity reflection,
construction of the covering descent datum, and the simply connected cover
existence theorem remain separate obligations.
