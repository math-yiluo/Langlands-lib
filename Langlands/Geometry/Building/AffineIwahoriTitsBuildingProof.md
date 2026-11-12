# Proof that the actual affine Iwahori–Tits system is the building Tits system

Author: Worker 4691.

This unit proves the published target
`Langlands.Geometry.Building.AffineIwahoriTitsBuildingStatement` of
`Langlands/Geometry/Building/AffineIwahoriTitsBuildingStatement.lean`. The theorem
`Langlands.Geometry.Building.affineIwahoriTitsBuilding` is stated at an arbitrary
universe `u`. Its type is exactly `AffineIwahoriTitsBuildingStatement.{u}`, so no
hypothesis is changed or added. The target's Lean/Markdown pair is unchanged.

## What is proved

For every nonarchimedean local field `F`, every group scheme `G` over `Spec F` with
`[IsAffineHom G.X.hom]`, every `P : ParahoricBuildingData G` satisfying
`P.apartment.SatisfiesApartmentAxioms P.centralizer`, normality of `P.normalizerZero`
and of `P.zeroSubgroup`, every chamber `C` of `P.affineRoots` and every
`e : P.affinePart ≃* AffineRootSystem.affineWeylGroup P.affineRoots` with
`P.AffineIwahoriTitsWith C e`, the theorem gives
`P.IsBuildingTitsSystem C P.affineTitsProjection (P.chamberSimpleInAffinePart e C)`.
These are the six fields of KP Axiom 4.1.9 on the existing quotient `B(G)` of (7.6.2):
the Tits axioms and saturation with Borel subgroup `P.chamberZeroStabilizerIn C`,
finiteness of the generating set, the bijection `Fc ↦ G(F)^0_{Fc}` from the facets of
`B(G)` onto the admissible parabolic subgroups, the face relation as reverse inclusion
of these stabilizers, and the identification of the apartments `h · A(S)` with the
restricted apartments.

The closing theorem writes the chamber as `C = facet P.affineRoots c` for a regular
point `c` and applies `ParahoricBuildingData.isBuildingTitsSystem_of_affineIwahoriTitsWith`.
The normality of `P.normalizerZero` is used as an instance, since it makes
`P.affinePart` and `P.affineTitsProjection` available. The normality of
`P.zeroSubgroup` is not used.

Notation below: `A = A(S)` is the apartment, `ι = P.apartmentMap : A → B(G)`, `Ψ` the
affine roots, `G⁰ = G(F)^0`, `N⁰ = N(F) ∩ G(F)^0`, `B = P_C ∩ G⁰ =
P.parahoricInZero C` the Borel subgroup of the given Tits system, and for a point `x`
of the closed chamber, `X(x) = P.facetSimpleInAffinePart e C (facet Ψ x)` the simple
reflections fixing the facet of `x`, pulled back along `e`.

## The implemented proof

### Preliminaries

- `Langlands.Group.TitsSystem.sameComponent_preimage` and
  `isAdmissibleType_preimage`: irreducible components and admissible types are carried
  back along a multiplicative equivalence. They move admissible types between the
  affine Weyl group and `P.affinePart`.
- `parahoric_le_fixer_of_mem_facetClosure`: `P_C` fixes `ι y` for every `y` in the
  closed chamber. Its `Z(F)^0` part fixes every point through the compact stabilizer,
  and its sharp part fixes `y` by antitonicity of the sharp fixer and the published
  `sharpFixer_singleton_le_of_mem_facetClosure`.
- `affineTitsProjection_apply` and `image_affineTitsProjection`: by the field
  `action_compatible` of `AffineIwahoriTitsWith`, the affine Weyl element
  `e (π n)` acts on `A` as the representative `n ∈ N⁰` itself.
- `normalizer_smul_image_apartmentMap` (`N(F)` acts on images by its action on `A`),
  `zeroStabilizerIn_smul` (stabilizers of translates are conjugates) and
  `smul_image_apartmentMap` (a translate of an image is its image in the translated
  chart).

### Face stabilizers of the chamber (KP Propositions 7.6.3 and 7.6.4(1))

- `smul_image_facet_eq_iff`: `n ∈ N⁰` stabilizes `ι(facet Ψ x)` exactly when
  `e (π n)` fixes `facet Ψ x` pointwise. The forward direction uses injectivity of
  `ι`, the published `apartmentMap_injective_of_rankOne` with
  `hasRankOneFactorization_actual`, and then the published `affineWeyl_facet_fixing`
  (an affine Weyl element stabilizing a facet setwise fixes it pointwise).
- `parahoricInZero_le_zeroStabilizerIn`: `B` stabilizes `ι(facet Ψ x)` for each `x` in
  the closed chamber, by the fixer lemma above.
- `coe_zeroStabilizerIn_facet` and `zeroStabilizerIn_facet_eq`: for `x` in the closed
  chamber, the stabilizer of `ι(facet Ψ x)` in `G⁰` is the standard parabolic subgroup
  `B ⟨X(x)⟩ B`. The proof applies the published
  `IsTitsSystem.coe_eq_standardParabolic`, which needs two inclusions. For points of `N⁰`
  in the stabilizer, `IsTitsSystem.mem_closure_of_mem` (Bourbaki, *Lie* IV §2 no.4,
  Theorem 2 Corollary 3, p.20, and no.5, Theorem 3, p.21, English 2002 edition) puts every letter of a reduced word of `π n` in the stabilizer, and each such
  letter is a simple reflection fixing `x`, by `smul_image_facet_eq_iff` and
  `facetSimpleReflections_facet_eq`. Conversely `exists_rep_mem_of_mem_closure`
  reduces representatives of `⟨X(x)⟩` to representatives of single reflections in
  `X(x)`. These fix the whole facet of `x`, hence stabilize its image. No geometric
  generation theorem for affine Weyl point stabilizers is needed.
- `facetSimpleInAffinePart_self_eq_empty` and
  `chamberZeroStabilizerIn_eq_parahoricInZero`: no simple reflection fixes the regular
  point `c`, so `X(c) = ∅` and the stabilizer of `ι C` in `G⁰` is
  `B ⟨∅⟩ B = B`. Thus the Borel subgroup of Axiom 4.1.9,
  `P.chamberZeroStabilizerIn C`, equals `P_C ∩ G⁰`.

### Types of faces

- `isAdmissibleType_facetSimpleInAffinePart`: each `X(x)` is an admissible type, from
  the published `isAdmissibleType_facetSimpleReflections`.
- `exists_facetSimpleInAffinePart_eq`: each admissible type is `X(x)` for some `x` in
  the closed chamber, from the published `exists_isFaceOf_facetSimpleReflections_eq`.
- The published `bijOn_facetSimpleReflections` (types determine faces) and
  `subset_facetClosure_iff_facetSimpleReflections_subset` (for `y, x'` in the closed
  chamber, `facet Ψ y ⊆ closure (facet Ψ x')` exactly when the facet-simple reflections
  of `x'` are among those of `y`, that is, `X(x') ⊆ X(y)` after pulling back along `e`)
  are used below.

### Every facet of `B(G)` is a `G⁰`-translate of a face of the chamber

- `exists_normalizerInZero_smul_facet`: every facet of `A` is `n • facet Ψ x` with
  `n ∈ N⁰` and `x` in the closed chamber. The point lies in the closure of some chamber
  (`exists_regularPoint_closure`), which is `w C` for an affine Weyl element `w`
  (`affineChamberSimpleTransitivity`). `w = e (π n)` by surjectivity of `π`, and the
  face of `n • C` is moved back with `normalizer_smul_isFaceOf`.
- `exists_eq_zero_smul_facet`: every facet `Fc = g · ι(Fa)` of `B(G)` equals
  `k · ι(facet Ψ x)` with `k ∈ G⁰` and `x` in the closed chamber. Here `g = k m` with
  `k ∈ G⁰` and `m ∈ N(F)` by the published `exists_zero_mul_normalizer` applied to the
  published `simplyConnectedCentralizerProduct` (KP Fact 2.6.22). Then
  `m · ι(Fa) = ι(m • Fa)` is the image of a facet (`normalizer_smul_isFacet`), handled
  by the previous lemma.
- `facetZeroStabilizer_eq_conjugate`: for such a presentation,
  `G⁰_{Fc} = k (B ⟨X(x)⟩ B) k⁻¹`.

### The fields of Axiom 4.1.9

`isBuildingTitsSystem_of_affineIwahoriTitsWith` rewrites the Borel subgroup by
`chamberZeroStabilizerIn_eq_parahoricInZero` and proves the six fields:

1. Tits axioms: the field `tits` of `AffineIwahoriTitsWith`.
2. Finiteness: the preimage under the injective `e` of the published
   `finite_chamberSimpleReflections`.
3. Saturation: the field `saturated` of `AffineIwahoriTitsWith`.
4. Bijection (`bijOn_facetZeroStabilizer_of_affineIwahoriTitsWith`). Maps into: by
   `facetZeroStabilizer_eq_conjugate` and admissibility of `X(x)`. Injective: equal
   conjugates of standard parabolics have equal types
   (`IsTitsSystem.eq_of_conjugateSubgroup_eq`), so the faces coincide by
   `bijOn_facetSimpleReflections`; then `k₂⁻¹ k₁` lies in the standard parabolic
   (`IsTitsSystem.mem_of_eq_conjugate`), that is, it stabilizes the image of the face,
   so the two facets are equal. Surjective: an admissible parabolic `g (B ⟨X⟩ B) g⁻¹`
   with `X = X(x)` is the stabilizer of the facet `g · ι(facet Ψ x)`.
5. Face relation (`facetPrecedes_iff_of_affineIwahoriTitsWith`). Write
   `Fc' = k' · ι(facet Ψ x')`. Forward: the published
   `exists_apartment_faces_of_facetPrecedes` gives faces in the translated apartment
   `k' · A`. Injectivity of the translated chart (`translatedApartmentMap_injective`)
   identifies the upper face with `facet Ψ x'`. The lower face is `facet Ψ y` for `y`
   in the closed chamber, so `X(x') ⊆ X(y)` and the standard parabolics are ordered
   (`IsTitsSystem.standardParabolicSubgroup_le_iff`). Backward: write
   `Fc = k · ι(facet Ψ x)`, `L = B ⟨X(x)⟩ B` and `L' = B ⟨X(x')⟩ B`. From
   `k' L' k'⁻¹ ≤ k L k⁻¹`, `IsTitsSystem.mem_of_conjugate_le` gives `k⁻¹ k' ∈ L`, hence
   `L' ≤ L` by `conjugateSubgroup_eq_self`, hence `X(x') ⊆ X(x)` and
   `facet Ψ x ⊆ closure (facet Ψ x')`. Since `k⁻¹ k'` stabilizes `ι(facet Ψ x)`,
   `Fc = k' · ι(facet Ψ x)`, which exhibits `Fc` as a face of `Fc'` in `k' · A`.
6. Apartments (`apartmentFacetStabilizers_eq_of_affineIwahoriTitsWith`). First,
   `facetStabilizersIn_apartmentImage_of_affineIwahoriTitsWith` shows that the
   stabilizers of the facets contained in `ι(A)` form the standard restricted apartment.
   A facet in `ι(A)` is an image of a facet of `A` (the published
   `exists_isFacet_image_of_isFacet`), hence an `N⁰`-translate of the image of a face
   of the chamber. The membership criterion is the published
   `IsTitsSystem.mem_restrictedApartment_iff_conjugate`. For `h = k m` with `k ∈ G⁰` and
   `m ∈ N(F)` (again KP Fact 2.6.22), `m` stabilizes `ι(A)`
   (`normalizerPoints_le_stabilizer_apartmentImage`). The published
   `facetStabilizersIn_smul` and `IsTitsSystem.image_conjugateSubgroup_restrictedApartment`
   then identify the facet stabilizers in `h · ι(A)` with the restricted apartment of `k`.

The development check of this module reported no errors or warnings. The axioms of
`affineIwahoriTitsBuilding` are `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

The target is the content of KP Propositions 7.6.3 and 7.6.4(1) and Remark 7.6.5
(Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*, 2023, printed pp. 264–266 / PDF
pp. 295–297) on the quotient (7.6.2), with KP Axiom 4.1.9 (printed p. 161 / PDF p. 192)
as the conclusion. KP defines `B(G)` as the restricted building of the Iwahori–Tits
system and compares it with the quotient using Proposition 4.4.4. The implemented route
works directly on the Library's quotient. It computes the stabilizers of the images of
faces of one chamber (the stabilizer part of Propositions 7.6.3 and 7.6.4(1)) by the
Tits-system subgroup classification, transports them to all facets with
`G(F) = G(F)^0 N(F)` (KP Fact 2.6.22, through its published Library proof), and reads
off the three comparisons of Axiom 4.1.9.

This unit is conditional only in the sense of the target: it is a theorem about supplied
`ParahoricBuildingData` satisfying the apartment axioms, with a supplied actual affine
Iwahori–Tits system. It does not construct such data and does not prove
`AffineIwahoriTitsStatement`.
