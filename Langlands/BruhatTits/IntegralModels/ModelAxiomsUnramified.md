# KP Axiom 4.1.20 on supplied data from the unramified statements

This module proves KP Axiom 4.1.20, `M.SatisfiesModelAxioms P`, for a building
model family `M` over `↥𝒪[F]` that it constructs. Here KP is Kaletha–Prasad,
*Bruhat–Tits theory: a new approach* (2023), Axiom 4.1.20 on printed p. 163 /
PDF p. 194. Following KP §§9.2.5 and 9.5, the proof constructs models over the
integers of the maximal unramified extension `K = inertiaFixedField F` and
descends them. The main theorem takes the following seven hypotheses.

| Hypothesis | Statement | Source |
| --- | --- | --- |
| `hpar` | `UnramifiedParahoricModelStatement` | KP Theorems 8.3.2 and 8.3.13 over `K` |
| `hdesc` | `UnramifiedSmoothModelDescentStatement` | KP Fact 2.10.16 |
| `hzero` | `UnramifiedZeroDescentStatement` | KP Proposition 9.3.24 for the zero-subgroup intersection, with derived Galois-stability clauses |
| `hext` | `UnramifiedSmoothHomExtensionStatement` | KP Corollary 2.10.10 |
| `hclos` | `UnramifiedOneFixerClosureStatement` | KP 7.4.4(3), §7.7, 7.7.5(1) |
| `hroot` | `UnramifiedZeroFixerAffineRootStatement` | KP 7.4.1, 7.4.4(3), 7.7.5(1) |
| `htor` | `UnramifiedTorusClauseStatement` | KP §9.2.5, 8.3.14(1) |

The proof uses lemmas from `UnramifiedModelFamily`,
`UnramifiedModelAxioms`, `RelativeComponentModelLemmas`,
`SimplyConnectedZeroPoints`, `ApartmentFacetBounds` and
`GeneralMorphismAxiomsUnramified`.

Throughout, `G(K)^1` is the common kernel of the valuations of the rational
characters of `G_K`, and `G(F)^1` is the Library `rationalCommonNormKernel G`.

## Point descent lemmas

Let `B` be valuation building data for `G` and `C` building data for `G_K`. Let
`e : B.ReducedBuilding → C.ReducedBuilding` be injective and equivariant along
`rationalExtend`. Let `M` be an integral model of `G` over `𝒪[F]` and `Y` a
subset of the reduced building of `B`.

- `integralPoints_eq_of_unramified_one`: if the unramified base change of `M`
  has integral points `G(K)^1 ∩ Fix(e '' Y)`, then `M` has integral points
  `Fix(Y) ∩ G(F)^1`. The proof pulls back along `G(F) → G(K)` and uses three
  Library lemmas:
  - `integralPoints_eq_comap_baseChangeUnramified`: the integral points of `M`
    are the preimage of those of its base change;
  - `MaximalUnramified.characterValuationKernel_comap`: `G(K)^1` pulls back to
    `G(F)^1`;
  - `MaximalUnramified.pointwiseFixer_comap`: `Fix(e '' Y)` pulls back to
    `Fix(Y)`. This uses the injectivity and equivariance of `e`.
- `integralPoints_eq_of_unramified_zero`: assume `UnramifiedZeroDescentStatement`
  and let `G` be connected reductive. Let `Z0` be a zero-subgroup datum over
  `F` and `E` a zero datum over `K`. If the unramified base change of `M` has
  integral points `E.zeroPoints ∩ Fix(e '' Y)`, then `M` has integral points
  `Fix(Y) ∩ G(F)^0`, where `G(F)^0 = Z0.zeroSubgroup`. The pull-back of
  `E.zeroPoints` to `G(F)` is `G(F)^0` by the third clause of the zero descent
  statement (KP Proposition 9.3.24).

## The main theorem

`BuildingModelFamily.exists_satisfiesModelAxioms_withBaseChange_of_unramified`
retains the integral-point identifications of both base-changed models.
For each index \(\Omega\), the full model gives \(G(K)^1 \cap
\operatorname{Fix}(e(\Omega))\) and the neutral model gives
\(G(K)^0 \cap \operatorname{Fix}(e(\Omega))\). Both identities come from
`exists_relativeComponentModelData_of_unramified`, which is used to construct
the models of the family. The following specialization retains the neutral
identity for use in constructing the quotient family.

`BuildingModelFamily.exists_satisfiesModelAxioms_of_unramified`. Let
`P : ParahoricBuildingData G`, a realization `R` and a splitting `T` satisfy
the seven predicates of the target statement `IntegralModelAxiomsStatement`.
Let `C`, `A`, `e`, `a` satisfy the following six conclusions of
`UnramifiedApartmentDescentStatement`.

- `e` is injective and equivariant along `rationalExtend`;
- `e (apartmentMap w) = C.apartmentMap (a w)`;
- every image point of `e` is fixed by the semilinear Galois action `A`;
- `a` pulls facets of `C` back to facets;
- the character-valuation kernel of the base-changed maximal split torus `S`
  fixes the image of the apartment.

Under the seven hypotheses of the table, there is a building model family `M`
over `𝒪[F]` with two properties:

- `M.SatisfiesModelAxioms P`;
- for every index `Ω`, the unramified base change of the neutral model of
  `M.model Ω` has integral points `E.zeroPoints ∩ Fix(e '' Ω)`, where
  `E = unramifiedZeroDatumOfParahoric P`.

`MorphismAxiomsUnramified` uses the second property to prove Axiom 4.1.22.

## Proof

Two facts about `P` come first:

- `hbdd` gives boundedness of every apartment presentation `Ωa` of an index
  by `isBoundedSubset_of_buildingModelIndex`, from the seven predicates.
- `hface`: a face lies in the apartment closure of a facet containing it. This
  is `subset_apartmentClosure_of_isFaceOf` (`ApartmentFacetBounds`).

### The models

For each index `Ω`, the image `e '' Ω` is a translate of a nonempty bounded
subset of the apartment of `C` (`exists_unramified_presentation`). It is
Galois-fixed because every image point of `e` is. Then
`exists_relativeComponentModelData_of_unramified` (from `hpar`, `hdesc`,
`hzero`) gives `model Ω : RelativeComponentModelData ↥𝒪[F] F G` whose base
changes have these integral points:

- full model: `G(K)^1 ∩ Fix(e '' Ω)`;
- neutral model: `E.zeroPoints ∩ Fix(e '' Ω)`.

The second identity is the extra conclusion of the theorem.

### The integral tori

Let `Ω = g · apartmentMap '' Ωa`. Then `htor` applies with these data:

- `Ya = a '' Ωa`, which is nonempty and bounded;
- the kernel `S(K)^1` fixes `C.apartmentMap '' Ya`, by the last descent
  conclusion and `he_apt`;
- the neutral points of `model Ω` are `E.zeroPoints ∩ Fix(g_K · apartmentMap '' Ya)`,
  by `image_translatedApartmentMap`.

It gives an integral torus for the inclusion `i ≫ Int(g)` satisfying the
torus clause. These tori are the field `torus` of the family, and they give
the clause `torus_clause`.

### The morphisms

For a pair `Ω ≺ Ω'` requiring a morphism, `one_inf_pointwiseFixer_le` (from `hclos`)
gives `G(K)^1 ∩ Fix(e '' Ω') ≤ G(K)^1 ∩ Fix(e '' Ω)`. Intersecting with
`G(K)^0 ≤ G(K)^1` gives the same inclusion for `E.zeroPoints`. Then
`nonempty_hom_of_unramified_le` (from `hext`) gives model morphisms over the
identity of `G`, one between the full models and one between the neutral
models. They commute with the inclusions by `comp_hom_eq_of_generic`. They
form a `RelativeComponentModelHom (model Ω') (model Ω)`.

### The clauses of Axiom 4.1.20

The family is `⟨model, morphisms, torus⟩` and `building_eq` holds by `rfl`.

- **Full and neutral points.** `integralPoints_eq_of_unramified_one` and
  `integralPoints_eq_of_unramified_zero`, the latter with the zero datum
  `P.zeroDatum` of `P`. They give `Fix(Ω) ∩ G(F)^1` and `Fix(Ω) ∩ G(F)^0`.
- **Facet constancy (4.1.20(1)).** Let `Ω` lie in a facet `F_b`, and write
  `F_b = g · apartmentMap '' facet(x)`. Then
  `Ω = g · apartmentMap '' (facet(x) ∩ preimage of Ω)`.
  - The facet of `x` is bounded (`isBoundedSubset_of_isFacet_of_satisfiesApartmentAxioms`,
    from `P.SatisfiesApartmentAxioms`).
  - By the facet clause of the descent, `a` maps `facet(x)` into the facet of
    `a x` for `C.affineRoots`.
  - The images of the two presentations therefore lie in one facet of `C`. By
    `forall_nonneg_iff_of_subset_facet` they have the same nonnegative affine
    roots.
  - `hroot` then gives equal `E.zeroPoints`-fixers. By
    `exists_isIso_neutral_of_unramified_eq` (from `hext`), the neutral models
    of `Ω` and `F_b` are isomorphic over the identity.
- **Closure invariance (4.1.20(2)).** Let `Ω = g · apartmentMap '' Ωa` and let
  `Ω'` be the index of the closure of `Ωa`. The images in `C` are
  `a '' Ωa ⊆ a '' cl(Ωa) ⊆ cl(a '' Ωa)`, by `subset_closure` and the continuity
  of `a` (`image_subset_closure_image`). `hclos` says the `G(K)^1`-fixers of
  the two ends agree, so all three agree by antitonicity. Intersecting with
  `G(K)^0 ≤ G(K)^1` (`inf_eq_inf_of_le_of_inf_eq`) gives equal neutral points.
  `exists_isIso_neutral_of_unramified_eq` gives the isomorphism.
- **Torus clause (4.1.20(3)).** From the tori above.
- **Simply connected case (4.1.20(4)).** If `G` is simply connected, so is
  `G_K` (Library `isSimplyConnectedFieldExtension`). Then
  `E.zeroPoints = ⊤` (`UnramifiedZeroDatum.zeroPoints_eq_top_of_isSimplyConnected`,
  `SimplyConnectedZeroPoints`), so the full points `G(K)^1 ∩ Fix` lie in the
  neutral points `Fix`. `nonempty_hom_of_unramified_le` gives a morphism from
  the full model back to the neutral model. Together with the inclusion,
  `isIso_hom_of_hom` makes the inclusion an isomorphism.

The theorem has `set_option maxHeartbeats 4000000`.

## Sources

- KP Axiom 4.1.20, printed p. 163 / PDF p. 194. The November 2024
  corrections (PDF p. 27) keep it in corrected Definition 4.1.26.
- KP §9.2.5, printed pp. 327–328 / PDF pp. 358–359, descends the models
  to the valuation ring of `F`. Section 9.5, printed pp. 363–364 / PDF
  pp. 394–395, verifies the axiom using the zero-subgroup intersection
  of Proposition 9.3.24 (printed p. 343 / PDF p. 374).
- The sources of the seven hypotheses are given in the Markdown of their
  statement modules.

The route is derived. KP get Axiom 4.1.20 over `F` by unramified descent of
the constructions of Chapters 7 and 8. This proof keeps that route, but works
through integral points after base change to the maximal unramified integers.
Over the finite residue field of `𝒪[F]`, integral points alone do not
determine a smooth model, so they cannot be used directly.
