# Generated smooth families under arbitrary field extension

This internal module proves that closed algebraic generation by a family of smooth connected affine groups is preserved by every field extension. It also constructs an actual comparison isomorphism between the base-changed generated subgroup and any independently chosen generated representative over the extension field, preserving their inclusions into the extended ambient group.

Let `k : Type u` be a field and `K : Type u` an extension field with its specified `Algebra k K`. Let `G` be a smooth affine group scheme over `Spec k`. Let `I : Type v` be an arbitrary index type and `a j : A j ⟶ G` a family with every `A j` smooth, affine and connected. The universes `u` and `v` are independent, and `I` need not be finite or nonempty. Connectedness of `G` is not assumed.

`IsGeneratedByFamily A a i` means that `i : H ⟶ G` is a closed subgroup inclusion, every family map factors through it as an actual scheme morphism, and its full subgroup-functor range lies in every closed subgroup through which the family factors. This minimality ranges over arbitrary closed competitors, including nonsmooth and nonreduced ones, and containment is on every scheme test. It does not mean merely generation of rational points.

## Preservation of generation

`IsGeneratedByFamily.baseChange K A a hA hi` proves that the actual base-changed inclusion still has this generation property for the actual base-changed family. There are no additional smoothness or connectedness assumptions on a supplied representative `H`; the hypotheses are its original generation property and the displayed family and ambient geometry. The extension may be inseparable, transcendental or infinite. Neither field is assumed algebraically closed or perfect, and there is no characteristic restriction. The two fields have the same universe `u`, as required by the existing scheme base-change interfaces.

The maps `FamilyBaseChange.extension` and `FamilyBaseChange.bc` are abbreviations for the actual field-extension morphism `Spec K ⟶ Spec k` and the resulting group-scheme base-change functor.

The difficult point is minimality against an arbitrary closed competitor `q : Q ⟶ G_K` which contains every extended family map. The proof fixes this competitor and calls a ground-field subgroup admissible when it is closed, smooth, affine and connected, and its entire extension has range in `q`. It then proceeds as follows.

1. The trivial ground-field subgroup is admissible. The range of its extended inclusion is bottom, by the published range/base-change and unit-subgroup identities.
2. The Lie dimension of an admissible subgroup is bounded by that of `G`, since a closed inclusion induces an injective differential. A largest occurring natural-number dimension therefore gives an admissible subgroup `M` of maximal dimension.
3. For each generator `A j`, take the existing pointed smooth connected generated image of the multiplication morphism `M × A j ⟶ G`. Call it `D`. Its two factors map into it, and a positive ordered power of the pointed source dominates `D`.
4. The full extension of `D` remains inside `q`. The existing `EnvelopeBaseChange.range_baseChange_le_of_points` proves this from the dominant ordered power. Every scheme-valued point of the extended product maps into `q` because both extended factors do and `q` is a subgroup. That published lemma uses quasi-compact schematic dominance after flat field extension and actual closed factorization, so this step does not extrapolate from rational points or assume that topological dominance is preserved without a scheme-theoretic argument.
5. Thus `D` is admissible. Its dimension is at most that of `M`. The closed inclusion `M ⟶ D` is an isomorphism: a proper closed inclusion between the smooth connected affine groups would have strictly smaller Lie dimension. Consequently the map `A j ⟶ D` factors through `M`.
6. The maximal admissible subgroup contains the entire original family. Original minimality therefore puts the supplied generated subgroup `H` inside `M`. Range containment commutes with actual base change, so `H_K` lies in `q`.

The internal result `FamilyBaseChange.exists_closed_containing_family` expresses the maximal-subgroup conclusion. No finite generating subfamily or extra generic-generation premise is assumed. The proof also treats the empty family, using the trivial admissible subgroup.

The other two clauses of `IsGeneratedByFamily` are preserved directly. Closedness survives base change. For each generator, representability turns its original factorization into a group homomorphism; applying the actual base-change functor gives the extended factorization. Together with the preceding minimality proof this gives the full generation statement on all scheme tests.

## Actual comparison isomorphism

The primary entry `IsGeneratedByFamily.baseChangeIso K A a hA hi q hq` additionally takes any closed generated representative `q : Q ⟶ G_K` of the extended family. It returns an actual group-scheme isomorphism `H_K ≅ Q`. The newly proved generation property for `H_K` and the supplied generation property for `Q` give both all-test range containments, hence equal subgroup functors. The published uniqueness of representing group schemes then constructs the isomorphism.

`IsGeneratedByFamily.baseChangeIso_hom_comp` proves that its forward map followed by `q` is exactly the base-changed original inclusion. Thus the comparison is compatible with the actual ambient group, rather than just an abstract isomorphism of the source groups. No isomorphism between the ambient groups, reductive classification statement or common-torus isomorphism theorem is used.

## Provenance and use

This is an internal combination of existing arbitrary-family generation, pointed-image smooth connected generation with dominant ordered powers, the published field-extension containment criterion for those generated images, closed-subgroup Lie dimension comparison, and uniqueness of representatives. The field-extension containment criterion is reused in its already general form; no assertion that all source groups are tori is made.

For the common-torus graph proof, the theorem permits comparison of a ground-field generated graph with a generated representative of its pulled-back family. Identifying the appropriate pulled-back graph families and proving their projections invertible remain further steps. This module alone proves neither Levi gluing nor the arbitrary-field common-torus isomorphism theorem.
