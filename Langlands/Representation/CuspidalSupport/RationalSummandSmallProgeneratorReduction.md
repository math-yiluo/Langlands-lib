# Renard VI.4.1 for one summand: reduction to the structural inputs

Worker 1637. Source: David Renard, *Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026, registered as `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. Locators: VI.4.1, the opening paragraphs, the Proposition and its proof, printed p.149 / PDF p.155; VI.3.2, printed pp.143–144 / PDF pp.149–150. These pages were read for this unit.

## What the module proves

This module proves both targets of VI.4.1 for one summand, `RationalSummandSmallProgeneratorStatement` and `RationalSummandHomEquivalenceStatement`, **conditionally** on three explicit structural propositions. These propositions are not proved here, so the module does not discharge either target. The three inputs are exactly the inputs of the published conditional reduction for the full-restriction progenerator Π₁ (`RationalNormKernelSmallProgeneratorReductionStatement`), with the compactness input derived from the published VI.2.1 implication:

- `RationalSpecialVertexCompactInputsStatement.{uF}`, or the stronger `Langlands.BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement.{uF}`, which implies it by the published `rationalSpecialVertexCompactInputs_of_jointBasis`;
- `RationalNormKernelFiniteRestrictionStatement.{uF, uV}` (VI.3.2(ii));
- `RationalNormKernelTwistEquivalenceStatement.{uF, max uF uV, max uF uV}` (VI.3.2(iii)).

Write H for the actual rational points with the canonical topology, H⁰ = `Plancherel.rationalCommonNormKernel G`, Π = `rationalNormKernelSummandInduction G ρ` and Π₁ = `rationalNormKernelCompactInduction G π`.

The module's only new definition is the morphism `rationalSummandInductionToUniversal` described below; everything else is a theorem.

### Objectwise results

Throughout, G is an affine group scheme locally of finite type over a nonarchimedean local field F, π is a smooth representation of H with carrier in `Type uV`, ρ is a smooth representation of H⁰ with carrier in `Type uV`, and j : ρ ⟶ `SmoothRep.restrictSubgroup H⁰ π`.

- `compactOpen_cofinal_of_isOpen`: in a locally compact nonarchimedean group, every open subgroup K of an open subgroup contains a compact open subgroup of that open subgroup. The proof takes a compact open subgroup V of the ambient group inside the image of K (published `Langlands.Jacquet.exists_isCompact_openSubgroup_subset`), pulls it back along the inclusion, and gets compactness from `IsInducing.isCompact_preimage'`, since V lies in the range of the inclusion.
- `rationalSummandInductionToUniversal`: the compact induction of j, a morphism Π ⟶ Π₁. Its target is Π₁ because Π₁ is, by definition, the compact induction of the full restriction. `rationalSummandInductionToUniversal_injective`: if j is injective, so is this morphism, since it is postcomposition with j on functions.
- `rationalNormKernelSummandInduction_mem`: if Π₁ is in the block `rationalInertiaBlockProperty G (rationalInertiaBaseLift G π)` and j is injective, so is Π, because the block is closed under subquotients and Π is a subrepresentation of Π₁.
- `exists_nonzero_rationalNormKernelSummandInduction`: if ρ is irreducible and j injective, then Π has a nonzero map to every D inertia-related to the lifted π. Write D ≅ χ·π_lift. The published `rationalNormKernelTwistRestrictionEquiv` and `Induction.restrictAlongEquiv` give an H⁰-isomorphism E from the restriction of π to the restriction of D, since unramified characters are trivial on H⁰. The map is `Induction.cosetSum` of E ∘ j (Frobenius reciprocity (VI.4.1.1) for the open subgroup H⁰). On the unit function of a nonzero v ∈ ρ it takes the value E(j v) ≠ 0 (`Induction.cosetSum_comp_unitMap`).
- `finite_rationalNormKernelSummandInduction`: if ρ is irreducible, then Π is finitely generated over `MonoidAlgebra ℂ H`. Any nonzero vector generates the simple module ρ, and the published `Induction.finite_compactInduced_of_finite` transfers finite generation to the compact induction from the open subgroup H⁰. This is Renard's finite-type argument with the functions f_{i,w} of (VI.4.1.2).
- `rationalNormKernelSummandInduction_projective` (H locally compact and nonarchimedean): if the whole restriction of π to H⁰ has compact smooth-dual coefficients and j is injective, then Π is projective among smooth representations of H. The published `HasCompactSmoothDualCoefficients.of_injective`, with the cofinality above for H⁰ (open by `isOpen_rationalCommonNormKernel`), gives compact coefficients of ρ. The published `Induction.projective_compactInduced_of_compactCoefficients` then gives projectivity of Π. Hausdorffness and total disconnectedness of H are derived from the local field, as in the published projectivity of Π₁.
- `isRationalInertiaSmallProgenerator_rationalNormKernelSummandInduction` (H locally compact and nonarchimedean, G connected reductive, π and ρ irreducible, j injective): from compact coefficients of the whole restriction of π and the finite-restriction and twist-equivalence statements, `IsRationalInertiaSmallProgenerator G π Π` holds. Its five parts are:
  1. membership: the published `rationalNormKernelCompactInduction_mem_of_restriction` gives Π₁ in the block, so Π is in the block;
  2. lifting: projectivity in the block, from ambient projectivity by the published `rationalInertiaBlock_projective_of_projective`, with `Projective.factorThru`;
  3. faithfulness of `preadditiveCoyonedaInt P`: the published `SmoothRep.faithful_preadditiveCoyonedaInt_of_projective_subquotients`, whose detection hypothesis is supplied by the nonzero maps above, since every irreducible subquotient of a block object is inertia-related to the lifted π;
  4. coproducts of the block indexed by `Type (max uF uV)`: the published `rationalInertiaBlock_hasColimitsOfShape`;
  5. coproduct preservation: the published `rationalInertiaBlockHom_preservesCoproducts_of_finite` with the finite generation above.

### Statement-level results

- `rationalSummandSmallProgenerator_of_specialVertexInputs`: the three inputs (special-vertex form) imply `RationalSummandSmallProgeneratorStatement.{uF, uV}`. For the data of the statement, the special-vertex input gives an apartment datum, a special vertex and the special compact, simultaneous basis and finite Cartan covering properties of its subgroup. The published `Langlands.Aubert.General.rationalCuspidalCompactRestriction` turns these, together with the statement's standard-cocharacter, root-system and unipotent-closedness premises and the cuspidality of π, into compact coefficients of the restriction of π to H⁰. The objectwise theorem then applies.
- `rationalSummandSmallProgenerator_of_jointBasis`: the same with the joint special-compact basis existence statement.
- `rationalSummandHomEquivalence_of_jointBasis`: the same inputs imply `RationalSummandHomEquivalenceStatement.{uF, uV}`, by `rationalSummandHomEquivalence_of_smallProgenerator` from `RationalSummandHomEquivalenceReduction`.

No admissibility, compactness of ρ, finite-dimensionality, splitness, characteristic, finite-length or abelianness premise is added. Compactness of ρ is derived from compactness of the whole restriction. The objectwise theorem does not use cuspidality: it is used only, in the statement-level theorem, to derive that compactness. The cuspidality is that of the statements, `Aubert.General.IsCuspidal` along every proper actual standard parabolic.

## Correspondence with Renard

Renard takes ρ to be an irreducible summand of Res π. The targets take any irreducible ρ with an injective H⁰-map into Res π, and the proof uses only that injection. The source steps correspond as follows.

- Projectivity. Renard uses the adjunction (VI.4.1.1), projectivity of the compact ρ in M(⁰G) and semisimplicity of restrictions of block objects. Here projectivity of Π among all smooth representations comes from compactness of ρ (inherited from Res π) and the published projectivity of compact inductions of compact representations from open subgroups.
- Generation. Renard shows Hom_G(Π, τ) ≠ 0 for every nonzero τ in the block. Here the published detector criterion uses nonzero maps from Π to the irreducible subquotients of block objects, together with projectivity. Each such map comes from j and Frobenius reciprocity, so no conjugacy of the summands is needed.
- Finite type and smallness. As in Renard, ρ is of finite type and so is Π. The published finite-generation coproduct lemma gives smallness.
- Membership of Π in M(G)[π] is implicit in Renard. Here it is derived from that of Π₁, which is where VI.3.2(ii) and (iii) enter.

The construction of the morphisms, the cofinality lemma and the assembly are internal. The route parallels the published Π₁ modules `RationalUniversalMembership`, `RationalUniversalProjectivity`, `RationalUniversalGeneration`, `RationalUniversalSmallness` and `RationalUniversalSmallProgeneratorReduction` of the Π₁ proof task `0ba788d6-b9d9-4a76-a017-972f8cad288f`, and uses their published lemmas by name.
