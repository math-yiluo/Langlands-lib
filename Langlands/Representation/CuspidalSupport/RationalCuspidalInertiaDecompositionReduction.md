# Reducing Renard VI.3.3.1 to compact restriction and VI.2.1

This module reduces the proper-standard-cuspidal form of VI.3.3.1, `Langlands.CuspidalSupport.RationalCuspidalInertiaDecompositionStatement.{uF,uV}`, to three published propositions. None of the three is proved here, so the module does not prove VI.3.3.1. Its single definition is the structural antecedent of VI.2.1 at one special vertex. The source is David Renard, *Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026, `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The relevant passages are VI.3.3, printed pp.144–145 / PDF pp.150–151, the theorem of VI.2.1, printed pp.137–139 / PDF pp.143–145, and V.5.1–V.5.2, printed pp.122–123 / PDF pp.128–129. The registered errata cover the 2010 edition only.

## The special-vertex inputs

`RationalSpecialVertexCompactInputsStatement.{uF}` takes an arbitrary nonarchimedean local field `F : Type uF`, an actual connected reductive group scheme `G`, an actual maximal split torus `i : S.toGrp ⟶ G` and a generic cocharacter `ν`. It asserts that there exist `D : KPApartmentData i (localFieldOrder F)` and `x : D.Apartment` with these four properties, all at the same `K0 = D.specialCompactSubgroup x`:

- `D.IsSpecialApartmentVertex x`;
- `SpecialCompactProperties F i ν K0`;
- `SimultaneousStandardBasisAt i ν K0`;
- `FiniteCartanCovering F i ν K0`.

These are exactly the extra hypotheses of the published `Langlands.Aubert.General.RationalPointFamily.RationalCuspidalCompactRestrictionStatement`. The binders and instance derivations are those of that statement and of `Langlands.BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement`: affineness of `G.X.hom` comes from `hG.isAffineHom` and the monomorphism instance comes from `hi.isSplitSubtorus.mono`. In the source these properties are V.5.1(2),(3), V.5.2(i)–(iv) and the covering clause of V.5.1(4) for a special maximal compact subgroup. The definition is derived and internal: it packages the hypotheses of the VI.2.1 statement as one existence proposition. It asserts nothing about weak `KPApartmentData` beyond the existence of one such witness.

## The proofs

`rationalSpecialVertexCompactInputs_of_jointBasis` derives the special-vertex inputs from `JointSpecialCompactBasisExistenceStatement.{uF}`. It destructures the joint witness `D, x, Z, j, s, h` and keeps the special-vertex, special-compact-property and simultaneous-basis conjuncts. It then applies the proved `Langlands.Aubert.General.RationalPointFamily.rationalPositiveCartanCover` (module `Langlands.Representation.Aubert.General.RationalPositiveCartanCoverProof`) to three conjuncts of the same witness: the centralizer representation `(torusCentralizer i).IsRepresentedBy j`, the factorization `s ≫ j = i` and `SpecialCompactRenardComparison D x ν j s h`. This gives `FiniteCartanCovering F i ν (D.specialCompactSubgroup x)` for the same compact subgroup. The Iwasawa, Levi-inheritance and Levi-compatibility conjuncts are not used.

`rationalCuspidalInertiaDecomposition_of_specialVertexInputs` proves `RationalCuspidalInertiaDecompositionStatement.{uF,uV}` from three hypotheses:

- `RationalCompactRestrictionInertiaDecompositionStatement.{uF,uV}`;
- `RationalCuspidalCompactRestrictionStatement.{uF,uV}`;
- `RationalSpecialVertexCompactInputsStatement.{uF}`.

Fix the target's data `F, G, hG, T, i, hi`, its three topology instances, `ν, hν`, `hStandard`, `hRoots`, `hU`, an irreducible `π` and proper-standard cuspidality `hcusp`. The special-vertex inputs at `(F, G, hG, T, i, hi, ν, hν)` give `D`, `x` and the four properties. The VI.2.1 statement is applied to the same `F, G, hG, T, i, hi`, the same topology instances, `ν, hν, hStandard, hRoots, hU`, this witness and `π, hcusp`. It gives `HasCompactSmoothDualCoefficients` for the restriction of `π` to `Plancherel.rationalCommonNormKernel G`. The compact-restriction statement, applied to `F, G, hG`, the same instances, `π`, its irreducibility and this compactness, gives `IsRationalInertiaCategoryDecomposition G π`.

`rationalCuspidalInertiaDecomposition_of_jointBasis` composes the two theorems. Its hypotheses are the compact-restriction decomposition, VI.2.1 (a) ⇒ (c) and the joint special-compact basis existence target.

## Actual-data and universe comparisons

Lean checks all of these comparisons by definitional unfolding; no transport lemma is needed.

- The VI.2.1 statement writes the point group as `RationalPoint F G.X`, while the target writes `GroupScheme.rationalPoints G`. Both are abbreviations of the same morphism type `Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X`. Both carry `rationalPointTopology F G.X`, and the target's locally compact, nonarchimedean and Hausdorff instances are accepted by the VI.2.1 statement unchanged.
- The cuspidality hypothesis uses the same `simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν` and the same semidirect family `isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν` in both statements.
- The norm kernel `Plancherel.rationalCommonNormKernel G` and the restricted representation are identical in the VI.2.1 conclusion and the compact-restriction premise.
- The smoothness instance `hG.smooth` appears in the target and the compact-restriction statement but not in the VI.2.1 statement. It does not occur in any of the types that are passed between them.
- The field universe `uF` and carrier universe `uV` stay independent. The special-vertex inputs, the joint target and `StandardCocharacterStatement` live at `uF` alone.

## Scope

All three hypotheses of the final reduction are separately owned and unproved. They are the compact-restriction proof task `4aec2dfc-fa49-4d51-9f5e-cb9d1976f360`, the VI.2.1 proof task `a13ad087-8856-4027-82f7-1632b154f3bf` and the joint-existence proof task `8c39faa0-2a70-4fc4-a027-914987aba924`. Once they are published, the proof of the target is a direct application of `rationalCuspidalInertiaDecomposition_of_jointBasis`.

The reduction runs entirely on the actual standard family of the target. It does not implement the source's comparison of this cocharacter and simple-relative-root indexing with the source's standard parabolics. It also does not implement the reduction from all proper parabolics to proper standard ones (first remark of VI.2.1) or the normalization correspondence. These remain parent obligations of the program. The same holds for the remarks after VI.3.3.1: the finite stabilizer, the algebraic-torus structure, the coordinate ring and the bijection with orbits of compact types.
