# Effective quotients by flat proper equivalence relations from the Hilbert scheme (proof)

This module proves the published statement
`Langlands.AlgebraicGeometry.FlatProperEquivalenceRelationQuotientReductionStatement`. It
contains no `sorry` and no new axioms. The axioms used are `propext`, `Classical.choice` and
`Quot.sound`.

## Theorem

`Langlands.AlgebraicGeometry.FlatEquivalenceRelation.flatProperEquivalenceRelationQuotient_of_hilbertScheme :
FlatProperEquivalenceRelationQuotientReductionStatement.{u}`.

So `HilbertSchemeUniversalFamilyStatement.{u}` implies
`FlatProperEquivalenceRelationQuotientStatement.{u}`. A proof of the Hilbert scheme statement
therefore proves `FlatProperEquivalenceRelationQuotientStatement`: with
`hilbertSchemeUniversalFamily` (module `HilbertSchemeUniversalFamilyProof`) this is done in
`FlatProperEquivalenceRelationQuotientProof`.

The module also proves two small lemmas:

- `locallyOfFinitePresentation_of_locallyOfFiniteType`: a morphism locally of finite type into a
  locally noetherian scheme is locally of finite presentation. Check this on affine opens, where
  the rings of the target are noetherian (Mathlib's `RingHom.FinitePresentation.of_finiteType`).
- `compactSpace_of_surjective`: the target of a surjective morphism from a quasi-compact scheme
  is quasi-compact.

## Proof

The proof follows Nitsure, *Construction of Hilbert and Quot schemes*
(`nitsure-2005-hilbert-quot-arxiv-math0504590v1`), Theorem 6.8 (proof pp.33–35), with the
changes described in `FlatProperEquivalenceRelationQuotientReductionStatement.md`. Let `A`, `p`,
`s`, `t` be as in the statement, with `p` H-quasi-projective through a quasi-compact immersion
`i : Z ⟶ ℙⁿ_A`.

1. **The Hilbert scheme of `ℙⁿ_A`.** The identity of `ℙⁿ_A` is a closed immersion, so
   `Picard.exists_closedImmersionBySections_iff_isHProjective` gives an invertible module on
   `ℙⁿ_A` whose sections give a closed immersion into projective space. `ℙⁿ_A ⟶ Spec A` is flat
   and locally of finite presentation (`ProjectiveSpace.FlatStructure`). So the hypothesis
   `HilbertSchemeUniversalFamilyStatement` gives `H`, `πH`, `W`, separatedness of `πH`, the
   classification clauses, and the cover of `H` by pairwise disjoint H-projective opens `U θ`.
   The classification clauses form a `Classifier` (module `FlatEquivalenceRelation.Classifier`).
2. **The family.** `Z` is locally noetherian, since it is locally of finite type over the
   noetherian `A`. The morphism `s` is proper, hence locally of finite type, hence locally of
   finite presentation. The family `R ⟶ ℙⁿ_A ×_A Z` is a closed immersion
   (`isClosedImmersion_family`). Its closed subscheme is flat and locally of finite presentation
   over `Z`, like `s`. The uniqueness clause with `T = Z` gives the classifying morphism
   `φ : Z ⟶ H` over `Spec A`.
3. **The quotient.** Take `Q`, `π` and `ιQ` from `FlatEquivalenceRelation.Quotient`, and
   `q := (ιQ ≫ H''.ι) ≫ πH`. Then `π ≫ q = p` by `π_ι_ι` and `φ ≫ πH = p`. That module gives
   that `π` is flat, surjective, proper and locally of finite presentation, and that
   `IsPullback s t π π` holds.
4. **Quasi-projectivity.** `Z` is quasi-compact, and `π` is surjective, so `Q` is
   quasi-compact. The morphism `ιQ ≫ H''.ι : Q ⟶ H` is an immersion (a closed immersion
   followed by an open immersion). So `q` is H-quasi-projective by
   `isHQuasiProjective_of_isImmersion_of_disjoint_cover` (module
   `HQuasiProjectiveDisjointUnion`), applied to the cover `U θ` of `H`.

## Helper modules

All are written for this proof:

- `Langlands.AlgebraicGeometry.ProjectiveSpace.FlatStructure`: `ℙⁿ_R ⟶ Spec R` is flat and
  locally of finite presentation.
- `Langlands.AlgebraicGeometry.ProjectiveSpace.CoordinateEmbedding`: closed immersions
  `ℙᵃ_R ⟶ ℙᴺ_R` along injective maps of coordinate indices.
- `Langlands.AlgebraicGeometry.HQuasiProjectiveDisjointUnion`: disjoint unions of
  H-quasi-projective schemes, and immersions into disjoint unions of H-projective schemes.
- `Langlands.AlgebraicGeometry.KernelFlatBaseChange`: flat base change of the kernel of a
  quasi-compact morphism (Stacks Project, Tag 081I).
- `Langlands.AlgebraicGeometry.FlatEquivalenceRelation.Classifier`: the classifying morphism
  and Nitsure's property (***).
- `Langlands.AlgebraicGeometry.FlatEquivalenceRelation.OpenLocus`: the open locus of `H` over
  which the graph of `φ` is closed.
- `Langlands.AlgebraicGeometry.FlatEquivalenceRelation.Quotient`: the quotient `Q` and the
  properties of `π`.

## Dependencies outside Mathlib

Library: `HilbertSchemeUniversalFamilyStatement` and
`FlatProperEquivalenceRelationQuotientStatement` (through the reduction statement),
`IsHQuasiProjective`, `IsHProjective`, `ProjectiveSpace` with its coordinate opens, charts and
properness (`ProjectiveSpace.Structure`, `ProjectiveSpace.Charts`,
`ProjectiveSpace.CoordinateCoverProof`), and
`Picard.exists_closedImmersionBySections_iff_isHProjective`. The FLT port supplies the
projective-space charts (`ProjSpace.ratio`, `ProjSpace.awayι_comp_π`) and ideal-sheaf lemmas
(`ComapLocal.ideal_comap_top`, `isPushout_appTop_of_isPullback`).
