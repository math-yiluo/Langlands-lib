# Proof of the canonical rigidified comparison with the fppf Picard sheaf

Module `Langlands.AlgebraicGeometry.Picard.RigidifiedFppfComparisonProof`.

`Langlands.AlgebraicGeometry.Picard.rigidifiedFppfComparison :
RigidifiedFppfComparisonStatement.{u}` proves the Library statement
`Langlands.AlgebraicGeometry.Picard.RigidifiedFppfComparisonStatement`. Let
`f : X ⟶ S` be quasi-compact and quasi-separated with a section `ε`
(`section_eq : ε ≫ f = 𝟙 S`), and suppose the relative projections induce
isomorphisms on all section rings (`hO`). Then the canonical map
`RigidifiedLineBundle.toPicardSheaf f ε section_eq`, from rigidified classes to
the underlying presheaf of the fppf Picard sheaf, is an isomorphism.

## Proof

The proof only assembles results from other modules. The quasi-compactness and
quasi-separatedness hypotheses on `f` are not used.

1. Uniqueness of rigidified isomorphisms:
   `RigidifiedLineBundle.relative_iso_subsingleton f ε section_eq hO` gives
   `Subsingleton (L ≅ M)` for relative rigidified line bundles over every
   `T : Over S` (module `Picard/RigidifiedRelativeIsoUniqueness`).
2. Zariski sheaf property: with this uniqueness,
   `RigidifiedLineBundle.classPresheaf_isSheaf_zariski_of_unique` shows that the
   rigidified class presheaf is a sheaf for `Scheme.zariskiTopology.over S`
   (module `Picard/RigidifiedClassesZariskiSheafGeneral`).
3. Faithfully flat affine sheaf condition:
   `RigidifiedLineBundle.classPresheaf_isSheafFor_affine` (module
   `Picard/RigidifiedClassesAffineSheaf`) gives the sheaf condition for the
   single arrow `Over.homMk (Spec.map φ)` with `Spec.map φ` flat and
   surjective. It takes as inputs isomorphism descent
   `Langlands.Scheme.Modules.LineBundleIsoDescent.lineBundleIsoDescent`
   (module `Modules/LineBundleIsoDescentProof`) and effective descent
   `Langlands.Scheme.Modules.lineBundleDescentEffective` (module
   `Modules/LineBundleDescentEffectiveProof`) of line bundles, together with
   the uniqueness from step 1.
4. fppf sheaf property: the criterion
   `OverFppfSheaf.isSheaf_fppfTopology_over` (module `Sites/OverFppfSheaf`)
   combines steps 2 and 3 into the sheaf property for
   `Scheme.fppfTopology.over S`.
5. Comparison: `RigidifiedLineBundle.toPicardSheaf_isIso_of_isSheaf` (module
   `Picard/RigidifiedComparisonOfSheaf`) shows that the canonical map is an
   isomorphism once the rigidified class presheaf is an fppf sheaf. It uses
   that forgetting the rigidification is injective and locally surjective,
   and that the comparison with the sheafification is locally bijective.
