# Proof of the reduction of the closed agreement locus to an affine base

`Langlands.AbelianScheme.rigidifiedClassesEqualizerClosedReduction` proves
`Langlands.AbelianScheme.RigidifiedClassesEqualizerClosedReductionStatement.{u}`: the
affine-base statement `RigidifiedClassesEqualizerClosedAffineStatement.{u}` and Zariski
separatedness `RigidifiedClassesZariskiSeparatedStatement.{u}` imply
`RigidifiedClassesEqualizerClosedStatement.{u}`. See
`RigidifiedClassesEqualizerClosedReductionStatement.md` for the three propositions. The proof
is a conditional implication. It does not prove either hypothesis.

The proof uses the published gluing theorem
`Langlands.AlgebraicGeometry.closedLocusFromAffineCharts` (closed loci given on all affine
opens glue) and the published ground-base change of rigidified families
(`familyBaseChange`, `familyBaseChangeEquivalence`, `familyBaseChangeNaturality`). The
local helpers live in the namespace
`Langlands.AbelianScheme.RigidifiedClassesEqualizerClosedReduction`. Inside that namespace,
`cp[A]` abbreviates `RigidifiedLineBundle.classesPullback A.X.hom (unitSection A)
(unitSection_comp A)`, the actual pullback of rigidified classes for the abelian scheme `A`.

## Helper lemmas

1. **Composition (`Langlands.AbelianScheme.classesPullback_comp`, imported from
   `MumfordParameterAxes`).** `cp[A] h (cp[A] k q) = cp[A] (h ≫ k) q`. The
   witness is the published natural isomorphism `RigidifiedLineBundle.relativePullbackComp`,
   built from the proved coherence `RigidifiedModule.pullbackCoherence`, applied to a
   representative of `q`.
2. **Precomposition (`agree_of_fac`).** If `a ≫ k = h` and the pullbacks of `q` and `r` along
   `k` agree, then they agree along `h`. This follows from step 1.
3. **Classes under ground-base change.** Let `b : S' ⟶ S`. The map
   `classesBaseChange b A T` sends a class on `(Over.map b).obj T` for `A` to a class on `T`
   for `(baseChange b).obj A`. It is `Quotient.map` of the functor `familyBaseChange b A T`.
   - `classesBaseChange_pullback`: it commutes with pullback along `h : T ⟶ U` in
     `Over S'`. The witness is `familyBaseChangeNaturality b A h`.
   - `classesBaseChange_injective`: it is injective. An isomorphism between the images of
     two families lifts to an isomorphism of the families, because `familyBaseChange b A T`
     is the functor of the equivalence `familyBaseChangeEquivalence b A T` and so is fully
     faithful (`preimageIso`).

## The predicate to glue

Fix `S`, `A`, `T` and `q r : RigidifiedClasses A T`. For a scheme morphism `g : Y ⟶ T.left`,
let `Agree q r g` say that the pullbacks of `q` and `r` along
`Over.homMk g : Over.mk (g ≫ T.hom) ⟶ T` are equal.

- **`agree_iff`.** For every `h : T' ⟶ T` in `Over S`, the pullbacks along `h` agree if and
  only if `Agree q r h.left`. The objects `T'` and `Over.mk (h.left ≫ T.hom)` have the same
  underlying scheme, and the identity of `T'.left` gives morphisms between them in both
  directions. Each direction is step 2.
- **Stability (`agree_comp`).** `Agree q r g` implies `Agree q r (f ≫ g)`, by step 2 with the
  morphism `Over.homMk f`.
- **Locality (`agree_of_affineOpens`).** Suppose `Agree q r ((g ⁻¹ᵁ V).ι ≫ g)` for every
  affine open `V` of `T.left`. The preimages `g ⁻¹ᵁ V` cover `Y`, because the affine opens
  cover `T.left` (`iSup_affineOpens_eq_top`, `Hom.iSup_preimage_eq_top`). Build the open cover
  `𝒰 = Y.openCoverOfIsOpenCover …` from them. Apply the Zariski separatedness hypothesis to
  the object `Over.mk (g ≫ T.hom)`, the cover `𝒰` and the two pulled-back classes. After
  rewriting with step 1, the hypothesis on each cover member is the assumption, by
  `agree_iff`. The conclusion is `Agree q r g`.
- **Affine charts (`chart`).** Let `U` be an affine open of `T.left` with
  `hU : IsAffineOpen U`. Put `b = hU.fromSpec ≫ T.hom : Spec Γ(T.left, U) ⟶ S` and let
  `φ : (Over.map b).obj (Over.mk (𝟙 _)) ⟶ T` be `Over.homMk hU.fromSpec`. Apply the
  affine-base hypothesis to the ring `Γ(T.left, U)`, the abelian scheme
  `(baseChange b).obj A`, and the classes `classesBaseChange b A _ (cp[A] φ q)` and
  `classesBaseChange b A _ (cp[A] φ r)`. It gives a closed immersion
  `ι : Z ⟶ Spec Γ(T.left, U)`. The chart on `U` is `ι ≫ hU.isoSpec.inv`, again a closed
  immersion. For `g : Y ⟶ U`, test the affine-base property with the object
  `Over.mk (g ≫ hU.isoSpec.hom)` and its structure morphism. Rewriting with
  `classesBaseChange_pullback`, injectivity of `classesBaseChange`, step 1 and `agree_iff`
  turns the right-hand side into `Agree q r` of the composite underlying morphism. That
  composite equals `g ≫ U.ι` by `IsAffineOpen.isoSpec_hom_fromSpec`. Factoring through `ι`
  and through `ι ≫ hU.isoSpec.inv` correspond by composing with `hU.isoSpec`.

## Main theorem

Given the two hypotheses and `S`, `A`, `T`, `q`, `r`, apply `closedLocusFromAffineCharts` to
the scheme `T.left` and the predicate `Agree q r`. Its three hypotheses are `agree_comp`,
`agree_of_affineOpens` and `chart`. It returns a closed immersion `ι : Z ⟶ T.left` such that
`g` factors through `ι` exactly when `Agree q r g`. For `h : T' ⟶ T`, apply this to
`g = h.left` and use `agree_iff`.

## Provenance

Internal. This is the formal reduction step of proof task
`e3d4a3ab-f378-42af-87c5-0cd4caec7b2e`, written for this project. The gluing step it uses is
the published `closedLocusFromAffineCharts`, which is adapted from the Anthropic FLT Lean
source (see `ClosedLocusFromAffineChartsProof.md`). The rest of this file (the predicate
`Agree`, its locality via Zariski separatedness, and the affine charts via ground-base change
of rigidified families) is written for this project's definitions and is not taken from FLT.
