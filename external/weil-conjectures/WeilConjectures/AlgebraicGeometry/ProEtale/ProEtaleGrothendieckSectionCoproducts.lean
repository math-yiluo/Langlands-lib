/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleQcqsSiteLimits
import WeilConjectures.AlgebraicGeometry.ProEtaleQcqsSubsite
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Sites.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Comma.Over.Basic
import WeilConjectures.CategoryTheory.Finite.FiniteHypercoverColimits
import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
import Mathlib.CategoryTheory.Sites.Hypercover.IsSheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import WeilConjectures.CategoryTheory.Sites.Categorical.CategoricalFiniteCechCriterion
import WeilConjectures.CategoryTheory.Sites.Categorical.CategoricalInjectiveCechExactness
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-! # Coproducts of Grothendieck-valued pro-etale sheaf sections on qcqs objects

## References

* Stacks Project, Tag 0738 and the qcqs subsite in the proof of Tag 09A1
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

private theorem finite_affine_cover_refinement (X : Scheme.{u}) (W : X.ProEt)
    [CompactSpace W.left] [QuasiSeparatedSpace W.left] (S : Sieve W) (hS : S ∈ topology X W) :
    ∃ (I : Type (u + 1)) (_ : Finite I) (V : I → X.ProEt) (f : ∀ i, V i ⟶ W),
      Sieve.ofArrows V f ∈ topology X W ∧ (∀ i, S (f i)) ∧ (∀ i, IsAffine (V i).left) := by
  classical
  have : (precoverage X).IsStableUnderComposition := by
    dsimp [precoverage]
    infer_instance
  have : (precoverage X).HasIsos := by dsimp [precoverage]; infer_instance
  have : (precoverage X).IsStableUnderBaseChange := by
    dsimp [precoverage]
    infer_instance
  obtain ⟨T, hT, hTS⟩ :=
    (precoverage X).mem_toGrothendieck_iff_of_isStableUnderComposition.mp hS
  let E := T.preZeroHypercover
  let F := ProEt.forget X ⋙ Over.forget X
  let E' := E.map F
  have hE' : E'.presieve₀ ∈ Scheme.proetalePrecoverage W.left := by
    have he : E'.presieve₀ = Presieve.map F T := by
      dsimp only [E']
      rw [PreZeroHypercover.presieve₀_map]
      exact congrArg (Presieve.map F) T.presieve₀_preZeroHypercover
    rw [he]
    exact hT
  let U : W.left.Cover (Scheme.precoverage @WeaklyEtale) := ⟨E', hE'.2⟩
  let : QuasiCompactCover U.toPreZeroHypercover :=
    Scheme.presieve₀_mem_qcPrecoverage_iff.mp hE'.1
  obtain ⟨A, r, hfin, _⟩ := QuasiCompactCover.exists_hom U
  let := hfin
  have : Finite A.cover.I₀ := hfin
  have (i : A.cover.I₀) : QuasiCompact (A.cover.f i) := by
    apply quasiCompact_of_compactSpace
  have : QuasiCompactCover A.cover.toPreZeroHypercover := QuasiCompactCover.of_finite
  have (i : A.I₀) : WeaklyEtale (A.f i) := A.cover.map_prop i
  let V : A.I₀ → X.ProEt := fun i ↦ ProEt.mk (A.f i ≫ W.hom)
  let f : ∀ i, V i ⟶ W := fun i ↦ MorphismProperty.Over.homMk (A.f i) (by rfl)
  refine ⟨A.I₀, hfin, V, f, ?_, ?_, ?_⟩
  · apply Precoverage.generate_mem_toGrothendieck
    change Presieve.map F (Presieve.ofArrows V f) ∈ Scheme.proetalePrecoverage W.left
    rw [Presieve.map_ofArrows]
    change A.cover.presieve₀ ∈ Scheme.proetalePrecoverage W.left
    exact ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.mpr inferInstance, A.cover.mem₀⟩
  · intro i
    let e := r.s₀ i
    let g : V i ⟶ E.X e := MorphismProperty.Over.homMk (r.h₀ i) (by
      change r.h₀ i ≫ (E.X e).hom = A.f i ≫ W.hom
      have he : r.h₀ i ≫ (E.f e).left = A.f i := r.w₀ i
      rw [← he, Category.assoc]
      congr 1
      simp)
    have hg : g ≫ E.f e = f i := by
      apply (ProEt.forget X).map_injective
      apply Over.OverMorphism.ext
      exact r.w₀ i
    rw [← hg]
    exact S.downward_closed (hTS _ _ e.2) g
  · intro i
    change IsAffine (Spec (A.X i))
    infer_instance

private instance qcqs_full (X : Scheme.{u}) : (qcqsInclusion X).Full :=
  inferInstanceAs (qcqsObjects X).ι.Full

private instance qcqs_faithful (X : Scheme.{u}) : (qcqsInclusion X).Faithful :=
  inferInstanceAs (qcqsObjects X).ι.Faithful

private def qcqsTopology (X : Scheme.{u}) : GrothendieckTopology (Qcqs X) :=
  (qcqsInclusion X).restrictedTopology (topology X)

private instance qcqs_coverDense (X : Scheme.{u}) :
    (qcqsInclusion X).IsCoverDense (topology X) where
  is_cover V := by
    let C := V.left.affineOpenCover
    let U (i : C.I₀) : X.ProEt := ProEt.mk (C.f i ≫ V.hom)
    have (i : C.I₀) : IsAffine (U i).left := by
      change IsAffine (Spec (C.X i))
      infer_instance
    let f (i : C.I₀) : U i ⟶ V := MorphismProperty.Over.homMk (C.f i)
    have hcover : Sieve.ofArrows U f ∈ topology X V := by
      apply Precoverage.generate_mem_toGrothendieck
      change (Presieve.ofArrows U f).map (ProEt.forget X ⋙ Over.forget X) ∈
        proetalePrecoverage V.left
      rw [Presieve.map_ofArrows]
      exact (zariskiPrecoverage_le_propQCPrecoverage (P := @WeaklyEtale)) _
        C.openCover.mem₀
    apply (topology X).superset_covering _ hcover
    rw [Sieve.ofArrows, Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro i
    let T : Qcqs X := ⟨U i, inferInstance, inferInstance⟩
    exact Presieve.in_coverByImage (qcqsInclusion X) (Y := T) (f i)

private instance qcqs_finiteHypercovers (X : Scheme.{u}) :
    (qcqsTopology X).finiteOneHypercover.{u, u + 1, u + 1}.IsGenerating where
  le {T} S hS := by
    obtain ⟨hp, P, hP, hlim, hscheme, hmap, hslice, hfinite, hadjoin⟩ := qcqs_site_limits X
    let : HasPullbacks (Qcqs X) := hp
    have hS' : S.functorPushforward (qcqsInclusion X) ∈ topology X T.obj :=
      Functor.mem_restrictedTopology_iff.mp hS
    let : CompactSpace T.obj.left := T.property.1
    let : QuasiSeparatedSpace T.obj.left := T.property.2
    obtain ⟨I, hI, V, f, hcov, hf, haff⟩ :=
      finite_affine_cover_refinement X T.obj _ hS'
    let : Finite I := hI
    let W (i : I) : Qcqs X :=
      have : IsAffine (V i).left := haff i
      ⟨V i, inferInstance, inferInstance⟩
    let g (i : I) : W i ⟶ T := (qcqsInclusion X).preimage (f i)
    have hg (i : I) : S (g i) := by
      apply (Sieve.mem_functorPushforward_iff_of_full_of_faithful
        (qcqsInclusion X) S (g i)).1
      simpa [g] using hf i
    have hcover : Sieve.ofArrows W g ∈ qcqsTopology X T := by
      apply Functor.mem_restrictedTopology_iff.mpr
      rw [Sieve.functorPushforward_ofArrows]
      simp only [g, Functor.map_preimage]
      simpa only [W, qcqsInclusion, ObjectProperty.ι_obj] using hcov
    let E₀ : PreZeroHypercover T := { I₀ := I, X := W, f := g }
    let : E₀.Finite := ⟨hI⟩
    let E : (qcqsTopology X).OneHypercover T :=
      .mk' E₀.toPreOneHypercover hcover (by simp)
    refine ⟨E, ?_, ?_⟩
    · change E₀.toPreOneHypercover.Finite
      infer_instance
    · rw [PreZeroHypercover.sieve₀, Sieve.ofArrows, Sieve.generate_le_iff,
        Presieve.ofArrows_le_iff]
      exact hg

/-- Sections on a qcqs pro-etale object commute with coproducts with coefficients in
any Grothendieck abelian category. -/
private theorem qcqs_evaluation_preservesCoproducts
    (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A]
    (X : Scheme.{u}) (V : X.ProEt)
    [CompactSpace V.left] [QuasiSeparatedSpace V.left] (I : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete I)
      (sheafToPresheaf (topology X) A ⋙ (CategoryTheory.evaluation X.ProEtᵒᵖ A).obj (op V)) := by
  let : HasColimitsOfSize.{u + 1, u + 1} A := IsGrothendieckAbelian.hasColimits A
  let : HasLimitsOfSize.{u + 1, u + 1} A := IsGrothendieckAbelian.hasLimits A
  let : HasLimitsOfSize.{u, u + 1} A :=
    hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} A
  let J := qcqsTopology X
  let G := qcqsInclusion X
  let : G.IsDenseSubsite J (topology X) := by
    dsimp [G, J, qcqsTopology]
    infer_instance
  let R := G.sheafPushforwardContinuous A J (topology X)
  let : ∀ W, HasLimitsOfShape (StructuredArrow W G.op) A := fun _ ↦ inferInstance
  let : R.IsEquivalence := by
    change (G.sheafPushforwardContinuous A J (topology X)).IsEquivalence
    infer_instance
  let : PreservesColimitsOfShape (Discrete I) (sheafToPresheaf J A) :=
    sheafToPresheaf_preservesColimits_of_finiteHypercovers J
  let W : Qcqs X := ⟨V, inferInstance, inferInstance⟩
  change PreservesColimitsOfShape (Discrete I)
    ((R ⋙ sheafToPresheaf J A) ⋙ (CategoryTheory.evaluation (Qcqs X)ᵒᵖ A).obj (op W))
  infer_instance

variable {X : Scheme.{u}}

private lemma compactSpace_and_quasiSeparatedSpace_of_iso {A B : X.ProEt} (e : A ≅ B)
    (h : CompactSpace A.left ∧ QuasiSeparatedSpace A.left) :
    CompactSpace B.left ∧ QuasiSeparatedSpace B.left := by
  let φ := TopCat.homeoOfIso
    (Scheme.forgetToTop.mapIso ((ProEt.forget X ⋙ Over.forget X).mapIso e))
  exact ⟨@Homeomorph.compactSpace _ _ _ _ h.1 φ, (quasiSeparatedSpace_congr φ).1 h.2⟩

/-- A fibre product of weakly étale `X`-schemes with quasi-compact quasi-separated
underlying schemes over one with quasi-separated underlying scheme has quasi-compact
quasi-separated underlying scheme. -/
private lemma compactSpace_and_quasiSeparatedSpace_pullback {V A B : X.ProEt}
    (f : A ⟶ V) (g : B ⟶ V)
    [QuasiSeparatedSpace V.left] [CompactSpace A.left] [QuasiSeparatedSpace A.left]
    [CompactSpace B.left] [QuasiSeparatedSpace B.left] :
    CompactSpace (pullback f g).left ∧ QuasiSeparatedSpace (pullback f g).left := by
  let iso := PreservesPullback.iso (ProEt.forget X ⋙ Over.forget X) f g
  have : QuasiCompact f.left := quasiCompact_of_compactSpace _
  have : CompactSpace ↥(Limits.pullback (C := Scheme.{u}) f.left g.left) := inferInstance
  have : QuasiSeparatedSpace ↥(Limits.pullback (C := Scheme.{u}) f.left g.left) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd f.left g.left)
  let φ := TopCat.homeoOfIso (Scheme.forgetToTop.mapIso iso).symm
  exact ⟨@Homeomorph.compactSpace _ _ _ _ ‹_› φ, (quasiSeparatedSpace_congr φ).1 ‹_›⟩

/-- A finite product in `Over V` of weakly étale `X`-schemes with quasi-compact quasi-separated
underlying schemes has quasi-compact quasi-separated underlying scheme, if `V` has. -/
private lemma compactSpace_and_quasiSeparatedSpace_piObj {V : X.ProEt} [CompactSpace V.left]
    [QuasiSeparatedSpace V.left] {J : Type*} [Finite J] (U : J → Over V)
    (hU : ∀ j, CompactSpace (U j).left.left ∧ QuasiSeparatedSpace (U j).left.left) :
    CompactSpace (∏ᶜ U).left.left ∧ QuasiSeparatedSpace (∏ᶜ U).left.left := by
  let P : ObjectProperty (Over V) := fun A ↦
    CompactSpace A.left.left ∧ QuasiSeparatedSpace A.left.left
  have hiso {A B : Over V} (e : A ≅ B) (h : P A) : P B :=
    compactSpace_and_quasiSeparatedSpace_of_iso ((Over.forget V).mapIso e) h
  have : P.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty) := ⟨by
    rintro A ⟨h⟩
    have hA : IsTerminal A := (isLimitEquivIsTerminalOfIsEmpty _ _) h.isLimit
    exact hiso (Over.mkIdTerminal.uniqueUpToIso hA) ⟨‹_›, ‹_›⟩⟩
  have : P.IsClosedUnderBinaryProducts := ⟨by
    rintro A ⟨h⟩
    let e : A ≅ h.diag.obj ⟨.left⟩ ⨯ h.diag.obj ⟨.right⟩ :=
      h.isLimit.conePointUniqueUpToIso (limit.isLimit _) ≪≫ HasLimit.isoOfNatIso (diagramIsoPair _)
    refine hiso e.symm ?_
    obtain ⟨_, _⟩ := h.prop_diag_obj ⟨.left⟩
    obtain ⟨_, _⟩ := h.prop_diag_obj ⟨.right⟩
    exact compactSpace_and_quasiSeparatedSpace_of_iso (Over.prodLeftIsoPullback _ _).symm
      (compactSpace_and_quasiSeparatedSpace_pullback _ _)⟩
  have : P.IsClosedUnderFiniteProducts := .mk'
  exact P.prop_product hU

end AlgebraicGeometry.Scheme.ProEt
