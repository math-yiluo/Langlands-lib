import Langlands.GroupScheme.Reductive.Basic
import Langlands.AlgebraicGeometry.ProjectiveBundle.BaseChangeSectionBasis
import Langlands.AlgebraicGeometry.Modules.SectionVanishingTransportProof
import Langlands.AlgebraicGeometry.FiniteSeparating.Core
import Langlands.AlgebraicGeometry.LinearSystem.CoefficientComparison
import Langlands.AbelianScheme.AlgClosedFieldAmpleCubeSeparationStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicFieldEmbeddingStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.CanonicalCubicBundleAmpleProof
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicDirectImageProof
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicFibreSections
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # The cubic Lefschetz embedding over a field from the algebraically closed case -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard
open Langlands.AlgebraicGeometry.LinearSystem Langlands.AlgebraicGeometry.ProjectiveBundle
open Langlands.AlgebraicGeometry.Modules.DerivedSections Langlands.AlgebraicGeometry
open Langlands.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma closureMap_flat_surjective (K : Type u) [Field K] :
    Flat (Langlands.GroupScheme.toAlgebraicClosure K) ∧ Surjective (Langlands.GroupScheme.toAlgebraicClosure K) :=
  (flat_and_surjective_SpecMap_iff _).mpr
    (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)

instance (K : Type u) [Field K] : Flat (Langlands.GroupScheme.toAlgebraicClosure K) := (closureMap_flat_surjective K).1

instance (K : Type u) [Field K] : Surjective (Langlands.GroupScheme.toAlgebraicClosure K) := (closureMap_flat_surjective K).2

variable {P : Prerequisites.{u}} {K : Type u} [Field K] {g d n : ℕ}
  (a : Datum P (Spec (CommRingCat.of K)) g d n)

/-- The algebraically closed separation statement, applied to the base change of the datum to
an algebraic closure and transported to the pullback of the cubic bundle. -/
lemma Datum.separates_closure (H : AlgClosedFieldAmpleCubeSeparationStatement.{u}) :
    SeparatesPointsAndTangents (a.pullback (Langlands.GroupScheme.toAlgebraicClosure K)).abelian.X.hom
      ((LineBundle.pullback (Limits.pullback.fst a.abelian.X.hom (Langlands.GroupScheme.toAlgebraicClosure K))).obj
        a.cubicBundle) := by
  have h : SeparatesPointsAndTangents (a.pullback (Langlands.GroupScheme.toAlgebraicClosure K)).abelian.X.hom
      (a.pullback (Langlands.GroupScheme.toAlgebraicClosure K)).cubicBundle :=
    H (AlgebraicClosure K) (a.pullback (Langlands.GroupScheme.toAlgebraicClosure K)).abelian
      (a.pullback (Langlands.GroupScheme.toAlgebraicClosure K)).canonicalBundle
      (canonicalCubicBundleAmple P (AlgebraicClosure K) g d n (a.pullback (Langlands.GroupScheme.toAlgebraicClosure K))).1
  exact h.of_iso ((LineBundle.forget _).mapIso (a.cubicBundlePullbackIso (Langlands.GroupScheme.toAlgebraicClosure K)))

/-- Quasi-coherence of the cubic direct image and invertibility of its comparison with the
direct image on the algebraic closure. -/
lemma Datum.closure_comparison (hd : 0 < d) :
    ((Scheme.Modules.pushforward a.abelian.X.hom).obj a.cubicBundle.obj).IsQuasicoherent ∧
      IsIso (baseChangeEvaluation a.abelian.X.hom a.cubicBundle
        (𝟙 ((Scheme.Modules.pushforward a.abelian.X.hom).obj a.cubicBundle.obj))
        (Langlands.GroupScheme.toAlgebraicClosure K) (a.pullback (Langlands.GroupScheme.toAlgebraicClosure K)).abelian.X.hom
        (Limits.pullback.fst a.abelian.X.hom (Langlands.GroupScheme.toAlgebraicClosure K)) Limits.pullback.condition) := by
  obtain ⟨hM, hbc⟩ := cubicDirectImage P (Spec (CommRingCat.of K)) g d n hd a
  have := hM.isLocallyFree
  have : IsIso (a.rigidificationBaseChangeMap (Langlands.GroupScheme.toAlgebraicClosure K)) := hbc _ (Langlands.GroupScheme.toAlgebraicClosure K)
  exact ⟨inferInstanceAs a.rigidificationModule.IsQuasicoherent,
    a.isIso_cubicBaseChangeEvaluation (Langlands.GroupScheme.toAlgebraicClosure K)⟩

/-- Every point lies in the nonvanishing locus of some global section of the cubic bundle. -/
lemma Datum.exists_mem_nonvanishingLocus_of_cubeSeparation (hd : 0 < d)
    (H : AlgClosedFieldAmpleCubeSeparationStatement.{u}) (x : a.abelian.X.left) :
    ∃ σ : GlobalSections a.cubicBundle.obj, x ∈ nonvanishingLocus a.cubicBundle.obj σ := by
  classical
  obtain ⟨hqc, hiso⟩ := a.closure_comparison hd
  have hSep := a.separates_closure H
  let f := Limits.pullback.fst a.abelian.X.hom (Langlands.GroupScheme.toAlgebraicClosure K)
  let b := Module.Basis.ofVectorSpace K
    ((relativeGlobalSections a.abelian.X.hom).obj a.cubicBundle.obj)
  let U : (a.pullback (Langlands.GroupScheme.toAlgebraicClosure K)).abelian.X.left.Opens :=
    ⨆ i, trivializationOpen ((LineBundle.pullback f).obj a.cubicBundle).obj
      (pullbackSection f a.cubicBundle.obj (b i))
  have hU : U = ⊤ := by
    apply FiniteSeparating.eq_top_of_forall_rationalPoint_mem
      (a.pullback (Langlands.GroupScheme.toAlgebraicClosure K)).abelian.X.hom U
    intro y hy
    by_contra hyU
    obtain ⟨σ', hσ'⟩ := hSep.1 y hy
    apply hσ'
    apply vanishesAlong_of_forall_pullbackSection a.abelian.X.hom a.cubicBundle f
      (a.pullback (Langlands.GroupScheme.toAlgebraicClosure K)).abelian.X.hom (Langlands.GroupScheme.toAlgebraicClosure K) Limits.pullback.condition b y
    intro i
    rw [vanishesAlong_iff_not_mem]
    intro hi
    exact hyU (TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩)
  obtain ⟨x', rfl⟩ := f.surjective x
  have hx' : x' ∈ U := hU ▸ trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
  refine ⟨b i, ?_⟩
  rw [lineBundleResidueOpenComparison]
  exact (mem_pullback_trivializationOpen_iff f (b i) x').mp hi

/-- The full cubic evaluation is an epimorphism. -/
theorem Datum.epi_cubicEvaluationAdjoint_of_cubeSeparation (hd : 0 < d)
    (H : AlgClosedFieldAmpleCubeSeparationStatement.{u}) :
    Epi a.cubicEvaluationAdjoint := by
  apply epi_of_forall_mem_nonvanishingLocus (L := a.cubicBundle)
  intro x
  obtain ⟨σ, hσ⟩ := a.exists_mem_nonvanishingLocus_of_cubeSeparation hd H x
  refine ⟨sectionPullback a.abelian.X.hom a.rigidificationModule ⊤ σ, ?_⟩
  rw [a.cubicEvaluationAdjoint_eq_evaluationAdjoint]
  have he := evaluationAdjoint_sectionPullback a.abelian.X.hom a.cubicBundle
    (𝟙 a.rigidificationModule) ⊤ σ
  erw [he]
  exact hσ

/-- The morphism defined by a basis of the global sections of the cubic bundle is a closed
immersion. -/
theorem Datum.isClosedImmersion_relativeLinearSystemMap_of_cubeSeparation (hd : 0 < d)
    (H : AlgClosedFieldAmpleCubeSeparationStatement.{u}) (m : ℕ)
    (b : Module.Basis (Fin (m + 1)) K
      ((relativeGlobalSections a.abelian.X.hom).obj a.cubicBundle.obj))
    (hb : ∀ x : a.abelian.X.left, ∃ i, x ∈ nonvanishingLocus a.cubicBundle.obj (b i)) :
    IsClosedImmersion (relativeLinearSystemMap a.abelian.X.hom hb) := by
  obtain ⟨hqc, hiso⟩ := a.closure_comparison hd
  have hSep := a.separates_closure H
  let f := Limits.pullback.fst a.abelian.X.hom (Langlands.GroupScheme.toAlgebraicClosure K)
  let p' := (a.pullback (Langlands.GroupScheme.toAlgebraicClosure K)).abelian.X.hom
  have hb' := pullbackSections_generate f hb
  have hspan : ∀ σ : GlobalSections ((LineBundle.pullback f).obj a.cubicBundle).obj,
      ∃ c : Fin (m + 1) → AlgebraicClosure K,
        σ = linComb p' (fun i ↦ pullbackSection f a.cubicBundle.obj (b i)) c :=
    fun σ ↦ exists_eq_linComb_pullbackSection a.abelian.X.hom a.cubicBundle f p'
      (Langlands.GroupScheme.toAlgebraicClosure K) Limits.pullback.condition b σ
  -- the closed immersion over the algebraic closure
  have hci : IsClosedImmersion (linearSystemMap p' hb') :=
    isClosedImmersion_linearSystemMap_of_separates p' hb' hSep hspan
  have hiso' : IsIso (RelativeProjectiveSpace.toPolynomial m
      (𝟙 (Spec (CommRingCat.of (AlgebraicClosure K))))) := by
    unfold RelativeProjectiveSpace.toPolynomial
    rw [RelativeProjectiveSpace.map_id, Category.id_comp]
    infer_instance
  have hci' : IsClosedImmersion (relativeLinearSystemMap p' hb') := by
    have h1 : IsClosedImmersion (relativeLinearSystemMap p' hb' ≫
        RelativeProjectiveSpace.toPolynomial m
          (𝟙 (Spec (CommRingCat.of (AlgebraicClosure K))))) := by
      rw [relativeLinearSystemMap_toPolynomial, Category.comp_id]
      exact hci
    exact (MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _ _).mp h1
  -- the base-change square
  have s : IsPullback (relativeLinearSystemMap p' hb' ≫ RelativeProjectiveSpace.toBase _ m) f
      (Langlands.GroupScheme.toAlgebraicClosure K)
      (relativeLinearSystemMap a.abelian.X.hom hb ≫ RelativeProjectiveSpace.toBase _ m) := by
    rw [relativeLinearSystemMap_toBase, relativeLinearSystemMap_toBase]
    exact (IsPullback.of_hasPullback a.abelian.X.hom (Langlands.GroupScheme.toAlgebraicClosure K)).flip
  have sq := IsPullback.of_right s
    (relativeLinearSystemMap_pullback a.abelian.X.hom p' f (Langlands.GroupScheme.toAlgebraicClosure K)
      Limits.pullback.condition hb)
    (RelativeProjectiveSpace.isPullback_map m (Langlands.GroupScheme.toAlgebraicClosure K))
  have hβ := RelativeProjectiveSpace.isPullback_map m (Langlands.GroupScheme.toAlgebraicClosure K)
  have : Surjective (RelativeProjectiveSpace.map m (Langlands.GroupScheme.toAlgebraicClosure K)) :=
    MorphismProperty.of_isPullback (P := @Surjective) hβ inferInstance
  have : Flat (RelativeProjectiveSpace.map m (Langlands.GroupScheme.toAlgebraicClosure K)) :=
    MorphismProperty.of_isPullback (P := @Flat) hβ inferInstance
  have : QuasiCompact (RelativeProjectiveSpace.map m (Langlands.GroupScheme.toAlgebraicClosure K)) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hβ inferInstance
  have : IsProper (relativeLinearSystemMap a.abelian.X.hom hb ≫
      RelativeProjectiveSpace.toBase _ m) := by
    rw [relativeLinearSystemMap_toBase]
    infer_instance
  have : IsProper (relativeLinearSystemMap a.abelian.X.hom hb) :=
    IsProper.of_comp _ (RelativeProjectiveSpace.toBase _ m)
  exact isClosedImmersion_of_isPullback_of_fpqc sq

/-- Lefschetz's cubic embedding over an arbitrary field follows from the separation statement
over algebraically closed fields. -/
theorem cubicFieldEmbedding_of_cubeSeparation
    (H : AlgClosedFieldAmpleCubeSeparationStatement.{u}) :
    CubicFieldEmbeddingStatement.{u} := by
  intro P K _ g d n hd a
  exact ⟨a.epi_cubicEvaluationAdjoint_of_cubeSeparation hd H,
    fun m b hb ↦ a.isClosedImmersion_relativeLinearSystemMap_of_cubeSeparation hd H m b hb⟩

end Langlands.AbelianScheme.PolarizedFiniteLevel
