import Langlands.Algebra.BrauerComparison.BaseChangeChart
import Langlands.Algebra.BrauerComparison.RelativeLaws
import Langlands.Algebra.BrauerSplitting
import Langlands.Algebra.CentralSimple.FiniteGaloisSplitting
import Langlands.ClassField.Global.H1VanishingProof
import Langlands.ClassField.Global.IdeleArchimedean
import Langlands.ClassField.Global.ReciprocityTower
import Langlands.ClassFieldTheory.Local.LocalInvariantFamilyRelativeImagesProof
import Langlands.ClassFieldTheory.Local.UnramifiedH2Proof

/-! # Splitting central simple algebras over number fields -/

noncomputable section

universe u

open CategoryTheory NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct NumberField.LiesOver Langlands.Global.AdelicFunctoriality.FiniteExtension
open scoped Langlands.Global.AdelicFunctoriality.InfiniteExtension

namespace Langlands.BrauerComparison

open Langlands.ClassField.Global Langlands.ClassFieldTheory.Local Langlands.CentralSimple
open Langlands.CentralSimple.SemilinearGaloisAction
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open FundamentalClass Reciprocity

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E] {A : CSA.{u, u} F}

local notation "d" => reducedDegree F A

omit [NumberField F] in
/-- A matrix chart for the scalar extension of a fixed algebra has the original reduced degree. -/
private theorem exists_chart_of_baseChange_isSplit (K : Type u) [Field K] [Algebra F K]
    (h : Brauer.IsSplit (Brauer.baseChange K A)) :
    Nonempty (K ⊗[F] A ≃ₐ[K] Matrix (Fin d) (Fin d) K) := by
  obtain ⟨n, _, ⟨f⟩⟩ := h
  have hn := matrix_size_eq_reducedDegree F A K n f
  subst n
  exact ⟨f⟩

/-- Finite-place localization of the relative Brauer class is computed by the extended chart. -/
theorem unitsLocalMap_relativeClass
    (e : E ⊗[F] A ≃ₐ[E] Matrix (Fin d) (Fin d) E)
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal] :
    (unitsLocalMap v w 2).hom (relativeClass e) =
      relativeClass (baseChangeSplittingChart (v.adicCompletion F) (w.adicCompletion E) e) := by
  let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (reducedDegree_pos F A)
  rw [relativeClass_baseChangeSplittingChart]
  simp only [relativeClass, descentClass, unitClass, groupCohomology.H2π_comp_map_apply]
  congr 1

set_option maxHeartbeats 800000 in
private theorem archimedeanInvariant_relativeClass_eq_zero_of_split
    (e : E ⊗[F] A ≃ₐ[E] Matrix (Fin d) (Fin d) E) (w : InfinitePlace E)
    (h : Brauer.IsSplit (Brauer.baseChange (w.comap (algebraMap F E)).Completion A)) :
    archimedeanInvariant w (relativeClass e) = 0 := by
  classical
  let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (reducedDegree_pos F A)
  let v := w.comap (algebraMap F E)
  let : w.LiesOver v := ⟨rfl⟩
  let K := v.Completion
  let M := w.Completion
  let : IsScalarTower F E M := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply F K M]
    exact NumberField.LiesOver.completionMap_coe (v := v) (w := w) (WithAbs.toAbs v.1 x)
  unfold archimedeanInvariant
  rw [relativeClass, descentClass, unitClass, H2Lift_H2π]
  let ρ := splittingChartIndexAction e
  change archimedeanCocycleHom w (unitCocycle ρ.scalarDefect ρ.scalarDefect_isTwoCocycle) = 0
  simp only [archimedeanCocycleHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  split_ifs with hc <;> try rfl
  let c := hc.choose
  have hconj := isConj_of_mem_stabilizer w hc.choose_spec.1 hc.choose_spec.2
  have hw : w.IsComplex := by
    apply InfinitePlace.not_isReal_iff_isComplex.mp
    intro hr
    apply hc.choose_spec.2
    apply AlgEquiv.ext
    intro x
    apply w.embedding.injective
    exact (hconj.eq x).trans (congrArg (fun p : E →+* ℂ => p x)
      (InfinitePlace.conjugate_embedding_eq_of_isReal hr))
  have hv : v.IsReal := by
    change (w.comap (algebraMap F E)).IsReal
    rw [← InfinitePlace.mk_embedding w, InfinitePlace.comap_mk, InfinitePlace.isReal_mk_iff]
    exact hconj.isReal_comp
  let D := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
  let σ₀ := D.trans (Complex.conjAe.toRingEquiv.trans D.symm)
  let σ : M ≃ₐ[K] M :=
    { σ₀ with
      commutes' := by
        intro x
        apply D.injective
        change D (D.symm (star (D (algebraMap K M x)))) = D (algebraMap K M x)
        rw [D.apply_symm_apply]
        let := InfinitePlace.LiesOver.extensionEmbedding_liesOver_of_isReal w hv
        change star (InfinitePlace.Completion.extensionEmbedding w (algebraMap K M x)) =
          InfinitePlace.Completion.extensionEmbedding w (algebraMap K M x)
        rw [InfinitePlace.Completion.liesOver_extensionEmbedding_apply (v := v) w,
          ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hv]
        exact Complex.conj_ofReal _ }
  have hσ (x : M) : D (σ x) = star (D x) := D.apply_symm_apply _
  have hσ₂ : σ * σ = 1 := by
    apply AlgEquiv.ext
    intro x
    apply D.injective
    change D (σ (σ x)) = D x
    rw [hσ, hσ, star_star]
  have hD (a : E) : D (algebraMap E M a) = w.embedding a :=
    extensionEmbedding_algebraMap w a
  have hres : (σ.restrictScalars F).restrictNormal E = c := by
    apply AlgEquiv.ext
    intro a
    apply (algebraMap E M).injective
    rw [AlgEquiv.restrictNormal_commutes]
    apply D.injective
    change D (σ (algebraMap E M a)) = D (algebraMap E M (c a))
    rw [hσ, hD, hD]
    exact (hconj.eq a).symm
  obtain ⟨f⟩ := exists_chart_of_baseChange_isSplit K h
  let e' := baseChangeSplittingChart K M e
  have hz : relativeClass e' = 0 := relativeClass_eq_zero_of_split e' f
  have heq := descentClass_eq_of_lifts (splittingChartIndexAction e')
    (baseChangeLift K M e) (baseChangeFactor K M ρ.scalarDefect)
    (baseChangeSplittingChart_action K M e) (baseChangeLift_mul K M e)
  have hb := (unitClass_eq_zero_iff _ _).mp (heq.symm.trans hz)
  obtain ⟨b, hb⟩ := hb
  let r : Gal(M/K) →* Gal(E/F) :=
    (AlgEquiv.restrictNormalHom E).comp (AlgEquiv.restrictScalarsHom F)
  have hres1 : (AlgEquiv.restrictScalars F (1 : Gal(M/K))).restrictNormal E = 1 := map_one r
  have hsig : w.embedding (conjugationValue c
      (unitCocycle ρ.scalarDefect ρ.scalarDefect_isTwoCocycle) : E) =
        star (D (b σ : M)) * D (b σ : M) := by
    have hmul := congrArg (fun x : Mˣ => D (x : M)) (congrArg₂ (· * ·) (hb σ σ) (hb 1 1))
    change D (algebraMap E M (ρ.scalarDefect _ _ : E) *
        algebraMap E M (ρ.scalarDefect _ _ : E)) = _ at hmul
    rw [hres, hres1, map_mul, hD, hD] at hmul
    change w.embedding ((ρ.scalarDefect c c : E) * (ρ.scalarDefect 1 1 : E)) = _
    rw [map_mul, hmul]
    have h : ScalarTwoCocycle.coboundary b σ σ * ScalarTwoCocycle.coboundary b 1 1 =
        b σ * (σ • b σ) := by
      simp only [ScalarTwoCocycle.coboundary, hσ₂, one_mul, one_smul]
      group
    rw [h, Units.val_mul, map_mul, mul_comm]
    change D (σ (b σ : M)) * D (b σ : M) = _
    rw [hσ]
  rw [hsig]
  exact signClass_star_mul_self _

end Langlands.BrauerComparison

namespace Langlands.Brauer

open Langlands.BrauerComparison Langlands.CentralSimple
open Langlands.ClassField.Global Langlands.ClassFieldTheory.Local

/-- A central simple algebra over a number field splits if it splits at every completion. -/
def NumberFieldBrauerSplittingStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (A : CSA.{u, u} F),
    (∀ v : HeightOneSpectrum (𝓞 F), IsSplit (baseChange (v.adicCompletion F) A)) →
    (∀ v : InfinitePlace F, IsSplit (baseChange v.Completion A)) → IsSplit A

/-- The splitting form of Brauer–Hasse–Noether, via finite relative unit cohomology. -/
theorem numberFieldBrauerSplitting : NumberFieldBrauerSplittingStatement.{u} := by
  intro F _ _ A hfin hinf
  let E := finiteGaloisSplittingField F A
  let e := finiteGaloisSplittingChart F A
  let : NumberField E := NumberField.of_module_finite F E
  let : Nonempty (Fin (reducedDegree F A)) := Fin.pos_iff_nonempty.mp (reducedDegree_pos F A)
  have hz : relativeClass e = 0 := by
    apply Reciprocity.eq_zero_of_local_eq_zero ideleClassH1Vanishing
      (fun p _ => localInvariantFamily unramifiedH2Exhaustion p)
      (fun p _ => localInvariantFamilyRelativeImages unramifiedH2Exhaustion p)
    · intro v w hw
      rw [unitsLocalMap_relativeClass]
      obtain ⟨f⟩ := exists_chart_of_baseChange_isSplit (v.adicCompletion F) (hfin v)
      exact relativeClass_eq_zero_of_split _ f
    · exact fun w => archimedeanInvariant_relativeClass_eq_zero_of_split e w (hinf _)
  exact ⟨reducedDegree F A, reducedDegree_pos F A, split_of_relativeClass_eq_zero e hz⟩

end Langlands.Brauer
