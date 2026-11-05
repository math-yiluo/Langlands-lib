import Langlands.AlgebraicGeometry.ProjectiveBundle.EvaluationGeneration
import Langlands.AlgebraicGeometry.Modules.CoherentClosure
import Langlands.AlgebraicGeometry.Picard.FieldLineBundleTrivialityProof
import Langlands.AlgebraicGeometry.Picard.LineBundleQuasicoherent

/-! # Adjoint evaluation and intrinsic generation -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.Modules Langlands.AlgebraicGeometry.Picard
open scoped TensorProduct ChangeOfRings

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.ProjectiveBundle

variable {X S : Scheme.{u}} (p : X ⟶ S) {M : S.Modules} (L : LineBundle X)
    (ev : M ⟶ (Scheme.Modules.pushforward p).obj L.obj)

/-- The actual adjoint of the given evaluation morphism. -/
def evaluationAdjoint : (Scheme.Modules.pullback p).obj M ⟶ L.obj :=
  ((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv M L.obj).symm ev

/-- Adjoint evaluation on a pulled-back local section is the given evaluation. -/
lemma evaluationAdjoint_sectionPullback (U : S.Opens) (σ : Γ(M, U)) :
    (evaluationAdjoint p L ev).app (p ⁻¹ᵁ U) (sectionPullback p M U σ) = ev.app U σ := by
  have h := ((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv M L.obj).apply_symm_apply ev
  exact congrArg (fun k => k.app U σ) h

/-- The same evaluation formula after restriction on the total space. -/
lemma evaluationAdjoint_sectionPullbackLE {U : S.Opens} {V : X.Opens}
    (h : V ≤ p ⁻¹ᵁ U) (σ : Γ(M, U)) :
    (evaluationAdjoint p L ev).app V (sectionPullbackLE p M h σ) =
      L.obj.presheaf.map (homOfLE h).op (ev.app U σ) := by
  exact (PresheafOfModules.naturality_apply (evaluationAdjoint p L ev).val
    (homOfLE h).op _).trans (congrArg _ (evaluationAdjoint_sectionPullback p L ev U σ))

private lemma pullback_map_sectionPullbackLE {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    {N P : Z.Modules} (g : N ⟶ P) {A : Y.Opens} {B : Z.Opens}
    (h : A ≤ f ⁻¹ᵁ B) (s : Γ(N, B)) :
    ((Scheme.Modules.pullback f).map g).app A (sectionPullbackLE f N h s) =
      sectionPullbackLE f P h (g.app B s) := by
  dsimp only [sectionPullbackLE]
  exact (PresheafOfModules.naturality_apply ((Scheme.Modules.pullback f).map g).val
    (homOfLE h).op _).trans
      (congrArg _ (sectionPullback_naturality f g B s).symm)

/-- The actual adjoint evaluation after restriction over a base open. -/
def localEvaluationAdjoint (U : S.Opens) :
    (Scheme.Modules.pullback ((p ⁻¹ᵁ U).ι ≫ p)).obj M ⟶
      (evaluationLineBundle p L U).obj :=
  (Scheme.Modules.pullbackComp (p ⁻¹ᵁ U).ι p).inv.app M ≫
    (Scheme.Modules.pullback (p ⁻¹ᵁ U).ι).map (evaluationAdjoint p L ev)

/-- The restricted adjoint takes a pulled-back base section to its local evaluation. -/
lemma localEvaluationAdjoint_sectionPullbackLE (U : S.Opens) (σ : Γ(M, U)) :
    (localEvaluationAdjoint p L ev U).app ⊤
        (sectionPullbackLE ((p ⁻¹ᵁ U).ι ≫ p) M
          (show ⊤ ≤ ((p ⁻¹ᵁ U).ι ≫ p) ⁻¹ᵁ U from fun x _ => x.property) σ) =
      localSectionEvaluation p L ev U σ := by
  dsimp only [localEvaluationAdjoint]
  rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  rw [pullbackComp_inv_sectionPullbackLE (p ⁻¹ᵁ U).ι p M le_rfl
    (show ⊤ ≤ (p ⁻¹ᵁ U).ι ⁻¹ᵁ (p ⁻¹ᵁ U) by simp)]
  erw [pullback_map_sectionPullbackLE, sectionPullbackLE_self,
    evaluationAdjoint_sectionPullback]
  exact (openSection_eq_sectionPullbackLE L.obj (p ⁻¹ᵁ U) (ev.app U σ)).symm

/-- Restriction preserves surjectivity of the adjoint evaluation. -/
instance localEvaluationAdjoint_epi (U : S.Opens) [Epi (evaluationAdjoint p L ev)] :
    Epi (localEvaluationAdjoint p L ev U) := by
  dsimp only [localEvaluationAdjoint]
  infer_instance

/-- A surjective actual adjoint evaluation supplies intrinsic nonvanishing witnesses. -/
theorem evaluationGenerates_of_epi_evaluationAdjoint [M.IsQuasicoherent]
    [Epi (evaluationAdjoint p L ev)] : EvaluationGenerates p L ev := by
  classical
  intro x
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show p x ∈ (⊤ : S.Opens) from trivial)
  let A : X.Opens := p ⁻¹ᵁ U
  let y : A.toScheme := ⟨x, hxU⟩
  let q := A.toScheme.fromSpecResidueField y
  let r := q ≫ (A.ι ≫ p)
  let Lq := (LineBundle.pullback q).obj (evaluationLineBundle p L U)
  let θ : (Scheme.Modules.pullback r).obj M ⟶ Lq.obj :=
    (Scheme.Modules.pullbackComp q (A.ι ≫ p)).inv.app M ≫
      (Scheme.Modules.pullback q).map (localEvaluationAdjoint p L ev U)
  have hA : ⊤ ≤ (A.ι ≫ p) ⁻¹ᵁ U := fun z _ => z.property
  have hq : ⊤ ≤ q ⁻¹ᵁ (⊤ : A.toScheme.Opens) := le_top
  have hr : ⊤ ≤ r ⁻¹ᵁ U := by
    intro z _
    change p (A.ι (q z)) ∈ U
    rw [show q z = y from Scheme.fromSpecResidueField_apply y z]
    exact y.property
  have hθ (σ : Γ(M, U)) :
      θ.app ⊤ (sectionPullbackLE r M hr σ) =
        residueSection (evaluationLineBundle p L U).obj
          (localSectionEvaluation p L ev U σ) y := by
    dsimp only [θ]
    rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
    rw [pullbackComp_inv_sectionPullbackLE q (A.ι ≫ p) M hA hq hr]
    erw [pullback_map_sectionPullbackLE, localEvaluationAdjoint_sectionPullbackLE]
    exact (pullbackSection_eq_sectionPullbackLE q _ _).symm
  refine ⟨U, hxU, ?_⟩
  by_contra hz
  simp only [not_exists] at hz
  have hzero (σ : Γ(M, U)) : θ.app ⊤ (sectionPullbackLE r M hr σ) = 0 := by
    apply (hθ σ).trans
    by_contra hσ
    exact hz σ ((mem_nonvanishingLocus _ _ y).mpr hσ)
  have hθzero (s : Γ((Scheme.Modules.pullback r).obj M, ⊤)) : θ.app ⊤ s = 0 := by
    obtain ⟨z, rfl⟩ := (pullbackTensorMap_bijective r M hr (isAffineOpen_top _) hU).surjective s
    induction z using TensorProduct.inductionOn with
    | tmul a σ =>
      rw [pullbackTensorMap_tmul, Scheme.Modules.Hom.app_smul, hzero, smul_zero]
    | add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]
  have : Epi θ := by
    dsimp only [θ]
    infer_instance
  have hsurj := QuasicoherentLocal.surjective_app_of_epi θ ⊤ (isAffineOpen_top _)
  obtain ⟨e⟩ := fieldLineBundleTriviality (A.toScheme.residueField y) Lq
  have h1 : (1 : Γ(Spec (A.toScheme.residueField y), ⊤)) ≠ 0 := by
    intro h
    have hh := congrArg (Scheme.ΓSpecIso (A.toScheme.residueField y)).hom h
    exact one_ne_zero (by simpa only [map_one, map_zero] using hh)
  obtain ⟨s, hs⟩ := hsurj (e.inv.app ⊤ (1 : Γ(Spec (A.toScheme.residueField y), ⊤)))
  have hezero : e.inv.app ⊤ (1 : Γ(Spec (A.toScheme.residueField y), ⊤)) = 0 :=
    hs.symm.trans (hθzero s)
  apply h1
  apply (ConcreteCategory.bijective_of_isIso (e.inv.app ⊤)).injective
  simpa only [map_zero] using hezero

/-- Surjective adjoint evaluation supplies the generation hypothesis in every frame rank. -/
lemma frameEvaluationGenerates_of_epi_evaluationAdjoint [M.IsQuasicoherent]
    [Epi (evaluationAdjoint p L ev)] (n : ℕ) : FrameEvaluationGenerates p L ev n :=
  (evaluationGenerates_of_epi_evaluationAdjoint p L ev).frameEvaluationGenerates p L ev

end Langlands.AlgebraicGeometry.ProjectiveBundle
