import Langlands.AlgebraicGeometry.ProjectiveBundle.EvaluationAdjoint
import Langlands.AlgebraicGeometry.Modules.DerivedRestriction
import Mathlib.AlgebraicGeometry.Fiber

/-! # Fibrewise criteria for intrinsic evaluation generation -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.Modules Langlands.AlgebraicGeometry.Picard
open Langlands.AlgebraicGeometry.Modules.DerivedSections
open scoped TensorProduct ChangeOfRings

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.ProjectiveBundle

private lemma epi_map_iff_of_natIso {C D : Type*} [Category* C] [Category* D]
    {F G : C ⥤ D} (e : F ≅ G) {N P : C} (φ : N ⟶ P) :
    Epi (F.map φ) ↔ Epi (G.map φ) := by
  constructor
  · intro h
    have : Epi (F.map φ) := h
    have he : G.map φ = e.inv.app N ≫ F.map φ ≫ e.hom.app P := by simp
    rw [he]
    infer_instance
  · intro h
    have : Epi (G.map φ) := h
    have he : F.map φ = e.hom.app N ≫ G.map φ ≫ e.inv.app P := by simp
    rw [he]
    infer_instance

private lemma epi_pullback_map_residue_restrict {X : Scheme.{u}}
    {N P : X.Modules} (φ : N ⟶ P)
    (hφ : ∀ x : X, Epi ((Scheme.Modules.pullback (X.fromSpecResidueField x)).map φ))
    (A : X.Opens) (y : A.toScheme) :
    Epi ((Scheme.Modules.pullback (A.toScheme.fromSpecResidueField y)).map
      ((Scheme.Modules.pullback A.ι).map φ)) := by
  let q := A.toScheme.fromSpecResidueField y
  let a := Spec.map (A.ι.residueFieldMap y)
  have : Epi ((Scheme.Modules.pullback (X.fromSpecResidueField (A.ι y))).map φ) :=
    hφ (A.ι y)
  have ha : Epi ((Scheme.Modules.pullback a).map
      ((Scheme.Modules.pullback (X.fromSpecResidueField (A.ι y))).map φ)) :=
    inferInstance
  have hc : Epi ((Scheme.Modules.pullback (a ≫ X.fromSpecResidueField (A.ι y))).map φ) :=
    (epi_map_iff_of_natIso
      (Scheme.Modules.pullbackComp a (X.fromSpecResidueField (A.ι y))) φ).mp ha
  have he : a ≫ X.fromSpecResidueField (A.ι y) = q ≫ A.ι :=
    A.ι.SpecMap_residueFieldMap_fromSpecResidueField y
  rw [he] at hc
  exact (epi_map_iff_of_natIso (Scheme.Modules.pullbackComp q A.ι) φ).mpr hc

private lemma pullback_map_sectionPullbackLE {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    {N P : Z.Modules} (g : N ⟶ P) {A : Y.Opens} {B : Z.Opens}
    (h : A ≤ f ⁻¹ᵁ B) (s : Γ(N, B)) :
    ((Scheme.Modules.pullback f).map g).app A (sectionPullbackLE f N h s) =
      sectionPullbackLE f P h (g.app B s) := by
  dsimp only [sectionPullbackLE]
  exact (PresheafOfModules.naturality_apply ((Scheme.Modules.pullback f).map g).val
    (homOfLE h).op _).trans
      (congrArg _ (sectionPullback_naturality f g B s).symm)

variable {X S : Scheme.{u}} (p : X ⟶ S) {M : S.Modules} (L : LineBundle X)
    (ev : M ⟶ (Scheme.Modules.pushforward p).obj L.obj)

/-- The actual original adjoint evaluation, pulled back to a residue-field fibre. -/
def fibreEvaluationAdjoint (s : S) :
    (Scheme.Modules.pullback (p.fiberToSpecResidueField s)).obj
        ((Scheme.Modules.pullback (S.fromSpecResidueField s)).obj M) ⟶
      (Scheme.Modules.pullback (p.fiberι s)).obj L.obj :=
  (pullbackSquareIso (S.fromSpecResidueField s) p (p.fiberToSpecResidueField s)
      (p.fiberι s) (p.fiber_fac s)).inv.app M ≫
    (Scheme.Modules.pullback (p.fiberι s)).map (evaluationAdjoint p L ev)

/-- Epimorphy after pullback to every original residue point gives intrinsic
generation, without requiring epimorphy on the total space. -/
theorem evaluationGenerates_of_residue_epi [M.IsQuasicoherent]
    (hres : ∀ x : X, Epi ((Scheme.Modules.pullback (X.fromSpecResidueField x)).map
      (evaluationAdjoint p L ev))) : EvaluationGenerates p L ev := by
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
  have : Epi ((Scheme.Modules.pullback q).map
      ((Scheme.Modules.pullback A.ι).map (evaluationAdjoint p L ev))) :=
    epi_pullback_map_residue_restrict (evaluationAdjoint p L ev) hres A y
  have : Epi ((Scheme.Modules.pullback q).map (localEvaluationAdjoint p L ev U)) := by
    dsimp only [localEvaluationAdjoint]
    rw [Functor.map_comp]
    infer_instance
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

/-- Epimorphy of the original adjoint on all actual fibres supplies the
intrinsic generation needed by projective evaluation. -/
theorem evaluationGenerates_of_fibre_epi [M.IsQuasicoherent]
    (hfib : ∀ s : S, Epi (fibreEvaluationAdjoint p L ev s)) :
    EvaluationGenerates p L ev := by
  apply evaluationGenerates_of_residue_epi p L ev
  intro x
  let e := pullbackSquareIso (S.fromSpecResidueField (p x)) p
    (p.fiberToSpecResidueField (p x)) (p.fiberι (p x)) (p.fiber_fac (p x))
  have : Epi (e.inv.app M ≫ (Scheme.Modules.pullback (p.fiberι (p x))).map
      (evaluationAdjoint p L ev)) := hfib (p x)
  have : Epi ((Scheme.Modules.pullback (p.fiberι (p x))).map
      (evaluationAdjoint p L ev)) := by
    exact epi_of_epi (e.inv.app M)
      ((Scheme.Modules.pullback (p.fiberι (p x))).map (evaluationAdjoint p L ev))
  have h : Epi ((Scheme.Modules.pullback (p.asFiberHom x)).map
      ((Scheme.Modules.pullback (p.fiberι (p x))).map (evaluationAdjoint p L ev))) :=
    inferInstance
  have hc := (epi_map_iff_of_natIso
    (Scheme.Modules.pullbackComp (p.asFiberHom x) (p.fiberι (p x)))
      (evaluationAdjoint p L ev)).mp h
  have he : p.asFiberHom x ≫ p.fiberι (p x) = X.fromSpecResidueField x :=
    p.asFiberHom_fiberι x
  rw [he] at hc
  exact hc

end Langlands.AlgebraicGeometry.ProjectiveBundle
