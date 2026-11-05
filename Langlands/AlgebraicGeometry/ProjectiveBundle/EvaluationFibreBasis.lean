import Langlands.AlgebraicGeometry.ProjectiveBundle.EvaluationFibreBaseChange
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # A genuine basis of the original-residue-field coefficients -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Langlands.Scheme.Modules Langlands.SchemeModule

universe u v

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.ProjectiveBundle

private def affineSectionPullbackBasis {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    (M : Z.Modules) [M.IsQuasicoherent] {A : Y.Opens} {B : Z.Opens}
    (h : A ≤ f ⁻¹ᵁ B) (hA : IsAffineOpen A) (hB : IsAffineOpen B)
    {I : Type v} (b : Module.Basis I Γ(Z, B) Γ(M, B)) :
    Module.Basis I Γ(Y, A) Γ((Scheme.Modules.pullback f).obj M, A) := by
  letI : Algebra Γ(Z, B) Γ(Y, A) := (f.appLE B A h).hom.toAlgebra
  exact (b.baseChange Γ(Y, A)).map
    (LinearEquiv.ofBijective (pullbackTensorMap f M h).hom
      (pullbackTensorMap_bijective f M h hA hB))

private lemma affineSectionPullbackBasis_apply {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    (M : Z.Modules) [M.IsQuasicoherent] {A : Y.Opens} {B : Z.Opens}
    (h : A ≤ f ⁻¹ᵁ B) (hA : IsAffineOpen A) (hB : IsAffineOpen B)
    {I : Type v} (b : Module.Basis I Γ(Z, B) Γ(M, B)) (i : I) :
    affineSectionPullbackBasis f M h hA hB b i = sectionPullbackLE f M h (b i) := by
  let : Algebra Γ(Z, B) Γ(Y, A) := (f.appLE B A h).hom.toAlgebra
  change (pullbackTensorMap f M h) ((b.baseChange Γ(Y, A)) i) = _
  rw [Module.Basis.baseChange_apply]
  exact pullbackTensorMap_one_tmul f M h (b i)

variable {S : Scheme.{u}} {M : S.Modules} {n : ℕ}

/-- Fixed-rank local freeness supplies an affine frame near every point. -/
lemma exists_affine_frameOpen (hM : IsLocallyFreeOfRank M (n + 1)) (s : S) :
    ∃ U : FrameOpen M n, s ∈ U.val ∧ IsAffineOpen U.val := by
  obtain ⟨U, hsU⟩ := exists_frameOpen M n hM s
  obtain ⟨V, hV, hsV, hVU⟩ := exists_isAffineOpen_mem_and_subset hsU
  exact ⟨⟨V, ⟨(frame M n U).restrict hVU⟩⟩, hsV, hV⟩

/-- The nearby frame as a genuine basis of its actual section module. -/
def LocalFrame.sectionBasis {U : S.Opens} (e : LocalFrame M n U) :
    Module.Basis (Fin (n + 1)) Γ(S, U) Γ(M, U) :=
  Module.Basis.ofEquivFun (e.coordinates U le_rfl)

@[simp]
lemma LocalFrame.sectionBasis_apply {U : S.Opens} (e : LocalFrame M n U)
    (i : Fin (n + 1)) : e.sectionBasis i = e.basisSection U le_rfl i := by
  classical
  exact congrFun (Module.Basis.coe_ofEquivFun _) i

variable [M.IsQuasicoherent]

/-- The affine section comparison constructs a basis of the actual pulled-back coefficients. -/
def fibreFrameBasis (U : FrameOpen M n) (hU : IsAffineOpen U.val)
    (s : S) (hs : s ∈ U.val) :
    Module.Basis (Fin (n + 1)) Γ(Spec (S.residueField s), ⊤)
      (GlobalSections ((Scheme.Modules.pullback (S.fromSpecResidueField s)).obj M)) :=
  affineSectionPullbackBasis (S.fromSpecResidueField s) M (fibreFrame_mem U s hs)
    (isAffineOpen_top _) hU (frame M n U).sectionBasis

/-- The constructed basis consists exactly of the actual pulled-back frame coefficients. -/
@[simp]
lemma fibreFrameBasis_apply (U : FrameOpen M n) (hU : IsAffineOpen U.val)
    (s : S) (hs : s ∈ U.val) (i : Fin (n + 1)) :
    fibreFrameBasis U hU s hs i = fibreFrameSections U s hs i := by
  rw [fibreFrameBasis, affineSectionPullbackBasis_apply, LocalFrame.sectionBasis_apply]
  rfl

end Langlands.AlgebraicGeometry.ProjectiveBundle
