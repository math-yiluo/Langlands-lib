import Langlands.Automorphic.ArchimedeanAlgebraicCoefficient
import Langlands.Global.ArchimedeanVectorSmooth
import Langlands.GroupScheme.MatrixRepresentationProductSmooth
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Smooth orbit maps of the actual archimedean algebraic coefficients -/

noncomputable section

universe uF uE uM

open scoped Classical Manifold ContDiff Matrix Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ)
variable {I : Type} (e : I → EmbeddingIndex F)

/-- Each selected oriented embedding is a smooth map on the actual units
manifold in mixed archimedean coordinates. -/
theorem contMDiff_embeddingGL (i : I) :
    ContMDiff 𝓘(ℝ, ArchimedeanMatrix F n) 𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ) ∞
      (fun x : ArchimedeanGL F n =>
        embeddingGL F n e ((archimedeanGLCoordinates F n).symm x) i) := by
  apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
  let L : ArchimedeanMatrix F n →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    ((embeddingComponent F (e i)).mapMatrix.toLinearMap).toContinuousLinearMap
  have hL : ContMDiff 𝓘(ℝ, ArchimedeanMatrix F n)
      𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ) ∞ L := L.contDiff.contMDiff
  have hV : ContMDiff 𝓘(ℝ, ArchimedeanMatrix F n)
      𝓘(ℝ, ArchimedeanMatrix F n) ∞
      (fun x : ArchimedeanGL F n => x.val) := Units.contMDiff_val
  have h : ContMDiff 𝓘(ℝ, ArchimedeanMatrix F n)
      𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ) ∞
      (fun x : ArchimedeanGL F n => L x.val) := hL.comp hV
  change ContMDiff 𝓘(ℝ, ArchimedeanMatrix F n)
    𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ) ∞
    (fun x : ArchimedeanGL F n => (embeddingComponent F (e i)).mapMatrix x.val) at h
  simpa only [Function.comp_def, embeddingGL_val,
    ContinuousMulEquiv.apply_symm_apply, embeddingMatrixHom, AlgHom.pi_apply] using h

end Langlands.Global.ArchimedeanGL

namespace Langlands.Automorphic.ArchimedeanAlgebraicCoefficient

open Langlands.Global Langlands.Global.ArchimedeanGL Langlands.GroupScheme

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}
variable {I : Type} [Finite I] (e : I → EmbeddingIndex F)
variable {m : Type} [Fintype m] [DecidableEq m]
variable (ρ : MatrixRepresentation
  (GeneralLinearProductDualNumber.groupScheme (fun _ : I => Fin n)
    (CommRingCat.of ℂ)) m)

instance : NormedAddCommGroup (Space e ρ) :=
  inferInstanceAs (NormedAddCommGroup (m → ℂ))
instance : NormedSpace ℂ (Space e ρ) :=
  inferInstanceAs (NormedSpace ℂ (m → ℂ))
instance : CompleteSpace (Space e ρ) :=
  inferInstanceAs (CompleteSpace (m → ℂ))

/-- Smoothness of the actual evaluated scheme matrix is derived from its
regular functions and the selected oriented completion coordinates. -/
theorem contMDiff_representation_matrix :
    ContMDiff 𝓘(ℝ, ArchimedeanMatrix F n) 𝓘(ℝ, Matrix m m ℂ) ∞
      (fun x : ArchimedeanGL F n =>
        ρ.productMatrixPointsHom ℂ
          (embeddingGL F n e ((archimedeanGLCoordinates F n).symm x))) :=
  ρ.contMDiff_productMatrixPointsHom 𝓘(ℝ, ArchimedeanMatrix F n) _
    (contMDiff_embeddingGL F n e)

private def matrixEntry (a b : m) : Matrix m m ℂ →L[ℝ] ℂ where
  toLinearMap :=
    { toFun := fun A => A a b
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  cont := (continuous_apply b).comp (continuous_apply a)

/-- Smooth parameter families of group elements and vectors give the actual
smooth coefficient action, with no regularity premise on the representation. -/
theorem contMDiff_representation_action
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type uE} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
    (g : M → ArchimedeanGL F n) (v : M → Space e ρ)
    (hg : ContMDiff J 𝓘(ℝ, ArchimedeanMatrix F n) ∞ g)
    (hv : ContMDiff J 𝓘(ℝ, Space e ρ) ∞ v) :
    ContMDiff J 𝓘(ℝ, Space e ρ) ∞
      (fun x => representation e ρ ((archimedeanGLCoordinates F n).symm (g x)) (v x)) := by
  have hA : ContMDiff J 𝓘(ℝ, Matrix m m ℂ) ∞
      (fun x => (ρ.productMatrixPointsHom ℂ
        (embeddingGL F n e ((archimedeanGLCoordinates F n).symm (g x))) :
          Matrix m m ℂ)) :=
    Units.contMDiff_val.comp ((contMDiff_representation_matrix e ρ).comp hg)
  change ContMDiff J 𝓘(ℝ, m → ℂ) ∞
    (fun x => (ρ.productMatrixPointsHom ℂ
      (embeddingGL F n e ((archimedeanGLCoordinates F n).symm (g x))) :
        Matrix m m ℂ) *ᵥ (v x : m → ℂ))
  apply contMDiff_pi_space.mpr
  intro a
  change ContMDiff J 𝓘(ℝ, ℂ) ∞
    (fun x => ∑ b, (ρ.productMatrixPointsHom ℂ
      (embeddingGL F n e ((archimedeanGLCoordinates F n).symm (g x))) :
        Matrix m m ℂ) a b * (v x : m → ℂ) b)
  apply contMDiff_finsetSum
  intro b _
  exact (contDiff_mul (𝕜 := ℝ) (𝔸 := ℂ)).contMDiff.comp
    (((matrixEntry a b).contDiff.contMDiff.comp hA).prodMk_space
      ((ContinuousLinearMap.proj b : (m → ℂ) →L[ℝ] ℂ).contDiff.contMDiff.comp hv))

/-- The joint action on the whole finite-free coefficient space is real smooth. -/
theorem contMDiff_jointAction :
    ContMDiff (𝓘(ℝ, ArchimedeanMatrix F n).prod 𝓘(ℝ, Space e ρ))
      𝓘(ℝ, Space e ρ) ∞
      (fun p : ArchimedeanGL F n × Space e ρ =>
        representation e ρ ((archimedeanGLCoordinates F n).symm p.1) p.2) :=
  contMDiff_representation_action e ρ Prod.fst Prod.snd contMDiff_fst contMDiff_snd

/-- Every vector in the full algebraic coefficient space has a smooth orbit map. -/
theorem contMDiff_orbit (v : Space e ρ) :
    ContMDiff 𝓘(ℝ, ArchimedeanMatrix F n) 𝓘(ℝ, Space e ρ) ∞
      (fun x : ArchimedeanGL F n =>
        representation e ρ ((archimedeanGLCoordinates F n).symm x) v) :=
  contMDiff_representation_action e ρ id (fun _ => v) contMDiff_id contMDiff_const

/-- The actual orbit function gives an intertwining realization in the existing
space of vector valued smooth functions with right translation. -/
def smoothOrbitMap :
    (representation e ρ).IntertwiningMap (vectorSmoothRightAction F n (Space e ρ)) where
  toLinearMap :=
    { toFun v := ⟨fun g => representation e ρ g v, contMDiff_orbit e ρ v⟩
      map_add' v w := by ext g; exact map_add (representation e ρ g) v w
      map_smul' c v := by ext g; exact map_smul (representation e ρ g) c v }
  isIntertwining' g := by
    ext v x
    exact (congrArg (fun T => T v) (map_mul (representation e ρ) x g)).symm

@[simp]
theorem smoothOrbitMap_apply (v : Space e ρ) (g : InfiniteAdelicGL F n) :
    (smoothOrbitMap e ρ v).val g = representation e ρ g v := rfl

@[simp]
theorem smoothOrbitMap_one (v : Space e ρ) :
    (smoothOrbitMap e ρ v).val 1 = v := by
  change representation e ρ 1 v = v
  simp

theorem smoothOrbitMap_injective : Function.Injective (smoothOrbitMap e ρ) := by
  intro v w h
  have h₁ := congrArg (fun f : VectorSmoothFunctions F n (Space e ρ) => f.val 1) h
  simpa only [smoothOrbitMap_one] using h₁

@[simp]
theorem smoothOrbitMap_rightAction (g : InfiniteAdelicGL F n) (v : Space e ρ) :
    smoothOrbitMap e ρ (representation e ρ g v) =
      vectorSmoothRightAction F n (Space e ρ) g (smoothOrbitMap e ρ v) :=
  Representation.IntertwiningMap.isIntertwining _ _ (smoothOrbitMap e ρ) g v

end Langlands.Automorphic.ArchimedeanAlgebraicCoefficient
