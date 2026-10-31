import Langlands.Automorphic.DeterminantMultiplier
import Langlands.Automorphic.Smooth
import Langlands.Global.HeckeCharacterFiniteOrder

/-! # Finite-order determinant multiplication on actual smooth adelic functions -/

noncomputable section

universe u

open scoped Classical Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000

namespace Langlands.Global.HeckeCharacter

variable {F : Type u} [Field F] [NumberField F] (n : ℕ)

/-- The actual finite determinant kernel is open for a finite-order character. -/
def finiteDeterminantKernel (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    OpenSubgroup (FiniteAdelicGL F n) where
  toSubgroup := ((χ.adelicDeterminant n).toMonoidHom.comp
    (AdelicGL.ofFinite F n).toMonoidHom).ker
  isOpen' := by
    change IsOpen {d : FiniteAdelicGL F n |
      χ.adelicDeterminant n (AdelicGL.ofFinite F n d) = 1}
    exact (hχ.isLocallyConstant_pullback
      ((ideleClassMap F).continuous.comp
        ((AdelicGL.determinant F n).continuous.comp
          (AdelicGL.ofFinite F n).continuous))).isOpen_fiber 1

@[simp]
theorem mem_finiteDeterminantKernel (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (d : FiniteAdelicGL F n) :
    d ∈ χ.finiteDeterminantKernel n hχ ↔
      χ.adelicDeterminant n (AdelicGL.ofFinite F n d) = 1 := Iff.rfl

end Langlands.Global.HeckeCharacter

namespace Langlands.Automorphic

open Langlands.Global ContinuousRationalFunctions

variable {F : Type u} [Field F] [NumberField F] (n : ℕ)

local instance smoothMultiplierRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance smoothMultiplierContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance smoothMultiplierSmoothGroup :
    AddCommGroup (SmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance smoothMultiplierFiniteSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _

/-- Local constancy of the scalar factor gives real smoothness on every infinite slice. -/
theorem infiniteSmooth_determinantMultiplier (χ : HeckeCharacter F)
    (hχ : χ.HasFiniteOrder) {f : ContinuousRationalFunctions F n}
    (hf : f ∈ infiniteSmoothSubrepresentation F n) :
    determinantMultiplier n χ f ∈ infiniteSmoothSubrepresentation F n := by
  let : CompleteSpace (ArchimedeanMatrix F n) :=
    inferInstanceAs (CompleteSpace
      (Fin n → Fin n → NumberField.mixedEmbedding.mixedSpace F))
  change f ∈ (⨅ b : FiniteAdelicGL F n,
    (ArchimedeanGL.smoothFunctions F n).comap (infiniteSlice F n b)) at hf
  change determinantMultiplier n χ f ∈ (⨅ b : FiniteAdelicGL F n,
    (ArchimedeanGL.smoothFunctions F n).comap (infiniteSlice F n b))
  simp only [Submodule.mem_iInf, Submodule.mem_comap] at hf ⊢
  intro b
  have hc : IsLocallyConstant (fun x : ArchimedeanGL F n =>
      (χ.adelicDeterminant n
        (AdelicGL.pair F n ((archimedeanGLCoordinates F n).symm x) b) : ℂ)) :=
    (hχ.isLocallyConstant_determinant n).comp_continuous
      ((AdelicGL.continuous_pair F n).comp
        ((archimedeanGLCoordinates F n).symm.continuous.prodMk continuous_const))
  intro x
  let c : ℂ := χ.adelicDeterminant n
    (AdelicGL.pair F n ((archimedeanGLCoordinates F n).symm x) b)
  have hs := (ArchimedeanGL.smoothFunctions F n).smul_mem c (hf b)
  refine ContMDiffAt.congr_of_eventuallyEq (hs x) ?_
  filter_upwards [hc.eventually_eq x] with y hy
  exact congrArg (fun z : ℂ =>
    z * evaluate F n f
      (AdelicGL.pair F n ((archimedeanGLCoordinates F n).symm y) b)) hy

/-- Both factors are locally constant on each actual finite slice. -/
theorem finiteLocallyConstant_determinantMultiplier (χ : HeckeCharacter F)
    (hχ : χ.HasFiniteOrder) {f : ContinuousRationalFunctions F n}
    (hf : f ∈ finiteLocallyConstantSubrepresentation F n) :
    determinantMultiplier n χ f ∈ finiteLocallyConstantSubrepresentation F n := by
  intro a
  exact ((hχ.isLocallyConstant_determinant n).comp_continuous
    ((AdelicGL.continuous_pair F n).comp
      (continuous_const.prodMk continuous_id))).mul (hf a)

/-- Slice-wise smoothness is preserved by every finite-order Hecke multiplier. -/
theorem smooth_determinantMultiplier (χ : HeckeCharacter F)
    (hχ : χ.HasFiniteOrder) {f : ContinuousRationalFunctions F n}
    (hf : f ∈ smoothSubrepresentation F n) :
    determinantMultiplier n χ f ∈ smoothSubrepresentation F n :=
  ⟨infiniteSmooth_determinantMultiplier n χ hχ hf.1,
    finiteLocallyConstant_determinantMultiplier n χ hχ hf.2⟩

/-- Intersect the old common stabilizer with the actual open determinant kernel. -/
theorem finiteSmooth_determinantMultiplier (χ : HeckeCharacter F)
    (hχ : χ.HasFiniteOrder) {f : ContinuousRationalFunctions F n}
    (hf : f ∈ finiteSmoothSubrepresentation F n) :
    determinantMultiplier n χ f ∈ finiteSmoothSubrepresentation F n := by
  obtain ⟨L, hL⟩ := hf
  refine ⟨L ⊓ χ.finiteDeterminantKernel n hχ, ?_⟩
  intro d
  have hd : χ.adelicDeterminant n (AdelicGL.ofFinite F n d.val) = 1 := d.property.2
  change continuousRightAction F n (AdelicGL.ofFinite F n d.val)
    (determinantMultiplier n χ f) = determinantMultiplier n χ f
  rw [determinantMultiplier_rightAction, hd, Units.val_one, one_smul]
  exact congrArg (determinantMultiplier n χ) (hL ⟨d.val, d.property.1⟩)

/-- A compact finite level can be shrunk without losing compactness. -/
theorem hasFiniteLevel_determinantMultiplier (χ : HeckeCharacter F)
    (hχ : χ.HasFiniteOrder) {f : ContinuousRationalFunctions F n}
    (hf : HasFiniteLevel F n f) :
    HasFiniteLevel F n (determinantMultiplier n χ f) := by
  have hs := finiteSmooth_determinantMultiplier n χ hχ
    (hasFiniteLevel_mem_finiteSmooth F n f hf)
  obtain ⟨L, ho, hc, _⟩ := hf
  exact finiteSmooth_hasFiniteLevel F n ⟨L, ho⟩ hc _ hs

/-- Preserve the stronger space with one common open finite stabilizer. -/
theorem finiteSmoothRational_determinantMultiplier (χ : HeckeCharacter F)
    (hχ : χ.HasFiniteOrder) {f : ContinuousRationalFunctions F n}
    (hf : f ∈ finiteSmoothRationalSubrepresentation F n) :
    determinantMultiplier n χ f ∈ finiteSmoothRationalSubrepresentation F n :=
  ⟨infiniteSmooth_determinantMultiplier n χ hχ hf.1,
    finiteSmooth_determinantMultiplier n χ hχ hf.2⟩

private theorem determinantMultiplier_map_of_preserves
    (χ : HeckeCharacter F) (P : Submodule ℂ (ContinuousRationalFunctions F n))
    (hp : ∀ f ∈ P, determinantMultiplier n χ f ∈ P)
    (hi : ∀ f ∈ P, determinantMultiplier n χ⁻¹ f ∈ P) :
    P.map (determinantMultiplier n χ).toLinearMap = P := by
  ext f
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact hp g hg
  · intro hf
    refine ⟨determinantMultiplier n χ⁻¹ f, hi f hf, ?_⟩
    change determinantMul n χ (determinantMul n χ⁻¹ f) = f
    simpa only [inv_inv (G := HeckeCharacter F)] using determinantMul_inv_apply n χ⁻¹ f

namespace SmoothRationalFunctions

/-- The actual multiplier, restricted with its inherited continuous linear structure. -/
def finiteOrderDeterminantMultiplier (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    SmoothRationalFunctions F n ≃L[ℂ] SmoothRationalFunctions F n :=
  (ContinuousRationalFunctions.determinantMultiplier n χ).ofSubmodules _ _
    (determinantMultiplier_map_of_preserves n χ _
      (fun _ hf => smooth_determinantMultiplier n χ hχ hf)
      (fun _ hf => smooth_determinantMultiplier n χ⁻¹ hχ.inv hf))

@[simp]
theorem evaluate_finiteOrderDeterminantMultiplier
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (f : SmoothRationalFunctions F n) (g : AdelicGL F n) :
    evaluate F n (finiteOrderDeterminantMultiplier n χ hχ f).val g =
      (χ.adelicDeterminant n g : ℂ) * evaluate F n f.val g := rfl

@[simp]
theorem evaluate_finiteOrderDeterminantMultiplier_symm
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (f : SmoothRationalFunctions F n) (g : AdelicGL F n) :
    evaluate F n ((finiteOrderDeterminantMultiplier n χ hχ).symm f).val g =
      ((χ.adelicDeterminant n g)⁻¹ : ℂˣ) * evaluate F n f.val g := rfl

theorem finiteOrderDeterminantMultiplier_rightAction
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (g : AdelicGL F n) (f : SmoothRationalFunctions F n) :
    smoothRightAction F n g (finiteOrderDeterminantMultiplier n χ hχ f) =
      (χ.adelicDeterminant n g : ℂ) •
        finiteOrderDeterminantMultiplier n χ hχ (smoothRightAction F n g f) := by
  apply Subtype.ext
  exact ContinuousRationalFunctions.determinantMultiplier_rightAction n χ g f.val

end SmoothRationalFunctions

namespace FiniteSmoothRationalFunctions

/-- Actual multiplication on the smooth space with a common finite stabilizer. -/
def finiteOrderDeterminantMultiplier (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    FiniteSmoothRationalFunctions F n ≃L[ℂ] FiniteSmoothRationalFunctions F n :=
  (ContinuousRationalFunctions.determinantMultiplier n χ).ofSubmodules _ _
    (determinantMultiplier_map_of_preserves n χ _
      (fun _ hf => finiteSmoothRational_determinantMultiplier n χ hχ hf)
      (fun _ hf => finiteSmoothRational_determinantMultiplier n χ⁻¹ hχ.inv hf))

@[simp]
theorem evaluate_finiteOrderDeterminantMultiplier
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (f : FiniteSmoothRationalFunctions F n) (g : AdelicGL F n) :
    evaluate F n (finiteOrderDeterminantMultiplier n χ hχ f).val g =
      (χ.adelicDeterminant n g : ℂ) * evaluate F n f.val g := rfl

@[simp]
theorem evaluate_finiteOrderDeterminantMultiplier_symm
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (f : FiniteSmoothRationalFunctions F n) (g : AdelicGL F n) :
    evaluate F n ((finiteOrderDeterminantMultiplier n χ hχ).symm f).val g =
      ((χ.adelicDeterminant n g)⁻¹ : ℂˣ) * evaluate F n f.val g := rfl

theorem finiteOrderDeterminantMultiplier_rightAction
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (g : AdelicGL F n) (f : FiniteSmoothRationalFunctions F n) :
    finiteSmoothRightAction F n g (finiteOrderDeterminantMultiplier n χ hχ f) =
      (χ.adelicDeterminant n g : ℂ) •
        finiteOrderDeterminantMultiplier n χ hχ (finiteSmoothRightAction F n g f) := by
  apply Subtype.ext
  exact ContinuousRationalFunctions.determinantMultiplier_rightAction n χ g f.val

end FiniteSmoothRationalFunctions
end Langlands.Automorphic
