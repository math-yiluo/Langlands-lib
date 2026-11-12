import Langlands.Automorphic.SmoothDeterminantMultiplier
import Langlands.Global.HeckeDeterminantLocalConstancy
import Langlands.Global.ArchimedeanCharacterSmoothness

/-! # Determinant multiplication by any Hecke character on smooth adelic functions

For every Hecke character `χ`, multiplication by `g ↦ χ(det g)` preserves the slice-wise
smooth functions and the smooth functions with a common open finite stabilizer. On each
infinite slice the factor is smooth (`contMDiff_adelicDeterminant_pair`), on each finite
slice it is locally constant, and its finite kernel is open
(`isOpen_ker_finiteDeterminant`). No finite-order hypothesis is used.
-/

noncomputable section

universe u

open scoped Classical Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.HeckeCharacter

variable {F : Type u} [Field F] [NumberField F] (n : ℕ)

/-- The finite determinant kernel of any Hecke character, an open subgroup. -/
def heckeFiniteDeterminantKernel (χ : HeckeCharacter F) :
    OpenSubgroup (FiniteAdelicGL F n) where
  toSubgroup := ((χ.adelicDeterminant n).toMonoidHom.comp
    (AdelicGL.ofFinite F n).toMonoidHom).ker
  isOpen' := χ.isOpen_ker_finiteDeterminant n

@[simp]
theorem mem_heckeFiniteDeterminantKernel (χ : HeckeCharacter F) (d : FiniteAdelicGL F n) :
    d ∈ χ.heckeFiniteDeterminantKernel n ↔
      χ.adelicDeterminant n (AdelicGL.ofFinite F n d) = 1 := Iff.rfl

/-- On every finite slice, the determinant factor of any Hecke character is locally
constant. -/
theorem isLocallyConstant_adelicDeterminant_pair (χ : HeckeCharacter F)
    (a : InfiniteAdelicGL F n) :
    IsLocallyConstant (fun b : FiniteAdelicGL F n =>
      (χ.adelicDeterminant n (AdelicGL.pair F n a b) : ℂ)) := by
  have h := (χ.isLocallyConstant_finiteDeterminant_val n).comp
    (fun z : ℂ => (χ.adelicDeterminant n (AdelicGL.ofInfinite F n a) : ℂ) * z)
  convert h using 1
  funext b
  simp only [Function.comp_apply, AdelicGL.pair_eq_ofInfinite_mul_ofFinite, map_mul,
    Units.val_mul]

/-- The archimedean determinant factor of a Hecke character, as a homomorphism. -/
def infiniteDeterminantCharacter (χ : HeckeCharacter F) : InfiniteAdelicGL F n →* ℂˣ :=
  (χ.adelicDeterminant n).toMonoidHom.comp (AdelicGL.ofInfinite F n).toMonoidHom

@[simp]
theorem infiniteDeterminantCharacter_apply (χ : HeckeCharacter F) (a : InfiniteAdelicGL F n) :
    χ.infiniteDeterminantCharacter n a = χ.adelicDeterminant n (AdelicGL.ofInfinite F n a) :=
  rfl

/-- The archimedean determinant factor is a smooth function. -/
theorem infiniteDeterminantCharacter_mem_smoothFunctions (χ : HeckeCharacter F) :
    (fun a => (χ.infiniteDeterminantCharacter n a : ℂ)) ∈
      ArchimedeanGL.smoothFunctions F n :=
  χ.contMDiff_adelicDeterminant_ofInfinite n

/-- The determinant factor on a slice is the finite value times the archimedean factor. -/
theorem adelicDeterminant_pair_val (χ : HeckeCharacter F) (a : InfiniteAdelicGL F n)
    (b : FiniteAdelicGL F n) :
    (χ.adelicDeterminant n (AdelicGL.pair F n a b) : ℂ) =
      (χ.adelicDeterminant n (AdelicGL.ofFinite F n b) : ℂ) *
        (χ.infiniteDeterminantCharacter n a : ℂ) := by
  rw [AdelicGL.pair_eq_ofInfinite_mul_ofFinite, map_mul, Units.val_mul, mul_comm]
  rfl

end Langlands.Global.HeckeCharacter

namespace Langlands.Automorphic

open Langlands.Global ContinuousRationalFunctions

variable {F : Type u} [Field F] [NumberField F] (n : ℕ)

local instance heckeSmoothMultiplierRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance heckeSmoothMultiplierContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance heckeSmoothMultiplierSmoothGroup :
    AddCommGroup (SmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance heckeSmoothMultiplierFiniteSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _

/-- Smoothness of the factor on every infinite slice preserves slice-wise smoothness. -/
theorem infiniteSmooth_heckeDeterminantMultiplier (χ : HeckeCharacter F)
    {f : ContinuousRationalFunctions F n}
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
  intro b x
  have hc := χ.contMDiff_adelicDeterminant_pair n b x
  exact contDiff_mul.contDiffAt.comp_contMDiffAt (hc.prodMk_space (hf b x))

/-- Both factors are locally constant on each finite slice. -/
theorem finiteLocallyConstant_heckeDeterminantMultiplier (χ : HeckeCharacter F)
    {f : ContinuousRationalFunctions F n}
    (hf : f ∈ finiteLocallyConstantSubrepresentation F n) :
    determinantMultiplier n χ f ∈ finiteLocallyConstantSubrepresentation F n := by
  intro a
  exact (χ.isLocallyConstant_adelicDeterminant_pair n a).mul (hf a)

/-- Slice-wise smoothness is preserved by every Hecke multiplier. -/
theorem smooth_heckeDeterminantMultiplier (χ : HeckeCharacter F)
    {f : ContinuousRationalFunctions F n}
    (hf : f ∈ smoothSubrepresentation F n) :
    determinantMultiplier n χ f ∈ smoothSubrepresentation F n :=
  ⟨infiniteSmooth_heckeDeterminantMultiplier n χ hf.1,
    finiteLocallyConstant_heckeDeterminantMultiplier n χ hf.2⟩

/-- Intersect a common stabilizer with the open finite determinant kernel. -/
theorem finiteSmooth_heckeDeterminantMultiplier (χ : HeckeCharacter F)
    {f : ContinuousRationalFunctions F n}
    (hf : f ∈ finiteSmoothSubrepresentation F n) :
    determinantMultiplier n χ f ∈ finiteSmoothSubrepresentation F n := by
  obtain ⟨L, hL⟩ := hf
  refine ⟨L ⊓ χ.heckeFiniteDeterminantKernel n, ?_⟩
  intro d
  have hd : χ.adelicDeterminant n (AdelicGL.ofFinite F n d.val) = 1 := d.property.2
  change continuousRightAction F n (AdelicGL.ofFinite F n d.val)
    (determinantMultiplier n χ f) = determinantMultiplier n χ f
  rw [determinantMultiplier_rightAction, hd, Units.val_one, one_smul]
  exact congrArg (determinantMultiplier n χ) (hL ⟨d.val, d.property.1⟩)

/-- A compact finite level is kept by every Hecke multiplier. -/
theorem hasFiniteLevel_heckeDeterminantMultiplier (χ : HeckeCharacter F)
    {f : ContinuousRationalFunctions F n} (hf : HasFiniteLevel F n f) :
    HasFiniteLevel F n (determinantMultiplier n χ f) := by
  have hs := finiteSmooth_heckeDeterminantMultiplier n χ
    (hasFiniteLevel_mem_finiteSmooth F n f hf)
  obtain ⟨L, ho, hc, _⟩ := hf
  exact finiteSmooth_hasFiniteLevel F n ⟨L, ho⟩ hc _ hs

/-- The smooth space with one common open finite stabilizer is preserved. -/
theorem finiteSmoothRational_heckeDeterminantMultiplier (χ : HeckeCharacter F)
    {f : ContinuousRationalFunctions F n}
    (hf : f ∈ finiteSmoothRationalSubrepresentation F n) :
    determinantMultiplier n χ f ∈ finiteSmoothRationalSubrepresentation F n :=
  ⟨infiniteSmooth_heckeDeterminantMultiplier n χ hf.1,
    finiteSmooth_heckeDeterminantMultiplier n χ hf.2⟩

/-- A submodule preserved by the multipliers of `χ` and `χ⁻¹` is its own image. -/
theorem determinantMultiplier_map_eq_of_preserves
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

/-- Multiplication by `χ ∘ det` on slice-wise smooth functions, for any Hecke character. -/
def heckeDeterminantMultiplier (χ : HeckeCharacter F) :
    SmoothRationalFunctions F n ≃L[ℂ] SmoothRationalFunctions F n :=
  (ContinuousRationalFunctions.determinantMultiplier n χ).ofSubmodules _ _
    (determinantMultiplier_map_eq_of_preserves n χ _
      (fun _ hf => smooth_heckeDeterminantMultiplier n χ hf)
      (fun _ hf => smooth_heckeDeterminantMultiplier n χ⁻¹ hf))

@[simp]
theorem evaluate_heckeDeterminantMultiplier (χ : HeckeCharacter F)
    (f : SmoothRationalFunctions F n) (g : AdelicGL F n) :
    evaluate F n (heckeDeterminantMultiplier n χ f).val g =
      (χ.adelicDeterminant n g : ℂ) * evaluate F n f.val g := rfl

@[simp]
theorem evaluate_heckeDeterminantMultiplier_symm (χ : HeckeCharacter F)
    (f : SmoothRationalFunctions F n) (g : AdelicGL F n) :
    evaluate F n ((heckeDeterminantMultiplier n χ).symm f).val g =
      ((χ.adelicDeterminant n g)⁻¹ : ℂˣ) * evaluate F n f.val g := rfl

theorem heckeDeterminantMultiplier_rightAction (χ : HeckeCharacter F)
    (g : AdelicGL F n) (f : SmoothRationalFunctions F n) :
    smoothRightAction F n g (heckeDeterminantMultiplier n χ f) =
      (χ.adelicDeterminant n g : ℂ) •
        heckeDeterminantMultiplier n χ (smoothRightAction F n g f) := by
  apply Subtype.ext
  exact ContinuousRationalFunctions.determinantMultiplier_rightAction n χ g f.val

end SmoothRationalFunctions

namespace FiniteSmoothRationalFunctions

/-- Multiplication by `χ ∘ det` on smooth functions with a common finite stabilizer, for any
Hecke character. -/
def heckeDeterminantMultiplier (χ : HeckeCharacter F) :
    FiniteSmoothRationalFunctions F n ≃L[ℂ] FiniteSmoothRationalFunctions F n :=
  (ContinuousRationalFunctions.determinantMultiplier n χ).ofSubmodules _ _
    (determinantMultiplier_map_eq_of_preserves n χ _
      (fun _ hf => finiteSmoothRational_heckeDeterminantMultiplier n χ hf)
      (fun _ hf => finiteSmoothRational_heckeDeterminantMultiplier n χ⁻¹ hf))

@[simp]
theorem evaluate_heckeDeterminantMultiplier (χ : HeckeCharacter F)
    (f : FiniteSmoothRationalFunctions F n) (g : AdelicGL F n) :
    evaluate F n (heckeDeterminantMultiplier n χ f).val g =
      (χ.adelicDeterminant n g : ℂ) * evaluate F n f.val g := rfl

@[simp]
theorem evaluate_heckeDeterminantMultiplier_symm (χ : HeckeCharacter F)
    (f : FiniteSmoothRationalFunctions F n) (g : AdelicGL F n) :
    evaluate F n ((heckeDeterminantMultiplier n χ).symm f).val g =
      ((χ.adelicDeterminant n g)⁻¹ : ℂˣ) * evaluate F n f.val g := rfl

theorem heckeDeterminantMultiplier_rightAction (χ : HeckeCharacter F)
    (g : AdelicGL F n) (f : FiniteSmoothRationalFunctions F n) :
    finiteSmoothRightAction F n g (heckeDeterminantMultiplier n χ f) =
      (χ.adelicDeterminant n g : ℂ) •
        heckeDeterminantMultiplier n χ (finiteSmoothRightAction F n g f) := by
  apply Subtype.ext
  exact ContinuousRationalFunctions.determinantMultiplier_rightAction n χ g f.val

end FiniteSmoothRationalFunctions
end Langlands.Automorphic
