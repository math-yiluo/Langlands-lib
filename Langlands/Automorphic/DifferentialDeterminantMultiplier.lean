import Langlands.Automorphic.SmoothDeterminantMultiplier
import Langlands.Automorphic.FiniteDifferential
import Langlands.Global.ArchimedeanLocallyConstantMultiplier

/-! # Determinant multiplication and genuine adelic differential operators -/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global ContinuousRationalFunctions

variable {F : Type u} [Field F] [NumberField F] (n : ℕ)

local instance differentialMultiplierRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance differentialMultiplierContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance differentialMultiplierFiniteSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance differentialMultiplierCenterFiniteGroup :
    AddCommGroup (CenterFiniteFiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _

/-- The actual determinant-character scalar on one infinite slice. -/
def determinantSliceScalar (χ : HeckeCharacter F) (b : FiniteAdelicGL F n)
    (a : InfiniteAdelicGL F n) : ℂ :=
  χ.adelicDeterminant n (AdelicGL.pair F n a b)

theorem isLocallyConstant_determinantSliceScalar (χ : HeckeCharacter F)
    (hχ : χ.HasFiniteOrder) (b : FiniteAdelicGL F n) :
    IsLocallyConstant (determinantSliceScalar n χ b) :=
  (hχ.isLocallyConstant_determinant n).comp_continuous
    ((AdelicGL.continuous_pair F n).comp (continuous_id.prodMk continuous_const))

/-- The actual adelic multiplier restricts to the generic archimedean scalar multiplier. -/
theorem finiteSmoothSlice_determinantMultiplier (χ : HeckeCharacter F)
    (hχ : χ.HasFiniteOrder) (b : FiniteAdelicGL F n)
    (f : FiniteSmoothRationalFunctions F n) :
    finiteSmoothSlice F n b
        (FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n χ hχ f) =
      ArchimedeanGL.locallyConstantMultiplier F n (determinantSliceScalar n χ b)
        (isLocallyConstant_determinantSliceScalar n χ hχ b) (finiteSmoothSlice F n b f) := by
  apply Subtype.ext
  funext a
  rfl

/-- Finite-order determinant multiplication commutes with every actual adelic differential. -/
theorem finiteSmoothEnvelopingAction_determinantMultiplier
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (a : ArchimedeanGL.EnvelopingAlgebra F n)
    (f : FiniteSmoothRationalFunctions F n) :
    finiteSmoothEnvelopingAction F n a
        (FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n χ hχ f) =
      FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n χ hχ
        (finiteSmoothEnvelopingAction F n a f) := by
  apply finiteSmoothSlice_injective F n
  funext b
  simp only [finiteSmoothSlice_envelopingAction, finiteSmoothSlice_determinantMultiplier,
    ArchimedeanGL.envelopingAction_locallyConstantMultiplier_apply]

theorem finiteSmoothCenterAction_determinantMultiplier
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (z : ArchimedeanGL.EnvelopingCenter F n)
    (f : FiniteSmoothRationalFunctions F n) :
    finiteSmoothCenterAction F n z
        (FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n χ hχ f) =
      FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n χ hχ
        (finiteSmoothCenterAction F n z f) :=
  finiteSmoothEnvelopingAction_determinantMultiplier n χ hχ
    (ArchimedeanGL.centerInclusion F n z) f

/-- Actual determinant multiplication intertwines the common center representation. -/
def finiteSmoothDeterminantCenterIntertwiner
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    (finiteSmoothCenterRepresentation F n).IntertwiningMap
      (finiteSmoothCenterRepresentation F n) where
  toLinearMap :=
    (FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n χ hχ).toLinearMap
  isIntertwining' z := by
    apply LinearMap.ext
    intro f
    exact (finiteSmoothCenterAction_determinantMultiplier n χ hχ z f).symm

theorem isCenterFinite_determinantMultiplier
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    {f : FiniteSmoothRationalFunctions F n}
    (hf : IsCenterFinite F n (finiteSmoothInclusion F n f)) :
    IsCenterFinite F n (finiteSmoothInclusion F n
      (FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n χ hχ f)) := by
  apply (isCenterFinite_iff_finiteSmoothCenterVector F n _).mpr
  exact ((isCenterFinite_iff_finiteSmoothCenterVector F n f).mp hf).map
    (finiteSmoothDeterminantCenterIntertwiner n χ hχ)

private theorem mem_centerFamilyAnnihilator_iff_action_eq_zero
    (f : FiniteSmoothRationalFunctions F n) (z : ArchimedeanGL.EnvelopingCenter F n) :
    z ∈ centerFamilyAnnihilator F n (finiteSmoothCenterSlices F n f) ↔
      finiteSmoothCenterAction F n z f = 0 := by
  constructor
  · intro hz
    apply finiteSmoothCenterSlices_injective F n
    funext b
    rw [finiteSmoothCenterSlices_apply, finiteSmoothSlice_centerAction]
    exact (mem_centerFamilyAnnihilator F n _ z).mp hz b
  · intro hz
    apply (mem_centerFamilyAnnihilator F n _ z).mpr
    intro b
    change ArchimedeanGL.centerAction F n z (finiteSmoothSlice F n b f) = 0
    rw [← finiteSmoothSlice_centerAction, hz, map_zero]

/-- Multiplication preserves exactly the single ideal annihilating all infinite slices. -/
theorem centerFamilyAnnihilator_determinantMultiplier
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (f : FiniteSmoothRationalFunctions F n) :
    centerFamilyAnnihilator F n (finiteSmoothCenterSlices F n
        (FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n χ hχ f)) =
      centerFamilyAnnihilator F n (finiteSmoothCenterSlices F n f) := by
  ext z
  rw [mem_centerFamilyAnnihilator_iff_action_eq_zero,
    mem_centerFamilyAnnihilator_iff_action_eq_zero,
    finiteSmoothCenterAction_determinantMultiplier]
  exact (FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n χ hχ).map_eq_zero_iff

private theorem centerFinite_map_determinantMultiplier
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    (centerFiniteFiniteSmoothFunctions F n).map
        (FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n χ hχ).toLinearMap =
      centerFiniteFiniteSmoothFunctions F n := by
  ext f
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact isCenterFinite_determinantMultiplier n χ hχ hg
  · intro hf
    let g := FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n χ⁻¹ hχ.inv f
    refine ⟨g, isCenterFinite_determinantMultiplier n χ⁻¹ hχ.inv hf, ?_⟩
    apply Subtype.ext
    change determinantMul n χ (determinantMul n χ⁻¹ f.val) = f.val
    simpa only [inv_inv (G := HeckeCharacter F)] using determinantMul_inv_apply n χ⁻¹ f.val

namespace CenterFiniteFiniteSmoothRationalFunctions

/-- Restrict the actual continuous linear multiplier to simultaneous center-finite functions. -/
def finiteOrderDeterminantMultiplier (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    CenterFiniteFiniteSmoothRationalFunctions F n ≃L[ℂ]
      CenterFiniteFiniteSmoothRationalFunctions F n :=
  (FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n χ hχ).ofSubmodules _ _
    (centerFinite_map_determinantMultiplier n χ hχ)

@[simp]
theorem finiteOrderDeterminantMultiplier_val (χ : HeckeCharacter F)
    (hχ : χ.HasFiniteOrder) (f : CenterFiniteFiniteSmoothRationalFunctions F n) :
    (finiteOrderDeterminantMultiplier n χ hχ f).val =
      FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n χ hχ f.val := rfl

theorem envelopingAction_determinantMultiplier
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (a : ArchimedeanGL.EnvelopingAlgebra F n)
    (f : CenterFiniteFiniteSmoothRationalFunctions F n) :
    centerFiniteEnvelopingAction F n a (finiteOrderDeterminantMultiplier n χ hχ f) =
      finiteOrderDeterminantMultiplier n χ hχ (centerFiniteEnvelopingAction F n a f) := by
  apply Subtype.ext
  exact finiteSmoothEnvelopingAction_determinantMultiplier n χ hχ a f.val

theorem finiteRightAction_determinantMultiplier
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (d : FiniteAdelicGL F n) (f : CenterFiniteFiniteSmoothRationalFunctions F n) :
    centerFiniteFiniteSmoothRightAction F n d (finiteOrderDeterminantMultiplier n χ hχ f) =
      (χ.adelicDeterminant n (AdelicGL.ofFinite F n d) : ℂ) •
        finiteOrderDeterminantMultiplier n χ hχ
          (centerFiniteFiniteSmoothRightAction F n d f) := by
  apply Subtype.ext
  exact FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier_rightAction n χ hχ
    (AdelicGL.ofFinite F n d) f.val

@[simp]
theorem evaluate_finiteOrderDeterminantMultiplier
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (f : CenterFiniteFiniteSmoothRationalFunctions F n) (g : AdelicGL F n) :
    evaluate F n (finiteOrderDeterminantMultiplier n χ hχ f).val.val g =
      (χ.adelicDeterminant n g : ℂ) * evaluate F n f.val.val g := rfl

@[simp]
theorem evaluate_finiteOrderDeterminantMultiplier_symm
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (f : CenterFiniteFiniteSmoothRationalFunctions F n) (g : AdelicGL F n) :
    evaluate F n ((finiteOrderDeterminantMultiplier n χ hχ).symm f).val.val g =
      ((χ.adelicDeterminant n g)⁻¹ : ℂˣ) * evaluate F n f.val.val g := rfl

end CenterFiniteFiniteSmoothRationalFunctions
end Langlands.Automorphic
