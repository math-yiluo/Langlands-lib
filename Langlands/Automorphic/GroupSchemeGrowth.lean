import Langlands.Global.RepresentationGrowth
import Langlands.Automorphic.GroupSchemePlotSmooth
import Langlands.Automorphic.Growth

/-! # Polynomial growth on actual adelic rational-function slices -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped Classical CategoryTheory.MonObj

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global

set_option backward.isDefEq.respectTransparency false

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  {N : ℕ} (rho : GroupScheme.MatrixRepresentation G (Fin N))

/-- Each fixed finite slice has a polynomial bound for the specified algebraic representation. -/
def HasPolynomialGrowth (f : ContinuousRationalFunctions F G) : Prop :=
  ∀ b : FiniteAdelicGroupPoints F G,
    RepresentationGrowth.HasPolynomialGrowth F G rho (infiniteSlice F G b f)

/-- The actual slice-growth subspace is stable under full positive adelic translation. -/
def polynomialGrowthSubrepresentation : Subrepresentation (continuousRightAction F G) where
  toSubmodule := ⨅ b : FiniteAdelicGroupPoints F G,
    (RepresentationGrowth.polynomialGrowthFunctions F G rho).comap (infiniteSlice F G b)
  apply_mem_toSubmodule g f hf := by
    simp only [Submodule.mem_iInf, Submodule.mem_comap,
      RepresentationGrowth.mem_polynomialGrowthFunctions] at hf ⊢
    intro b
    have h := (hf (b * AdelicGroupPoints.finite F G g)).rightTranslate
      (AdelicGroupPoints.infinite F G g)
    change RepresentationGrowth.HasPolynomialGrowth F G rho
      (fun a => evaluate F G f (AdelicGroupPoints.pair F G
        (a * AdelicGroupPoints.infinite F G g) (b * AdelicGroupPoints.finite F G g))) at h
    change RepresentationGrowth.HasPolynomialGrowth F G rho
      (fun a => evaluate F G f (AdelicGroupPoints.pair F G a b * g))
    simpa only [AdelicGroupPoints.pair_mul_right] using h

@[simp] theorem mem_polynomialGrowthSubrepresentation (f : ContinuousRationalFunctions F G) :
    f ∈ polynomialGrowthSubrepresentation F G rho ↔ HasPolynomialGrowth F G rho f := by
  change f ∈ (⨅ b : FiniteAdelicGroupPoints F G,
    (RepresentationGrowth.polynomialGrowthFunctions F G rho).comap (infiniteSlice F G b) :
      Submodule ℂ _) ↔ _
  simp only [Submodule.mem_iInf, Submodule.mem_comap,
    RepresentationGrowth.mem_polynomialGrowthFunctions, HasPolynomialGrowth]

abbrev PolynomialGrowthRationalFunctions :=
  (polynomialGrowthSubrepresentation F G rho).toSubmodule

def polynomialGrowthRightAction :
    Representation ℂ (AdelicGroupPoints F G) (PolynomialGrowthRationalFunctions F G rho) :=
  (polynomialGrowthSubrepresentation F G rho).toRepresentation

/-- The growth space retains its injective, equivariant continuous function realization. -/
def polynomialGrowthInclusion :
    (polynomialGrowthRightAction F G rho).IntertwiningMap (continuousRightAction F G) where
  toLinearMap := (polynomialGrowthSubrepresentation F G rho).toSubmodule.subtype
  isIntertwining' _ := by ext; rfl

theorem polynomialGrowthInclusion_injective :
    Function.Injective (polynomialGrowthInclusion F G rho) := Subtype.val_injective

@[simp] theorem evaluate_polynomialGrowthRightAction (g x : AdelicGroupPoints F G)
    (f : PolynomialGrowthRationalFunctions F G rho) :
    evaluate F G (polynomialGrowthRightAction F G rho g f).val x =
      evaluate F G f.val (x * g) := rfl

/-- Infinite plot smoothness, finite-slice local constancy and slice-wise polynomial growth. -/
def plotSmoothPolynomialGrowthSubrepresentation :
    Subrepresentation (continuousRightAction F G) :=
  plotSmoothSubrepresentation F G ⊓ polynomialGrowthSubrepresentation F G rho

/-- Infinite plot smoothness, a common open finite stabilizer and slice-wise polynomial growth. -/
def finitePlotSmoothPolynomialGrowthSubrepresentation :
    Subrepresentation (continuousRightAction F G) :=
  finitePlotSmoothRationalSubrepresentation F G ⊓ polynomialGrowthSubrepresentation F G rho

theorem finitePlotSmoothPolynomialGrowth_le_plotSmoothPolynomialGrowth :
    finitePlotSmoothPolynomialGrowthSubrepresentation F G rho ≤
      plotSmoothPolynomialGrowthSubrepresentation F G rho :=
  inf_le_inf_right _ (finitePlotSmoothRational_le_plotSmooth F G)

section GeneralLinearComparison

variable (n : ℕ)

local notation "GLG" =>
  (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F))
local notation "std" => (GroupScheme.MatrixRepresentation.standard (Fin n) (CommRingCat.of F))

local instance growthGeneralLinearIsAffine : IsAffine (GLG).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

/-- The original matrix slice-growth predicate corresponds exactly to the actual one. -/
theorem continuousGeneralLinearEquiv_mem_polynomialGrowth
    (f : ContinuousRationalFunctions F GLG) :
    continuousGeneralLinearEquiv F n f ∈
        Langlands.Automorphic.polynomialGrowthSubrepresentation F n ↔
      f ∈ polynomialGrowthSubrepresentation F GLG std := by
  rw [mem_polynomialGrowthSubrepresentation,
    Langlands.Automorphic.mem_polynomialGrowthSubrepresentation]
  change (∀ b : FiniteAdelicGL F n,
    ArchimedeanGL.HasPolynomialGrowth F n
      (Langlands.Automorphic.infiniteSlice F n b (continuousGeneralLinearEquiv F n f))) ↔
    ∀ b : FiniteAdelicGroupPoints F GLG,
      RepresentationGrowth.HasPolynomialGrowth F GLG std (infiniteSlice F GLG b f)
  constructor
  · intro hf b
    apply (RepresentationGrowth.hasPolynomialGrowth_standard_iff F n _).mpr
    rw [← infiniteSlice_continuousGeneralLinearEquiv]
    exact hf _
  · intro hf b
    obtain ⟨b, rfl⟩ := (GeneralLinearGroupPoints.finiteHomeomorph F n).surjective b
    rw [infiniteSlice_continuousGeneralLinearEquiv]
    exact (RepresentationGrowth.hasPolynomialGrowth_standard_iff F n _).mp (hf b)

/-- Restrict the original ambient equivalence to the corresponding slice-growth spaces. -/
def polynomialGrowthGeneralLinearEquiv :
    PolynomialGrowthRationalFunctions F GLG std ≃ₗ[ℂ]
      Langlands.Automorphic.PolynomialGrowthRationalFunctions F n where
  toFun f := ⟨continuousGeneralLinearEquiv F n f.val,
    (continuousGeneralLinearEquiv_mem_polynomialGrowth F n f.val).mpr f.property⟩
  invFun f := ⟨(continuousGeneralLinearEquiv F n).symm f.val, by
    apply (continuousGeneralLinearEquiv_mem_polynomialGrowth F n _).mp
    rw [LinearEquiv.apply_symm_apply]
    exact f.property⟩
  left_inv f := Subtype.ext ((continuousGeneralLinearEquiv F n).symm_apply_apply f.val)
  right_inv f := Subtype.ext ((continuousGeneralLinearEquiv F n).apply_symm_apply f.val)
  map_add' _ _ := Subtype.ext (map_add (continuousGeneralLinearEquiv F n) _ _)
  map_smul' _ _ := Subtype.ext (map_smul (continuousGeneralLinearEquiv F n) _ _)

@[simp] theorem polynomialGrowthGeneralLinearEquiv_val
    (f : PolynomialGrowthRationalFunctions F GLG std) :
    (polynomialGrowthGeneralLinearEquiv F n f).val = continuousGeneralLinearEquiv F n f.val := rfl

/-- Both restricted full adelic actions retain the exact original positive convention. -/
theorem polynomialGrowthGeneralLinearEquiv_rightAction
    (f : PolynomialGrowthRationalFunctions F GLG std) (g : AdelicGroupPoints F GLG) :
    polynomialGrowthGeneralLinearEquiv F n (polynomialGrowthRightAction F GLG std g f) =
      Langlands.Automorphic.polynomialGrowthRightAction F n
        (GeneralLinearGroupPoints.adelicHomeomorph F n g)
        (polynomialGrowthGeneralLinearEquiv F n f) := by
  apply Subtype.ext
  exact continuousGeneralLinearEquiv_rightAction F n f.val g

/-- The growth comparison commutes with the existing faithful ambient inclusions. -/
theorem polynomialGrowthGeneralLinearEquiv_inclusion
    (f : PolynomialGrowthRationalFunctions F GLG std) :
    Langlands.Automorphic.polynomialGrowthInclusion F n
        (polynomialGrowthGeneralLinearEquiv F n f) =
      continuousGeneralLinearEquiv F n (polynomialGrowthInclusion F GLG std f) := rfl

/-- Adding the existing smooth conditions corresponds exactly to the original intersection. -/
theorem continuousGeneralLinearEquiv_mem_plotSmoothPolynomialGrowth
    (f : ContinuousRationalFunctions F GLG) :
    continuousGeneralLinearEquiv F n f ∈
        Langlands.Automorphic.smoothPolynomialGrowthSubrepresentation F n ↔
      f ∈ plotSmoothPolynomialGrowthSubrepresentation F GLG std := by
  change (continuousGeneralLinearEquiv F n f ∈ Langlands.Automorphic.smoothSubrepresentation F n ∧
    continuousGeneralLinearEquiv F n f ∈
      Langlands.Automorphic.polynomialGrowthSubrepresentation F n) ↔
    (f ∈ plotSmoothSubrepresentation F GLG ∧
      f ∈ polynomialGrowthSubrepresentation F GLG std)
  rw [continuousGeneralLinearEquiv_mem_plotSmooth, continuousGeneralLinearEquiv_mem_polynomialGrowth]

/-- A common finite stabilizer is preserved together with smoothness and polynomial growth. -/
theorem continuousGeneralLinearEquiv_mem_finitePlotSmoothPolynomialGrowth
    (f : ContinuousRationalFunctions F GLG) :
    continuousGeneralLinearEquiv F n f ∈
        Langlands.Automorphic.finiteSmoothPolynomialGrowthSubrepresentation F n ↔
      f ∈ finitePlotSmoothPolynomialGrowthSubrepresentation F GLG std := by
  change (continuousGeneralLinearEquiv F n f ∈
      Langlands.Automorphic.finiteSmoothRationalSubrepresentation F n ∧
    continuousGeneralLinearEquiv F n f ∈
      Langlands.Automorphic.polynomialGrowthSubrepresentation F n) ↔
    (f ∈ finitePlotSmoothRationalSubrepresentation F GLG ∧
      f ∈ polynomialGrowthSubrepresentation F GLG std)
  rw [continuousGeneralLinearEquiv_mem_finitePlotSmooth,
    continuousGeneralLinearEquiv_mem_polynomialGrowth]

/-- The original smooth polynomial-growth intersection is realized on actual group-scheme points. -/
def plotSmoothPolynomialGrowthGeneralLinearEquiv :
    ↥(plotSmoothPolynomialGrowthSubrepresentation F GLG std).toSubmodule ≃ₗ[ℂ]
      ↥(Langlands.Automorphic.smoothPolynomialGrowthSubrepresentation F n).toSubmodule where
  toFun f := ⟨continuousGeneralLinearEquiv F n f.val,
    (continuousGeneralLinearEquiv_mem_plotSmoothPolynomialGrowth F n f.val).mpr f.property⟩
  invFun f := ⟨(continuousGeneralLinearEquiv F n).symm f.val, by
    apply (continuousGeneralLinearEquiv_mem_plotSmoothPolynomialGrowth F n _).mp
    rw [LinearEquiv.apply_symm_apply]
    exact f.property⟩
  left_inv f := Subtype.ext ((continuousGeneralLinearEquiv F n).symm_apply_apply f.val)
  right_inv f := Subtype.ext ((continuousGeneralLinearEquiv F n).apply_symm_apply f.val)
  map_add' _ _ := Subtype.ext (map_add (continuousGeneralLinearEquiv F n) _ _)
  map_smul' _ _ := Subtype.ext (map_smul (continuousGeneralLinearEquiv F n) _ _)

/-- The same actual comparison recovers the original common-stabilizer growth intersection. -/
def finitePlotSmoothPolynomialGrowthGeneralLinearEquiv :
    ↥(finitePlotSmoothPolynomialGrowthSubrepresentation F GLG std).toSubmodule ≃ₗ[ℂ]
      ↥(Langlands.Automorphic.finiteSmoothPolynomialGrowthSubrepresentation F n).toSubmodule where
  toFun f := ⟨continuousGeneralLinearEquiv F n f.val,
    (continuousGeneralLinearEquiv_mem_finitePlotSmoothPolynomialGrowth F n f.val).mpr f.property⟩
  invFun f := ⟨(continuousGeneralLinearEquiv F n).symm f.val, by
    apply (continuousGeneralLinearEquiv_mem_finitePlotSmoothPolynomialGrowth F n _).mp
    rw [LinearEquiv.apply_symm_apply]
    exact f.property⟩
  left_inv f := Subtype.ext ((continuousGeneralLinearEquiv F n).symm_apply_apply f.val)
  right_inv f := Subtype.ext ((continuousGeneralLinearEquiv F n).apply_symm_apply f.val)
  map_add' _ _ := Subtype.ext (map_add (continuousGeneralLinearEquiv F n) _ _)
  map_smul' _ _ := Subtype.ext (map_smul (continuousGeneralLinearEquiv F n) _ _)

/-- The smooth-growth equivalence intertwines the restricted positive right representations. -/
theorem plotSmoothPolynomialGrowthGeneralLinearEquiv_rightAction
    (f : ↥(plotSmoothPolynomialGrowthSubrepresentation F GLG std).toSubmodule)
    (g : AdelicGroupPoints F GLG) :
    plotSmoothPolynomialGrowthGeneralLinearEquiv F n
        ((plotSmoothPolynomialGrowthSubrepresentation F GLG std).toRepresentation g f) =
      (Langlands.Automorphic.smoothPolynomialGrowthSubrepresentation F n).toRepresentation
        (GeneralLinearGroupPoints.adelicHomeomorph F n g)
        (plotSmoothPolynomialGrowthGeneralLinearEquiv F n f) := by
  apply Subtype.ext
  exact continuousGeneralLinearEquiv_rightAction F n f.val g

/-- The common-stabilizer growth equivalence also intertwines the restricted actions. -/
theorem finitePlotSmoothPolynomialGrowthGeneralLinearEquiv_rightAction
    (f : ↥(finitePlotSmoothPolynomialGrowthSubrepresentation F GLG std).toSubmodule)
    (g : AdelicGroupPoints F GLG) :
    finitePlotSmoothPolynomialGrowthGeneralLinearEquiv F n
        ((finitePlotSmoothPolynomialGrowthSubrepresentation F GLG std).toRepresentation g f) =
      (Langlands.Automorphic.finiteSmoothPolynomialGrowthSubrepresentation F n).toRepresentation
        (GeneralLinearGroupPoints.adelicHomeomorph F n g)
        (finitePlotSmoothPolynomialGrowthGeneralLinearEquiv F n f) := by
  apply Subtype.ext
  exact continuousGeneralLinearEquiv_rightAction F n f.val g

end GeneralLinearComparison

end Langlands.Automorphic.GroupSchemeFunctions
