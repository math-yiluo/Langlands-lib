import Langlands.Automorphic.GroupSchemeFiniteLevel
import Langlands.GroupScheme.GeneralLinearSmoothFunctions

/-! # Plot-smooth infinite slices on actual adelic points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped Classical CategoryTheory.MonObj

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global

set_option backward.isDefEq.respectTransparency false

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]

/-- Restriction to the actual infinite factor at a fixed finite point. -/
def infiniteSlice (b : FiniteAdelicGroupPoints F G) :
    ContinuousRationalFunctions F G →ₗ[ℂ] (InfiniteAdelicGroupPoints F G → ℂ) where
  toFun f a := evaluate F G f (AdelicGroupPoints.pair F G a b)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Infinite slices tested on all coordinate-smooth real families in mixed coordinates. -/
def infinitePlotSmoothSubrepresentation : Subrepresentation (continuousRightAction F G) where
  toSubmodule := ⨅ b : FiniteAdelicGroupPoints F G,
    (G.plotSmoothFunctions (CommAlgCat.of F (InfiniteAdeleRing F))
      (B := mixedEmbedding.mixedSpace F)
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom).comap (infiniteSlice F G b)
  apply_mem_toSubmodule g f hf := by
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hf ⊢
    intro b
    let s : ↥(G.plotSmoothFunctions (CommAlgCat.of F (InfiniteAdeleRing F))
        (B := mixedEmbedding.mixedSpace F)
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom) :=
      ⟨infiniteSlice F G (b * AdelicGroupPoints.finite F G g) f, hf _⟩
    have h := (G.plotSmoothRightAction (CommAlgCat.of F (InfiniteAdeleRing F))
      (B := mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom
      (AdelicGroupPoints.infinite F G g) s).property
    change (fun a => evaluate F G f (AdelicGroupPoints.pair F G
      (a * AdelicGroupPoints.infinite F G g) (b * AdelicGroupPoints.finite F G g))) ∈
      G.plotSmoothFunctions (CommAlgCat.of F (InfiniteAdeleRing F))
        (B := mixedEmbedding.mixedSpace F)
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom at h
    change (fun a => evaluate F G f (AdelicGroupPoints.pair F G a b * g)) ∈ _
    simpa only [AdelicGroupPoints.pair_mul_right] using h

/-- The infinite condition is exactly the defining plot test on every finite slice. -/
theorem mem_infinitePlotSmoothSubrepresentation (f : ContinuousRationalFunctions F G) :
    f ∈ infinitePlotSmoothSubrepresentation F G ↔
      ∀ b : FiniteAdelicGroupPoints F G,
        G.IsPlotSmooth (CommAlgCat.of F (InfiniteAdeleRing F))
          (B := mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom (infiniteSlice F G b f) := by
  change f ∈ (⨅ b : FiniteAdelicGroupPoints F G,
    (G.plotSmoothFunctions (CommAlgCat.of F (InfiniteAdeleRing F))
      (B := mixedEmbedding.mixedSpace F)
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom).comap (infiniteSlice F G b)) ↔ _
  simp only [Submodule.mem_iInf, Submodule.mem_comap]
  rfl

/-- Continuous rational-invariant functions with infinite plot tests and finite-slice local constancy. -/
def plotSmoothSubrepresentation : Subrepresentation (continuousRightAction F G) :=
  infinitePlotSmoothSubrepresentation F G ⊓ finiteLocallyConstantSubrepresentation F G

abbrev PlotSmoothRationalFunctions := (plotSmoothSubrepresentation F G).toSubmodule

/-- Full positive right translation restricts to the slice-regular space. -/
def plotSmoothRightAction :
    Representation ℂ (AdelicGroupPoints F G) (PlotSmoothRationalFunctions F G) :=
  (plotSmoothSubrepresentation F G).toRepresentation

/-- The slice-regular space retains its actual continuous function realization. -/
def plotSmoothInclusion :
    (plotSmoothRightAction F G).IntertwiningMap (continuousRightAction F G) where
  toLinearMap := (plotSmoothSubrepresentation F G).toSubmodule.subtype
  isIntertwining' _ := by ext; rfl

@[simp]
theorem evaluate_plotSmoothRightAction (g x : AdelicGroupPoints F G)
    (f : PlotSmoothRationalFunctions F G) :
    evaluate F G (plotSmoothRightAction F G g f).val x = evaluate F G f.val (x * g) := rfl

/-- Infinite plot tests with a common open finite stabilizer. -/
def finitePlotSmoothRationalSubrepresentation :
    Subrepresentation (continuousRightAction F G) :=
  infinitePlotSmoothSubrepresentation F G ⊓ finiteSmoothSubrepresentation F G

abbrev FinitePlotSmoothRationalFunctions :=
  (finitePlotSmoothRationalSubrepresentation F G).toSubmodule

theorem finitePlotSmoothRational_le_plotSmooth :
    finitePlotSmoothRationalSubrepresentation F G ≤ plotSmoothSubrepresentation F G :=
  inf_le_inf_left _ (finiteSmooth_le_finiteLocallyConstant F G)

def finitePlotSmoothRightAction :
    Representation ℂ (AdelicGroupPoints F G) (FinitePlotSmoothRationalFunctions F G) :=
  (finitePlotSmoothRationalSubrepresentation F G).toRepresentation

/-- Common finite stabilizers give the equivariant inclusion into slice regularity. -/
def finitePlotSmoothInclusion :
    (finitePlotSmoothRightAction F G).IntertwiningMap (plotSmoothRightAction F G) where
  toLinearMap := (finitePlotSmoothRationalSubrepresentation F G).toSubmodule.inclusion
    (finitePlotSmoothRational_le_plotSmooth F G)
  isIntertwining' _ := by ext; rfl

section GeneralLinearComparison

variable (n : ℕ)

local notation "GLG" =>
  (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F))

local instance plotSmoothGeneralLinearIsAffine : IsAffine (GLG).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

/-- Infinite slices correspond through the original continuous general-linear equivalence. -/
theorem infiniteSlice_continuousGeneralLinearEquiv
    (f : ContinuousRationalFunctions F GLG) (b : FiniteAdelicGroupPoints F GLG) :
    Langlands.Automorphic.infiniteSlice F n (GeneralLinearGroupPoints.finiteHomeomorph F n b)
      (continuousGeneralLinearEquiv F n f) =
    fun a => infiniteSlice F GLG b f ((GeneralLinearGroupPoints.infiniteHomeomorph F n).symm a) := by
  funext a
  obtain ⟨a, rfl⟩ := (GeneralLinearGroupPoints.infiniteHomeomorph F n).surjective a
  rw [(GeneralLinearGroupPoints.infiniteHomeomorph F n).symm_apply_apply]
  exact evaluate_continuousGeneralLinearEquiv_pair F n f a b

/-- The original matrix infinite-smoothness condition is exactly the actual plot-slice condition. -/
theorem continuousGeneralLinearEquiv_mem_infinitePlotSmooth
    (f : ContinuousRationalFunctions F GLG) :
    continuousGeneralLinearEquiv F n f ∈
        Langlands.Automorphic.infiniteSmoothSubrepresentation F n ↔
      f ∈ infinitePlotSmoothSubrepresentation F GLG := by
  rw [mem_infinitePlotSmoothSubrepresentation]
  change (continuousGeneralLinearEquiv F n f ∈
    (⨅ b : FiniteAdelicGL F n,
      (ArchimedeanGL.smoothFunctions F n).comap (Langlands.Automorphic.infiniteSlice F n b))) ↔ _
  simp only [Submodule.mem_iInf, Submodule.mem_comap]
  constructor
  · intro hf b
    apply (GeneralLinearGroupPoints.isPlotSmooth_iff_mem_smoothFunctions F n _).mpr
    rw [← infiniteSlice_continuousGeneralLinearEquiv]
    exact hf _
  · intro hf b
    obtain ⟨b, rfl⟩ := (GeneralLinearGroupPoints.finiteHomeomorph F n).surjective b
    rw [infiniteSlice_continuousGeneralLinearEquiv]
    exact (GeneralLinearGroupPoints.isPlotSmooth_iff_mem_smoothFunctions F n _).mp (hf b)

/-- Slice regularity is preserved and reflected in the original matrix smooth space. -/
theorem continuousGeneralLinearEquiv_mem_plotSmooth
    (f : ContinuousRationalFunctions F GLG) :
    continuousGeneralLinearEquiv F n f ∈ Langlands.Automorphic.smoothSubrepresentation F n ↔
      f ∈ plotSmoothSubrepresentation F GLG := by
  change (continuousGeneralLinearEquiv F n f ∈
      Langlands.Automorphic.infiniteSmoothSubrepresentation F n ∧
    continuousGeneralLinearEquiv F n f ∈
      Langlands.Automorphic.finiteLocallyConstantSubrepresentation F n) ↔
    (f ∈ infinitePlotSmoothSubrepresentation F GLG ∧
      f ∈ finiteLocallyConstantSubrepresentation F GLG)
  rw [continuousGeneralLinearEquiv_mem_infinitePlotSmooth,
    continuousGeneralLinearEquiv_mem_finiteLocallyConstant]

/-- A genuine complex linear equivalence with the original smooth rational-function space. -/
def plotSmoothGeneralLinearEquiv :
    PlotSmoothRationalFunctions F GLG ≃ₗ[ℂ] Langlands.Automorphic.SmoothRationalFunctions F n where
  toFun f := ⟨continuousGeneralLinearEquiv F n f.val,
    (continuousGeneralLinearEquiv_mem_plotSmooth F n f.val).mpr f.property⟩
  invFun f := ⟨(continuousGeneralLinearEquiv F n).symm f.val, by
    apply (continuousGeneralLinearEquiv_mem_plotSmooth F n _).mp
    rw [LinearEquiv.apply_symm_apply]
    exact f.property⟩
  left_inv f := Subtype.ext ((continuousGeneralLinearEquiv F n).symm_apply_apply f.val)
  right_inv f := Subtype.ext ((continuousGeneralLinearEquiv F n).apply_symm_apply f.val)
  map_add' _ _ := Subtype.ext (map_add (continuousGeneralLinearEquiv F n) _ _)
  map_smul' _ _ := Subtype.ext (map_smul (continuousGeneralLinearEquiv F n) _ _)

/-- The comparison is the original ambient map after inclusion. -/
@[simp]
theorem plotSmoothGeneralLinearEquiv_val (f : PlotSmoothRationalFunctions F GLG) :
    (plotSmoothGeneralLinearEquiv F n f).val = continuousGeneralLinearEquiv F n f.val := rfl

/-- The smooth comparison preserves the original full positive adelic action. -/
theorem plotSmoothGeneralLinearEquiv_rightAction
    (f : PlotSmoothRationalFunctions F GLG) (g : AdelicGroupPoints F GLG) :
    plotSmoothGeneralLinearEquiv F n (plotSmoothRightAction F GLG g f) =
      Langlands.Automorphic.smoothRightAction F n
        (GeneralLinearGroupPoints.adelicHomeomorph F n g) (plotSmoothGeneralLinearEquiv F n f) := by
  apply Subtype.ext
  exact continuousGeneralLinearEquiv_rightAction F n f.val g

/-- A common finite stabilizer is also preserved together with infinite smoothness. -/
theorem continuousGeneralLinearEquiv_mem_finitePlotSmooth
    (f : ContinuousRationalFunctions F GLG) :
    continuousGeneralLinearEquiv F n f ∈
        Langlands.Automorphic.finiteSmoothRationalSubrepresentation F n ↔
      f ∈ finitePlotSmoothRationalSubrepresentation F GLG := by
  change (continuousGeneralLinearEquiv F n f ∈
      Langlands.Automorphic.infiniteSmoothSubrepresentation F n ∧
    continuousGeneralLinearEquiv F n f ∈
      Langlands.Automorphic.finiteSmoothSubrepresentation F n) ↔
    (f ∈ infinitePlotSmoothSubrepresentation F GLG ∧
      f ∈ finiteSmoothSubrepresentation F GLG)
  rw [continuousGeneralLinearEquiv_mem_infinitePlotSmooth,
    continuousGeneralLinearEquiv_mem_finiteSmooth]

/-- The original finite-smooth rational space is recovered on the actual carrier. -/
def finitePlotSmoothGeneralLinearEquiv :
    FinitePlotSmoothRationalFunctions F GLG ≃ₗ[ℂ]
      Langlands.Automorphic.FiniteSmoothRationalFunctions F n where
  toFun f := ⟨continuousGeneralLinearEquiv F n f.val,
    (continuousGeneralLinearEquiv_mem_finitePlotSmooth F n f.val).mpr f.property⟩
  invFun f := ⟨(continuousGeneralLinearEquiv F n).symm f.val, by
    apply (continuousGeneralLinearEquiv_mem_finitePlotSmooth F n _).mp
    rw [LinearEquiv.apply_symm_apply]
    exact f.property⟩
  left_inv f := Subtype.ext ((continuousGeneralLinearEquiv F n).symm_apply_apply f.val)
  right_inv f := Subtype.ext ((continuousGeneralLinearEquiv F n).apply_symm_apply f.val)
  map_add' _ _ := Subtype.ext (map_add (continuousGeneralLinearEquiv F n) _ _)
  map_smul' _ _ := Subtype.ext (map_smul (continuousGeneralLinearEquiv F n) _ _)

@[simp]
theorem finitePlotSmoothGeneralLinearEquiv_val (f : FinitePlotSmoothRationalFunctions F GLG) :
    (finitePlotSmoothGeneralLinearEquiv F n f).val = continuousGeneralLinearEquiv F n f.val := rfl

/-- The common-stabilizer comparison preserves the original full positive adelic action. -/
theorem finitePlotSmoothGeneralLinearEquiv_rightAction
    (f : FinitePlotSmoothRationalFunctions F GLG) (g : AdelicGroupPoints F GLG) :
    finitePlotSmoothGeneralLinearEquiv F n (finitePlotSmoothRightAction F GLG g f) =
      Langlands.Automorphic.finiteSmoothRightAction F n
        (GeneralLinearGroupPoints.adelicHomeomorph F n g)
        (finitePlotSmoothGeneralLinearEquiv F n f) := by
  apply Subtype.ext
  exact continuousGeneralLinearEquiv_rightAction F n f.val g

/-- The two general-linear comparisons commute with the common-stabilizer inclusion. -/
theorem plotSmoothGeneralLinearEquiv_finiteInclusion
    (f : FinitePlotSmoothRationalFunctions F GLG) :
    plotSmoothGeneralLinearEquiv F n (finitePlotSmoothInclusion F GLG f) =
      Langlands.Automorphic.finiteSmoothInclusion F n (finitePlotSmoothGeneralLinearEquiv F n f) := by
  rfl

end GeneralLinearComparison

end Langlands.Automorphic.GroupSchemeFunctions
