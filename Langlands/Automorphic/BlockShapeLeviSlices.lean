import Langlands.Automorphic.BlockShapeConstantTerm
import Langlands.Automorphic.GeneralLinearBlockLeviSlice
import Langlands.Global.AdelicBlockParabolic
import Langlands.Global.AdelicGLIwasawa
import Langlands.Group.GL.TriangularParabolic

/-! # Matrix Levi slices and archimedean Iwasawa detection -/

noncomputable section

universe u

open NumberField
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.GeneralLinear Langlands.Global

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)

local instance blockLeviSlicesRationalAddCommGroup : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance blockLeviSlicesContinuousAddCommGroup : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance blockLeviSlicesFiniteSmoothAddCommGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _

/-- The original block constant term at `m g`, in the product of actual adelic blocks. -/
def blockShapeLeviSlice (f : FiniteSmoothRationalFunctions F n) (g : AdelicGL F n)
    (m : AdelicBlockParabolic.FullLevi F B) : ℂ :=
  blockShapeConstantTerm B F f (B.leviEmbedding (Adeles F) m * g)

theorem continuous_blockShapeLeviSlice (f : FiniteSmoothRationalFunctions F n) (g : AdelicGL F n) :
    Continuous (blockShapeLeviSlice F B f g) := by
  let a := (GroupSchemeFunctions.continuousGeneralLinearEquiv F n).symm f.val
  exact (GroupSchemeFunctions.continuous_normalizedBlockConstantTerm F
    (standardBlockWeight B.cuts) a).comp
    ((GeneralLinearGroupPoints.adelicHomeomorph F n).symm.continuous.comp
      ((B.leviEmbeddingContinuous (Adeles F)).continuous.mul_const g))

/-- Left multiplication by a parabolic point is evaluated at its Levi factor. -/
theorem blockShapeConstantTerm_parabolic_mul (f : FiniteSmoothRationalFunctions F n)
    (p : AdelicBlockParabolic.Full F B) (g : AdelicGL F n) :
    blockShapeConstantTerm B F f (p.val * g) =
      blockShapeLeviSlice F B f g (B.leviProjection (Adeles F) p) := by
  let u := B.unipotentPart (Adeles F) p
  let m := B.leviProjection (Adeles F) p
  have hu : u.val.val ∈ B.unipotentSubgroup (Adeles F) := ⟨u.val, u.property, rfl⟩
  have hp : u.val.val * B.leviEmbedding (Adeles F) m = p.val :=
    congrArg Subtype.val ((B.decomposition (Adeles F)).left_inv p)
  change _ = blockShapeConstantTerm B F f (B.leviEmbedding (Adeles F) m * g)
  rw [← hp, mul_assoc]
  exact blockShapeConstantTerm_unipotent_mul B F f hu _

/-- The unnormalized Levi slices transform by right translation in the Levi
when the ambient argument is multiplied on the left by a parabolic element. -/
theorem blockShapeLeviSlice_parabolic_mul (f : FiniteSmoothRationalFunctions F n)
    (p : AdelicBlockParabolic.Full F B) (g : AdelicGL F n) (m : AdelicBlockParabolic.FullLevi F B) :
    blockShapeLeviSlice F B f (p.val * g) m =
      blockShapeLeviSlice F B f g (m * B.leviProjection (Adeles F) p) := by
  have h := blockShapeConstantTerm_parabolic_mul F B f (B.leviInParabolic (Adeles F) m * p) g
  simpa only [Subgroup.coe_mul, B.leviInParabolic_val, map_mul, B.leviProjection_section,
    blockShapeLeviSlice, mul_assoc] using h

theorem blockShapeLeviSlice_rightAction (f : FiniteSmoothRationalFunctions F n)
    (h g : AdelicGL F n) (m : AdelicBlockParabolic.FullLevi F B) :
    blockShapeLeviSlice F B (finiteSmoothRightAction F n h f) g m =
      blockShapeLeviSlice F B f (g * h) m := by
  change blockShapeConstantTerm B F (finiteSmoothRightAction F n h f)
    (B.leviEmbedding (Adeles F) m * g) = _
  rw [blockShapeConstantTerm_rightAction, mul_assoc]
  rfl

/-- The entire constant term is detected by Levi slices at standard
archimedean compact elements and all finite adelic arguments. -/
theorem blockShapeConstantTerm_eq_leviSlice_at_infiniteCompact
    (f : FiniteSmoothRationalFunctions F n) (g : AdelicGL F n) :
    ∃ (k : standardInfiniteCompact F n) (m : AdelicBlockParabolic.FullLevi F B),
      blockShapeConstantTerm B F f g =
        blockShapeLeviSlice F B f (AdelicGL.pair F n k.val (AdelicGL.finite F n g)) m := by
  obtain ⟨b, k, hg, hb, hk⟩ := PrimitiveAdelicHeight.exists_infinite_iwasawa F n
    (AdelicGL.infinite F n g)
  let p : AdelicBlockParabolic.Full F B :=
    AdelicBlockParabolic.pair F B ⟨b, B.mem_parabolic_of_isUpperTriangular b hb⟩ 1
  have hp : g = p.val * AdelicGL.pair F n k (AdelicGL.finite F n g) := by
    change g = AdelicGL.pair F n b 1 * AdelicGL.pair F n k (AdelicGL.finite F n g)
    rw [AdelicGL.pair_mul, one_mul, ← hg, AdelicGL.pair_projections]
  refine ⟨⟨k, hk⟩, B.leviProjection (Adeles F) p, ?_⟩
  exact congrArg (blockShapeConstantTerm B F f) hp |>.trans
    (blockShapeConstantTerm_parabolic_mul F B f p _)

end Langlands.Automorphic
