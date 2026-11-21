import Langlands.Automorphic.BlockShapeConstantTerm
import Langlands.Automorphic.CompactAction
import Langlands.Global.FiniteBlockParabolicCosets

/-! # The separate block scalars and their action on functions -/

noncomputable section

universe u

open NumberField
open scoped Classical BigOperators CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global Langlands.GeneralLinear

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)

local instance constantTermIdeleOrbitRationalAddCommGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance constantTermIdeleOrbitContinuousAddCommGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance constantTermIdeleOrbitFiniteSmoothAddCommGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local notation "I" => Fin B.length
local notation "G" => AdelicGL F n
local notation "V" => FiniteSmoothRationalFunctions F n
local notation "M" => AdelicBlockParabolic.FullLevi F B
local notation "Cen" => (Fin B.length → Ideles F)
local notation "Lemb" => B.leviEmbedding (Adeles F)

/-- The separate scalar ideles of the actual Levi blocks. -/
def blockLeviScalars : Cen →ₜ* M where
  toFun z i := AdelicGL.scalar F (B.size i) (z i)
  map_one' := funext fun i => map_one (AdelicGL.scalar F (B.size i))
  map_mul' z w := funext fun i => map_mul (AdelicGL.scalar F (B.size i)) (z i) (w i)
  continuous_toFun := continuous_pi fun i => (AdelicGL.scalar F (B.size i)).continuous.comp (continuous_apply i)

@[simp]
theorem blockLeviScalars_apply (z : Cen) (i : I) :
    blockLeviScalars F B z i = AdelicGL.scalar F (B.size i) (z i) := rfl

theorem blockLeviScalars_commute (z : Cen) (m : M) : Commute (blockLeviScalars F B z) m :=
  funext fun i => (AdelicGL.scalar_commute F (B.size i) (z i) (m i)).eq

/-- The actual block constant term as a linear map into functions on the adelic group. -/
def blockShapeConstantTermLinear : V →ₗ[ℂ] (G → ℂ) where
  toFun f := blockShapeConstantTerm B F f
  map_add' f g := funext fun x => congrFun
    (map_add (finiteSmoothBlockConstantTerm F (standardBlockWeight B.cuts)) f g)
    ((GeneralLinearGroupPoints.adelicEquiv F n).symm x)
  map_smul' c f := funext fun x => congrFun
    (map_smul (finiteSmoothBlockConstantTerm F (standardBlockWeight B.cuts)) c f)
    ((GeneralLinearGroupPoints.adelicEquiv F n).symm x)

/-- The block idele centre acts on functions on the full group by left translation. -/
def blockConstantTermScalarAction : Representation ℂ Cen (G → ℂ) where
  toFun z :=
    { toFun h g := h (Lemb (blockLeviScalars F B z) * g)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_one' := LinearMap.ext fun h => funext fun g => by simp only [map_one, one_mul]; rfl
  map_mul' z w := LinearMap.ext fun h => funext fun g => by
    change h (Lemb (blockLeviScalars F B (z * w)) * g) =
      h (Lemb (blockLeviScalars F B w) * (Lemb (blockLeviScalars F B z) * g))
    rw [mul_comm z w, map_mul, map_mul, mul_assoc]

@[simp]
theorem blockConstantTermScalarAction_apply (z : Cen) (h : G → ℂ) (g : G) :
    blockConstantTermScalarAction F B z h g = h (Lemb (blockLeviScalars F B z) * g) := rfl

end Langlands.Automorphic
