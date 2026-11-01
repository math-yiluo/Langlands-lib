import Langlands.Global.AdelicBlockParabolic
import Langlands.Global.Adelic

/-!
# Scalar ideles in actual adelic block parabolics
-/

noncomputable section

universe uF

namespace Langlands.Global.AdelicBlockCenter

open NumberField IsDedekindDomain
open Langlands.GeneralLinear AdelicBlockParabolic

variable (F : Type uF) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)

/-- A common scalar in every actual diagonal block. -/
def scalarLevi : Ideles F →ₜ* FullLevi F B where
  toFun z i := AdelicGL.scalar F (B.size i) z
  map_one' := by funext i; exact map_one _
  map_mul' z w := by funext i; exact map_mul _ z w
  continuous_toFun := continuous_pi fun i => (AdelicGL.scalar F (B.size i)).continuous

@[simp]
theorem scalarLevi_apply (z : Ideles F) (i : Fin B.length) :
    scalarLevi F B z i = AdelicGL.scalar F (B.size i) z := rfl

/-- Every actual scalar matrix belongs to the actual upper block parabolic. -/
theorem scalar_mem_parabolic (z : Ideles F) :
    AdelicGL.scalar F n z ∈ B.parabolic (Adeles F) := by
  apply (B.mem_parabolic_iff _ _).mpr
  intro i j a b hij
  have hidx : B.index i a ≠ B.index j b := by
    intro h
    have hs : (⟨i, a⟩ : B.Index) = ⟨j, b⟩ := B.indexEquiv.injective h
    exact (ne_of_gt hij) (congrArg Sigma.fst hs)
  change (if B.index i a = B.index j b then (z : Adeles F) else 0) = 0
  simp [hidx]

/-- Scalar ideles valued in the genuine parabolic subgroup, continuously. -/
def scalarParabolic : Ideles F →ₜ* Full F B where
  toFun z := ⟨AdelicGL.scalar F n z, scalar_mem_parabolic F B z⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' z w := Subtype.ext (map_mul _ z w)
  continuous_toFun := (AdelicGL.scalar F n).continuous.subtype_mk _

@[simp]
theorem scalarParabolic_val (z : Ideles F) :
    (scalarParabolic F B z).val = AdelicGL.scalar F n z := rfl

/-- The actual diagonal blocks of a scalar are the corresponding scalar blocks. -/
@[simp]
theorem leviProjection_scalar (z : Ideles F) :
    B.leviProjection (Adeles F) (scalarParabolic F B z) = scalarLevi F B z := by
  funext i
  apply Units.ext
  ext a b
  change (if B.index i a = B.index i b then (z : Adeles F) else 0) =
    if a = b then (z : Adeles F) else 0
  simp only [(B.index i).injective.eq_iff]

/-- Scalar ideles commute with every actual adelic block Levi element. -/
theorem scalarLevi_commute (z : Ideles F) (m : FullLevi F B) :
    Commute (scalarLevi F B z) m := by
  change scalarLevi F B z * m = m * scalarLevi F B z
  funext i
  exact (AdelicGL.scalar_commute F (B.size i) z (m i)).eq

/-- Scalar ideles commute inside the actual block parabolic subgroup. -/
theorem scalarParabolic_commute (z : Ideles F) (p : Full F B) :
    Commute (scalarParabolic F B z) p := by
  apply Subtype.ext
  exact (AdelicGL.scalar_commute F n z p.val).eq

end Langlands.Global.AdelicBlockCenter
