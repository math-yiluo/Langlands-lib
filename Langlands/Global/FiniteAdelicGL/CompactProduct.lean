import Langlands.Global.AdelicBlockParabolic
import Langlands.Global.FiniteAdelicGL.RestrictedProduct
import Langlands.Global.FiniteAdelicGL.StandardIntegralCompact

/-!
# Products of the finite adelic compact matrix groups

The standard integral group and its parabolic intersection are the actual
products of their counterparts at the finite places.
-/

noncomputable section

set_option autoImplicit false

universe u

namespace Langlands.Global.FiniteAdelicGL

open Langlands.GeneralLinear

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

private def fromIntegralProduct (x : ∀ v : FinitePlace F, localIntegral F n v) :
    standardIntegral F n := by
  let g : LocalRestrictedProduct F n :=
    ⟨fun v => (x v).val, Filter.Eventually.of_forall fun v => (x v).property⟩
  refine ⟨fromRestrictedProduct F n g, (mem_standardIntegral_iff_local F n _).mpr fun v => ?_⟩
  rw [localProjection_fromRestrictedProduct]
  exact (x v).property

private theorem localProjection_fromIntegralProduct
    (x : ∀ v : FinitePlace F, localIntegral F n v) (v : FinitePlace F) :
    localProjection F n v (fromIntegralProduct F n x).val = (x v).val :=
  localProjection_fromRestrictedProduct F n _ v

private def standardIntegralMulEquiv : (standardIntegral F n) ≃*
    (∀ v : FinitePlace F, localIntegral F n v) where
  toFun g v := ⟨localProjection F n v g.val, (mem_standardIntegral_iff_local F n _).mp g.property v⟩
  invFun := fromIntegralProduct F n
  left_inv g := by
    apply Subtype.ext
    apply ext_localProjection F n
    intro v
    rw [localProjection_fromIntegralProduct]
  right_inv g := by
    funext v
    apply Subtype.ext
    exact localProjection_fromIntegralProduct F n g v
  map_mul' g h := funext fun v => Subtype.ext ((localProjection F n v).map_mul g.val h.val)

/-- The standard integral finite adelic group is the product of the actual local
integral groups, with its product topology. -/
def standardIntegralProductEquiv : (standardIntegral F n) ≃ₜ*
    (∀ v : FinitePlace F, localIntegral F n v) := by
  let e := standardIntegralMulEquiv F n
  have he : Continuous e := continuous_pi fun v =>
    ((localProjection F n v).continuous.comp continuous_subtype_val).subtype_mk _
  let : CompactSpace (standardIntegral F n) :=
    isCompact_iff_compactSpace.mp (isCompact_standardIntegral F n)
  exact { __ := e
          continuous_toFun := he
          continuous_invFun := (he.homeoOfEquivCompactToT2 (f := e.toEquiv)).continuous_symm }

@[simp]
theorem standardIntegralProductEquiv_apply (g : standardIntegral F n) (v : FinitePlace F) :
    (standardIntegralProductEquiv F n g v).val = localProjection F n v g.val := rfl

variable {n} (B : BlockShape n)

private theorem localProjection_mem_parabolic (v : FinitePlace F)
    (p : AdelicBlockParabolic.Finite F B) :
    localProjection F n v p.val ∈ B.parabolic (FiniteCompletion F v) := by
  rw [B.mem_parabolic_iff]
  intro i j a b hij
  rw [localProjection_apply, (B.mem_parabolic_iff _ _).mp p.property i j a b hij]
  rfl

/-- Projection to a finite place restricts to the actual block parabolic. -/
def localParabolicProjection (v : FinitePlace F) :
    AdelicBlockParabolic.Finite F B →ₜ* B.parabolic (FiniteCompletion F v) where
  toFun p := ⟨localProjection F n v p.val, localProjection_mem_parabolic F B v p⟩
  map_one' := Subtype.ext ((localProjection F n v).map_one)
  map_mul' p q := Subtype.ext ((localProjection F n v).map_mul p.val q.val)
  continuous_toFun := ((localProjection F n v).continuous.comp continuous_subtype_val).subtype_mk _

/-- Local projection commutes with extracting each diagonal block. -/
theorem localProjection_leviProjection (v : FinitePlace F) (p : AdelicBlockParabolic.Finite F B)
    (i : Fin B.length) :
    localProjection F (B.size i) v (B.leviProjection (FiniteAdeles F) p i) =
      B.leviProjection (FiniteCompletion F v) (localParabolicProjection F B v p) i := by
  apply Units.ext
  rfl

/-- The standard integral parabolic subgroup, viewed inside the finite adelic
standard integral group. -/
abbrev standardIntegralParabolic : Subgroup (standardIntegral F n) :=
  (B.parabolic (FiniteAdeles F)).comap (standardIntegral F n).toSubgroup.subtype

/-- The corresponding actual intersection at one finite place. -/
abbrev localIntegralParabolic (v : FinitePlace F) : Subgroup (localIntegral F n v) :=
  (B.parabolic (FiniteCompletion F v)).comap (localIntegral F n v).toSubgroup.subtype

theorem mem_standardIntegralParabolic_iff (g : standardIntegral F n) :
    g ∈ standardIntegralParabolic F B ↔
      ∀ v, standardIntegralProductEquiv F n g v ∈ localIntegralParabolic F B v := by
  change g.val ∈ B.parabolic (FiniteAdeles F) ↔
    ∀ v, (standardIntegralProductEquiv F n g v).val ∈ B.parabolic (FiniteCompletion F v)
  constructor
  · exact fun hg v => (localParabolicProjection F B v ⟨g.val, hg⟩).property
  · intro hg
    rw [B.mem_parabolic_iff]
    intro i j a b hij
    refine IsDedekindDomain.FiniteAdeleRing.ext _ fun v => ?_
    exact (B.mem_parabolic_iff _ _).mp (hg v) i j a b hij

/-- The finite adelic compact parabolic subgroup is the product of its actual
local compact parabolic subgroups. -/
def standardIntegralParabolicProductEquiv :
    standardIntegralParabolic F B ≃ₜ* (∀ v : FinitePlace F, localIntegralParabolic F B v) where
  toFun g v := ⟨standardIntegralProductEquiv F n g.val v,
    (mem_standardIntegralParabolic_iff F B _).mp g.property v⟩
  invFun x := ⟨(standardIntegralProductEquiv F n).symm (fun v => (x v).val),
    (mem_standardIntegralParabolic_iff F B _).mpr (by
      intro v
      rw [ContinuousMulEquiv.apply_symm_apply]
      exact (x v).property)⟩
  left_inv g := Subtype.ext ((standardIntegralProductEquiv F n).symm_apply_apply g.val)
  right_inv x := by
    have h := (standardIntegralProductEquiv F n).apply_symm_apply (fun v => (x v).val)
    exact funext fun v => Subtype.ext (congrFun h v)
  map_mul' g h := funext fun v =>
    Subtype.ext (congrFun ((standardIntegralProductEquiv F n).map_mul g.val h.val) v)
  continuous_toFun := continuous_pi fun v =>
    ((continuous_apply v).comp ((standardIntegralProductEquiv F n).continuous.comp
      continuous_subtype_val)).subtype_mk _
  continuous_invFun := ((standardIntegralProductEquiv F n).symm.continuous.comp
    (continuous_pi fun v => continuous_subtype_val.comp (continuous_apply v))).subtype_mk _

@[simp]
theorem standardIntegralParabolicProductEquiv_apply (g : standardIntegralParabolic F B)
    (v : FinitePlace F) :
    (standardIntegralParabolicProductEquiv F B g v).val =
      standardIntegralProductEquiv F n g.val v := rfl

end Langlands.Global.FiniteAdelicGL
