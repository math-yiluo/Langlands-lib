import Langlands.Representation.Plancherel.RationalCharacterValuation
import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-! # Actual rational-character central translations for the enlarged building -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Plancherel

namespace Langlands.Geometry.Building

variable {F : Type u} [Field F]

/-- The real dual of the actual rational characters, with its own translation action. -/
def CentralFactor (G : GroupScheme (Spec (CommRingCat.of F))) : Type u :=
  rationalCharacters G →+ ℝ

namespace CentralFactor

variable (G : GroupScheme (Spec (CommRingCat.of F)))

instance : AddCommGroup (CentralFactor G) :=
  inferInstanceAs (AddCommGroup (rationalCharacters G →+ ℝ))

instance : Module ℝ (CentralFactor G) :=
  inferInstanceAs (Module ℝ (rationalCharacters G →+ ℝ))

/-- The identity linear comparison with the actual rational-character dual. -/
def dualEquiv : CentralFactor G ≃ₗ[ℝ] (rationalCharacters G →+ ℝ) :=
  LinearEquiv.refl ℝ _

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- The negative of the actual source-positive character valuation. -/
def translation : rationalPoints G →* Multiplicative (CentralFactor G) where
  toFun g := Multiplicative.ofAdd (-(rationalNormLogarithm G g).toAdd)
  map_one' := by change -(rationalNormLogarithm G 1).toAdd = 0; simp
  map_mul' g h := by
    change -(rationalNormLogarithm G (g * h)).toAdd =
      -(rationalNormLogarithm G g).toAdd + -(rationalNormLogarithm G h).toAdd
    simp only [map_mul, toAdd_mul, neg_add]

instance : MulAction (rationalPoints G) (CentralFactor G) where
  smul g v := v + (translation G g).toAdd
  one_smul v := by change v + (translation G 1).toAdd = v; simp
  mul_smul g h v := by
    change v + (translation G (g * h)).toAdd =
      (v + (translation G h).toAdd) + (translation G g).toAdd
    simp only [map_mul, toAdd_mul]
    abel

@[simp] theorem smul_eq (g : rationalPoints G) (v : CentralFactor G) :
    g • v = v - (show CentralFactor G from (rationalNormLogarithm G g).toAdd) := rfl

/-- Each coordinate translates by the negative actual integer character valuation. -/
theorem smul_apply (g : rationalPoints G) (v : CentralFactor G)
    (χ : rationalCharacters G) :
    dualEquiv G (g • v) χ = dualEquiv G v χ -
      ((rationalCharacterValuation G g).toAdd χ : ℝ) := by
  change dualEquiv G v χ - (rationalNormLogarithm G g).toAdd χ = _
  rw [rationalNormLogarithm_eq_intValuation]

/-- Zero translation is precisely the existing actual norm kernel. -/
theorem translation_ker : (translation G).ker = rationalCommonNormKernel G := by
  ext g
  rw [← rationalNormLogarithm_ker G]
  change -(rationalNormLogarithm G g).toAdd = 0 ↔
    (rationalNormLogarithm G g).toAdd = 0
  exact neg_eq_zero

theorem smul_eq_self_iff (g : rationalPoints G) (v : CentralFactor G) :
    g • v = v ↔ g ∈ rationalCommonNormKernel G := by
  rw [← translation_ker G]
  change v + (translation G g).toAdd = v ↔ (translation G g).toAdd = 0
  exact add_eq_left

theorem stabilizer_eq (v : CentralFactor G) :
    MulAction.stabilizer (rationalPoints G) v = rationalCommonNormKernel G := by
  ext g
  exact smul_eq_self_iff G g v

/-- The subgroup acting trivially on the whole central factor, using the actual action. -/
def actionKernel : Subgroup (rationalPoints G) :=
  fixingSubgroup (rationalPoints G) (Set.univ : Set (CentralFactor G))

theorem actionKernel_eq : actionKernel G = rationalCommonNormKernel G := by
  ext g
  rw [actionKernel, mem_fixingSubgroup_iff]
  constructor
  · intro hg
    exact (smul_eq_self_iff G g 0).mp (hg 0 (Set.mem_univ _))
  · intro hg v _
    exact (smul_eq_self_iff G g v).mpr hg

theorem exists_fixed_iff (g : rationalPoints G) :
    (∃ v : CentralFactor G, g • v = v) ↔ g ∈ rationalCommonNormKernel G := by
  simp only [smul_eq_self_iff]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨0, h⟩⟩

theorem acts_trivially_iff (g : rationalPoints G) :
    (∀ v : CentralFactor G, g • v = v) ↔ g ∈ rationalCommonNormKernel G := by
  exact ⟨fun h => (smul_eq_self_iff G g 0).mp (h 0),
    fun h v => (smul_eq_self_iff G g v).mpr h⟩

end CentralFactor
end Langlands.Geometry.Building
