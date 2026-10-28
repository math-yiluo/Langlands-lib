import Langlands.Algebra.UnitizationNoetherianStatements
import Mathlib.Algebra.Module.RingHom
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Noetherianity of a unitization and its scalar-projection kernel

Derived internal algebra over the actual Mathlib unitization.
-/

set_option autoImplicit false

namespace Langlands.Algebra.UnitizationNoetherian

universe uR uA

variable (R : Type uR) (A : Type uA)
variable [CommRing R] [NonUnitalRing A] [Module R A]
variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem noetherian_iff_kernel :
    IsNoetherianRing (Unitization R A) ↔
      IsNoetherianRing R ∧
        IsNoetherian (Unitization R A) (RingHom.ker (Unitization.fstHom R A)) := by
  constructor
  · intro h
    let := h
    refine ⟨isNoetherianRing_of_surjective (Unitization R A) R
      (Unitization.fstHom R A).toRingHom ?_, inferInstance⟩
    intro r
    exact ⟨Unitization.inl r, rfl⟩
  · rintro ⟨hR, hI⟩
    let := hR
    let : Module (Unitization R A) R :=
      Module.compHom R (Unitization.fstHom R A).toRingHom
    let : IsScalarTower R (Unitization R A) R :=
      ⟨fun r u s => by
        change (r • u).fst * s = r * (u.fst * s)
        simp [mul_assoc]⟩
    let : IsNoetherian (Unitization R A) R :=
      isNoetherian_of_tower R (inferInstance : IsNoetherian R R)
    let p : Unitization R A →ₗ[Unitization R A] R :=
      { toFun := fun u => u.fst
        map_add' := fun _ _ => rfl
        map_smul' := fun u v => by
          change (u * v).fst = u.fst * v.fst
          exact Unitization.fst_mul u v }
    let I : Submodule (Unitization R A) (Unitization R A) :=
      RingHom.ker (Unitization.fstHom R A)
    have : IsNoetherian (Unitization R A) I := hI
    apply isNoetherian_of_range_eq_ker I.subtype p
    change LinearMap.range I.subtype = I
    exact Submodule.range_subtype I

theorem kernelCriterion : KernelCriterionStatement.{uR, uA} := by
  intro R A _ _ _ _ _
  exact noetherian_iff_kernel R A

theorem noetherianScalarCriterion : NoetherianScalarCriterionStatement.{uR, uA} := by
  intro R A _ _ _ _ _ _
  exact ⟨fun h => ((noetherian_iff_kernel R A).mp h).2,
    fun h => (noetherian_iff_kernel R A).mpr ⟨inferInstance, h⟩⟩

theorem fieldCriterion : FieldCriterionStatement.{uR, uA} := by
  intro k A _ _ _ _ _
  exact noetherianScalarCriterion k A

theorem unitizationNoetherian : UnitizationNoetherianStatement.{uR, uA} :=
  ⟨kernelCriterion, noetherianScalarCriterion, fieldCriterion⟩

end Langlands.Algebra.UnitizationNoetherian
