import Langlands.ClassFieldTheory.Local.Norms
import Mathlib.Algebra.Group.Units.Equiv

/-! Surjectivity of determinant norms under composition and compatible field equivalences. -/
namespace Langlands.ClassFieldTheory.Local.InertiaNormTransport

open Langlands.LocalClassField

universe u v w z

theorem surjective_norm_trans (K : Type u) (E : Type v) (L : Type w)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
    [FiniteDimensional K E] [FiniteDimensional E L] [FiniteDimensional K L]
    (hKE : Function.Surjective (normUnits K E))
    (hEL : Function.Surjective (normUnits E L)) :
    Function.Surjective (normUnits K L) := by
  intro x
  obtain ⟨y, hy⟩ := hKE x
  obtain ⟨z, hz⟩ := hEL y
  refine ⟨z, ?_⟩
  rw [← hy, ← hz]
  apply Units.ext
  exact (Algebra.norm_norm (R := K) (S := E) (a := (z : L))).symm

theorem surjective_norm_of_equiv (K : Type u) (L : Type v) (K' : Type w) (L' : Type z)
    [Field K] [Field L] [Field K'] [Field L']
    [Algebra K L] [Algebra K' L']
    [FiniteDimensional K L] [FiniteDimensional K' L']
    (eK : K ≃+* K') (eL : L ≃+* L')
    (hc : (algebraMap K' L').comp eK =
      (eL : L →+* L').comp (algebraMap K L))
    (h : Function.Surjective (normUnits K' L')) :
    Function.Surjective (normUnits K L) := by
  intro x
  obtain ⟨y, hy⟩ := h (Units.mapEquiv eK.toMulEquiv x)
  refine ⟨Units.mapEquiv eL.symm.toMulEquiv y, ?_⟩
  apply Units.ext
  change Algebra.norm K (eL.symm (y : L')) = (x : K)
  rw [Algebra.norm_eq_of_equiv_equiv eK eL hc, eL.apply_symm_apply]
  have hv := congrArg (fun t : K'ˣ => (t : K')) hy
  change Algebra.norm K' (y : L') = eK (x : K) at hv
  rw [hv, eK.symm_apply_apply]

end Langlands.ClassFieldTheory.Local.InertiaNormTransport
