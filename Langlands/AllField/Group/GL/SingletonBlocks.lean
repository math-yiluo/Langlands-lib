import Langlands.Group.GL.SingletonBlocks
import Langlands.AllField.Group.GL.BlockModulus
/-!
# The singleton block shape and the upper unipotent group

With `n` blocks of size one, the standard block parabolic is the upper triangular
group and its unipotent radical is the actual upper unipotent group, with the same
matrices. Levi elements are diagonal matrices, and the block modulus is the
product of the root quotients `|t_i| / |t_j|` over `i < j`.
-/

open scoped BigOperators NNReal

namespace Langlands.AllField.GeneralLinear
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear

universe u

namespace BlockShape
open Langlands.GeneralLinear.BlockShape
open Langlands.AllField.GeneralLinear.BlockShape
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear

variable {n : ℕ}

variable (R : Type u) [CommRing R]

section Topology

variable [TopologicalSpace R]

end Topology

end BlockShape
end Langlands.AllField.GeneralLinear

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.GeneralLinear.BlockShape hiding oppositeParabolicLocallyCompactSpace parabolicLocallyCompactSpace unipotentRadicalLocallyCompactSpace
open Langlands.AllField.GeneralLinear.BlockShape

universe u

variable {F : Type u} [Field F] (T : LocalFieldData F)

/-- The singleton block modulus of a diagonal element is the product of the root
quotients `|t_i| / |t_j|` over `i < j`. -/
theorem leviModulus_singletonLevi {n : ℕ} (t : Fin n → Fˣ) :
    T.leviModulus (singletons n) (singletonLevi F t) =
      ∏ i : Fin n, ∏ j ∈ Finset.univ.filter (fun j => i < j),
        T.normalizedAbsUnits (t i) / T.normalizedAbsUnits (t j) := by
  rw [T.leviModulus_apply]
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  rw [singletonLevi_apply, singletonLevi_apply, T.determinantNorm_scalar,
    T.determinantNorm_scalar]
  simp only [pow_one]

end Langlands.LocalFieldData
