import Langlands.GroupScheme.MatrixRepresentation.FieldExtensionSubspaces
import Langlands.GroupScheme.MatrixRepresentation.AffineSemisimpleModules
import Langlands.GroupScheme.MatrixRepresentation.AffineCoefficientBaseChange

/-! # Descent of actual semisimplicity along a field extension -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation.FieldExtensionDescent

open AffineCoefficientAlgebra AffineCoefficientBaseChange
open AffineSemisimpleModules FieldExtensionSubspaces

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {n : Type} [Fintype n] [DecidableEq n]

/-- Entrywise scalar extension of coordinate vectors. -/
def vectorMap : (n → k) →ₗ[k] (n → K) where
  toFun v i := algebraMap k K (v i)
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp [Algebra.smul_def]

/-- Applying a smaller-field coefficient functional in each coordinate. -/
def coefficientVector (ℓ : K →ₗ[k] k) : (n → K) →ₗ[k] (n → k) where
  toFun v i := ℓ (v i)
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/-- Descending an extended endomorphism by a coefficient functional. -/
def descendEndomorphism (P : Module.End K (n → K)) (ℓ : K →ₗ[k] k) :
    Module.End k (n → k) :=
  (coefficientVector ℓ).comp ((P.restrictScalars k).comp vectorMap)

omit [Fintype n] [DecidableEq n] in
theorem coefficientVector_vectorMap (ℓ : K →ₗ[k] k) (hℓ : ℓ 1 = 1)
    (v : n → k) : coefficientVector ℓ (vectorMap (K := K) v) = v := by
  funext i
  have h := ℓ.map_smul (v i) (1 : K)
  simpa [coefficientVector, vectorMap, Algebra.smul_def, hℓ] using h

theorem vectorMap_end (f : Module.End k (n → k)) (v : n → k) :
    vectorMap (K := K) (f v) = extensionHom (K := K) f (vectorMap v) := by
  let C := LinearMap.toMatrix' f
  have hC : C.mulVecLin = f := Matrix.toLin'_toMatrix' f
  rw [← hC, extensionHom_mulVecLin]
  funext i
  exact (algebraMap k K).map_mulVec C v i

theorem coefficientVector_end (ℓ : K →ₗ[k] k)
    (f : Module.End k (n → k)) (v : n → K) :
    coefficientVector ℓ (extensionHom (K := K) f v) = f (coefficientVector ℓ v) := by
  let C := LinearMap.toMatrix' f
  have hC : C.mulVecLin = f := Matrix.toLin'_toMatrix' f
  rw [← hC, extensionHom_mulVecLin]
  exact linearFunctional_mulVec_rectangular C v ℓ

omit [Fintype n] [DecidableEq n] in
/-- A projection commutes with any linear operator preserving both its image
subspace and its complementary subspace. -/
theorem projection_commutes (S T : Submodule K (n → K)) (hST : IsCompl S T)
    (f : Module.End K (n → K))
    (hS : ∀ v ∈ S, f v ∈ S) (hT : ∀ v ∈ T, f v ∈ T) (v : n → K) :
    S.projection T hST (f v) = f (S.projection T hST v) := by
  calc
    _ = S.projection T hST
        (f (S.projection T hST v + T.projection S hST.symm v)) := by
          rw [Submodule.projection_add_projection_eq_self]
    _ = S.projection T hST (f (S.projection T hST v)) +
        S.projection T hST (f (T.projection S hST.symm v)) := by
          rw [map_add, map_add]
    _ = f (S.projection T hST v) + 0 := by
      rw [Submodule.projection_apply_of_mem_left hST
          (hS _ (Submodule.projection_apply_mem hST v)),
        Submodule.projection_apply_of_mem_right hST
          (hT _ (Submodule.projection_apply_mem hST.symm v))]
    _ = _ := add_zero _

variable {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (ρ : MatrixRepresentation G n)

local instance operatorRing : Ring (operatorAlgebra ρ) := inferInstance
local instance extendedOperatorRing :
    Ring (operatorAlgebra
      (ρ.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K))))) := inferInstance

/-- Milne 4.19(a), semisimple case, expressed in the target's exact raw
simple-subspace sum formula. -/
theorem isSemisimple_of_baseChange
    (hρ : sSup {W : Submodule K (n → K) |
      (ρ.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).IsStableSubspace W ∧
      W ≠ ⊥ ∧ ∀ U : Submodule K (n → K),
        (ρ.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).IsStableSubspace U →
        U ≤ W → U = ⊥ ∨ U = W} = ⊤) :
    sSup {W : Submodule k (n → k) | ρ.IsStableSubspace W ∧ W ≠ ⊥ ∧
      ∀ U : Submodule k (n → k), ρ.IsStableSubspace U → U ≤ W →
        U = ⊥ ∨ U = W} = ⊤ := by
  classical
  let ρK := ρ.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  let : IsSemisimpleModule (operatorAlgebra ρK) (n → K) :=
    (AffineSemisimpleModules.isSemisimpleModule_iff ρK).mpr hρ
  apply (AffineSemisimpleModules.isSemisimpleModule_iff ρ).mp
  refine { exists_isCompl := fun S => ?_ }
  let W := S.restrictScalars k
  have hW : ρ.IsStableSubspace W := stable_restrictScalars ρ S
  have hWK : ρK.IsStableSubspace (scalarExtension (K := K) W) := hW.scalarExtension
  let SK := operatorSubmodule ρK (scalarExtension (K := K) W) hWK
  obtain ⟨T, hST⟩ := exists_isCompl SK
  let hSTK : IsCompl (SK.restrictScalars K) (T.restrictScalars K) :=
    (Submodule.isCompl_restrictScalars_iff K).mpr hST
  let P := (SK.restrictScalars K).projection (T.restrictScalars K) hSTK
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_eq_one k (one_ne_zero : (1 : K) ≠ 0)
  let F := descendEndomorphism P ℓ
  have hPmem (v : n → K) : P v ∈ scalarExtension (K := K) W :=
    Submodule.projection_apply_mem hSTK v
  have hFmem (v : n → k) : F v ∈ W :=
    coefficients_mem (hPmem (vectorMap v)) ℓ
  have hFfix (v : n → k) (hv : v ∈ W) : F v = v := by
    have hm : vectorMap (K := K) v ∈ SK.restrictScalars K :=
      (mem_scalarExtension_iff (K := K) W v).mpr hv
    have hp : P (vectorMap v) = vectorMap (K := K) v :=
      Submodule.projection_apply_of_mem_left hSTK hm
    change coefficientVector ℓ (P (vectorMap v)) = v
    rw [hp]
    exact coefficientVector_vectorMap ℓ hℓ v
  have hPcomm (a : operatorAlgebra ρ) (v : n → K) :
      P (extensionHom (K := K) a.val v) =
        extensionHom (K := K) a.val (P v) := by
    apply projection_commutes _ _ hSTK
    · exact operator_preserves ρ hWK a.property
    · exact operator_preserves ρ (stable_restrictScalars ρK T) a.property
  have hFcomm (a : operatorAlgebra ρ) (v : n → k) :
      F (a • v) = a • F v := by
    change coefficientVector ℓ (P (vectorMap (a.val v))) =
      a.val (coefficientVector ℓ (P (vectorMap v)))
    rw [vectorMap_end, hPcomm, coefficientVector_end]
  let r : (n → k) →ₗ[operatorAlgebra ρ] S :=
    { toFun := fun v => ⟨F v, hFmem v⟩
      map_add' := fun v w => Subtype.ext (F.map_add v w)
      map_smul' := fun a v => Subtype.ext (hFcomm a v) }
  refine ⟨LinearMap.ker r, LinearMap.isCompl_of_proj ?_⟩
  intro v
  exact Subtype.ext (hFfix v v.property)

end Langlands.GroupScheme.MatrixRepresentation.FieldExtensionDescent
