import Langlands.GroupScheme.SimplyConnected.LocalCocycleVanishingStatement
import Langlands.GroupScheme.SimplyConnected.LocalGaloisCocycleVanishingStatement
import Langlands.GroupScheme.CocycleRefinement
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.AlgebraicGeometry.PointTopology.ProductRingPoints
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.IsSepClosed

/-! # From finite Galois covers to finite separable covers

A cocycle on a finite separable cover `Spec L` is refined to the cover by the spectrum of a
normal closure of `L/F` inside a separable closure of `F`. That refinement is a finite Galois
cover, and triviality of cocycles is reflected along the faithfully flat field map.
The converse implication is the specialization to Galois extensions.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A finite separable extension admits an `F`-embedding into a finite Galois extension in the
same universe: the normal closure of its image in a separable closure of `F`. -/
theorem exists_finite_galois_algHom (F : Type u) [Field F] (L : Type u) [Field L]
    [Algebra F L] [FiniteDimensional F L] [Algebra.IsSeparable F L] :
    ∃ (E : IntermediateField F (SeparableClosure F)),
      FiniteDimensional F E ∧ IsGalois F E ∧ Nonempty (L →ₐ[F] E) := by
  let E := IntermediateField.normalClosure F L (SeparableClosure F)
  have hsep : Algebra.IsSeparable F E :=
    Algebra.isSeparable_tower_bot_of_isSeparable F E (SeparableClosure F)
  exact ⟨E, inferInstance, { to_isSeparable := hsep, to_normal := inferInstance },
    ⟨(normalClosure.algHomEquiv F L (SeparableClosure F)).symm IsSepClosed.lift⟩⟩

/-- Vanishing on every finite Galois cover gives vanishing on every finite separable cover. -/
theorem localSimplyConnectedCocycleVanishing_of_galois
    (h : LocalSimplyConnectedGaloisCocycleVanishingStatement.{u}) :
    LocalSimplyConnectedCocycleVanishingStatement.{u} := by
  intro F _ _ _ _ G _ hG L _ _ _ _ ξ
  obtain ⟨E, hfin, hgal, ⟨φ⟩⟩ := exists_finite_galois_algHom F L
  let : Algebra L E := φ.toRingHom.toAlgebra
  obtain ⟨h₁, h₂, h₃⟩ := fieldExtension_fpqc L E
  have : Surjective (ringTestMap F φ).left := h₁
  have : Flat (ringTestMap F φ).left := h₂
  have : QuasiCompact (ringTestMap F φ).left := h₃
  let ξ' : Cocycle G (ringTest F L) := ξ
  have hE : (ξ'.refine (ringTestMap F φ)).IsTrivial := h F G hG E _
  exact (ξ'.isTrivial_refine_iff (ringTestMap F φ)).mp hE

/-- Vanishing on every finite separable cover gives vanishing on every finite Galois cover. -/
theorem localSimplyConnectedGaloisCocycleVanishing_of_separable
    (h : LocalSimplyConnectedCocycleVanishingStatement.{u}) :
    LocalSimplyConnectedGaloisCocycleVanishingStatement.{u} := by
  intro F _ _ _ _ G _ hG M _ _ _ _ ξ
  exact h F G hG M ξ

/-- The finite Galois and finite separable forms of local cocycle vanishing are equivalent. -/
theorem localSimplyConnectedGaloisCocycleVanishing_iff :
    LocalSimplyConnectedGaloisCocycleVanishingStatement.{u} ↔
      LocalSimplyConnectedCocycleVanishingStatement.{u} :=
  ⟨localSimplyConnectedCocycleVanishing_of_galois,
    localSimplyConnectedGaloisCocycleVanishing_of_separable⟩

end Langlands.GroupScheme
