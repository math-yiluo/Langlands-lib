import Langlands.GroupScheme.SimplyConnected.LocalUnramifiedIntegralTwistReductionStatement
import Langlands.GroupScheme.LocalUnramifiedTwistDescent
import Langlands.GroupScheme.CocycleRefinement
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.AlgebraicGeometry.PointTopology.ProductRingPoints

/-! # Integral twists give vanishing on finite unramified covers

A cocycle on a finite unramified cover `Spec E` is refined to the spectrum of the normal closure
`E₁` of `E` inside the maximal unramified extension `L`. Its Galois values form a crossed
homomorphism on `Gal(E₁/F)`; the twisting statement supplies `h ∈ G(L)` making the twisted
values integral, and `GaloisCocycle.isTrivial_of_unramified_integral_twist` trivializes the
refined cocycle. Triviality descends along the faithfully flat field extension `E → E₁`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj ValuativeRel

namespace Langlands.GroupScheme

open LocalGalois.Separable

/-- **Integral twists give vanishing on finite unramified covers.** -/
theorem localSimplyConnectedUnramifiedIntegralTwistReduction :
    LocalSimplyConnectedUnramifiedIntegralTwistReductionStatement.{u} := by
  intro hI F _ _ _ _ G _ hG E _ hE ξ
  obtain ⟨M, hM, hconn, htw⟩ := hI F G hG
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : LocallyOfFiniteType G.X.hom :=
    have : Smooth G.X.hom := hG.isSemisimple.isConnectedReductive.smooth
    inferInstance
  obtain ⟨E₁, _, _, hEE₁, hE₁L⟩ :=
    GaloisCocycle.exists_finiteDimensional_isGalois_between (inertiaFixedField F) E hE
  let φ : E →ₐ[F] E₁ := IntermediateField.inclusion hEE₁
  let : Algebra E E₁ := φ.toRingHom.toAlgebra
  obtain ⟨h₁, h₂, h₃⟩ := fieldExtension_fpqc E E₁
  have : Surjective (ringTestMap F φ).left := h₁
  have : Flat (ringTestMap F φ).left := h₂
  have : QuasiCompact (ringTestMap F φ).left := h₃
  let ξ' : Cocycle G (ringTest F E) := ξ
  refine (ξ'.isTrivial_refine_iff (ringTestMap F φ)).mp ?_
  let ξ₁ : Cocycle G (GaloisCocycle.cover F E₁) := ξ'.refine (ringTestMap F φ)
  let : Algebra E₁ (inertiaFixedField F) := (IntermediateField.inclusion hE₁L).toAlgebra
  have : IsScalarTower F E₁ (inertiaFixedField F) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨h, hh⟩ := htw E₁ (GaloisCocycle.value ξ₁) (GaloisCocycle.value_mul ξ₁)
  exact GaloisCocycle.isTrivial_of_unramified_integral_twist M hM hconn (inertiaFixedField F)
    le_rfl ξ₁ h hh

end Langlands.GroupScheme
