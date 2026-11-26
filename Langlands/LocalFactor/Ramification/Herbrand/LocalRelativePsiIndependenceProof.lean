import Langlands.LocalFactor.Ramification.Herbrand.LocalTowerProof
import Langlands.LocalFactor.Ramification.Herbrand.LocalSubextensionStatement

/-!
# Independence of the relative inverse Herbrand function

For a finite intermediate field `E` of a separable closure `Ω/K`, the relative
index `φ_{M/E} ∘ ψ_{M/K}` does not depend on the finite Galois field `M ⊇ E`.
For nested fields the two Herbrand tower laws cancel the contribution of the
enlargement, and the normal closure of `E/K` lies in every such `M`.
-/

namespace Langlands.Ramification.Local

universe u₀ uK uΩ

/-- The relative index `φ_{M/E} ∘ ψ_{M/K}` does not change when the finite
Galois field `M₀ ⊇ E` is enlarged to `M` (Serre, *Local Fields*, IV §3,
Proposition 15 and Remark 2). -/
theorem relativeIndex_eq_of_le
    (K₀ : Type u₀) [NontriviallyNormedField K₀] [IsUltrametricDist K₀]
    [CompleteSpace K₀] [ValuativeRel K₀] [LocallyCompactSpace K₀]
    (K : Type uK) [Field K] [Algebra K₀ K] [FiniteDimensional K₀ K]
    {Ω : Type uΩ} [Field Ω] [Algebra K Ω] [Algebra K₀ Ω] [IsScalarTower K₀ K Ω]
    (hbase : ∀ a b : K₀, ‖a‖ ≤ ‖b‖ ↔ ValuativeRel.vle a b)
    (E : IntermediateField K Ω)
    {M₀ M : FiniteGaloisIntermediateField K Ω} (hle : M₀ ≤ M)
    (h₀ : ∀ x : E, algebraMap E Ω x ∈ M₀.toIntermediateField)
    (h : ∀ x : E, algebraMap E Ω x ∈ M.toIntermediateField) (u : ℝ) :
    haveI : IsScalarTower K₀ E Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
    relativeIndex K₀ K hbase M h u = relativeIndex K₀ K hbase M₀ h₀ u := by
  let : IsScalarTower K₀ E Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let N₀ := extendFiniteGalois h₀
  let N := extendFiniteGalois h
  have hN : N₀.toIntermediateField ≤ N.toIntermediateField := fun _ hx => hle hx
  let : Algebra N₀ N := (IntermediateField.inclusion hN).toRingHom.toAlgebra
  let : IsScalarTower K N₀ N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower E N₀ N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower K₀ N₀ N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower K₀ K N₀ := IsScalarTower.of_algebraMap_eq fun a =>
    Subtype.ext (IsScalarTower.algebraMap_apply K₀ K Ω a)
  let : IsScalarTower K₀ K N := IsScalarTower.of_algebraMap_eq fun a =>
    Subtype.ext (IsScalarTower.algebraMap_apply K₀ K Ω a)
  have : FiniteDimensional K N₀ := M₀.finiteDimensional
  have : FiniteDimensional K N := M.finiteDimensional
  have : FiniteDimensional K₀ N₀ := FiniteDimensional.trans K₀ K N₀
  have : FiniteDimensional K₀ N := FiniteDimensional.trans K₀ K N
  have : IsGalois K N₀ := M₀.isGalois
  have : IsGalois K N := M.isGalois
  have : IsGalois N₀ N := IsGalois.tower_top_of_isGalois K N₀ N
  let S := LocalField.canonicalTopologicalData K₀ N₀ hbase
  let T := LocalField.canonicalTopologicalData K₀ N hbase
  change herbrandPhi T E (herbrandPsi T K u) = herbrandPhi S E (herbrandPsi S K u)
  rw [herbrandPsiTower K N N₀ T S u, herbrandPhiTower E N N₀ T S, herbrandPhi_herbrandPsi]

/-- The relative inverse Herbrand function `ψ_{E/K}`, computed in the normal
closure of `E/K`, equals the relative index `φ_{M/E} ∘ ψ_{M/K}` of every finite
Galois intermediate field `M` of `Ω/K` containing `E`, at every real argument
(Serre, *Local Fields*, IV §3, Remark 2). -/
theorem relativeHerbrandPsiIndependence :
    RelativeHerbrandPsiIndependence.{u₀, uK, uΩ} := by
  intro K₀ _ _ _ _ _ K _ _ _ Ω _ _ _ _ _ hbase E _ M h u
  have hE : E ≤ M.toIntermediateField := fun x hx => h ⟨x, hx⟩
  have hle : galoisClosure E ≤ M :=
    (FiniteGaloisIntermediateField.le_iff _ _).mpr
      (IntermediateField.normalClosure_le_iff_of_normal.mpr hE)
  exact (relativeIndex_eq_of_le K₀ K hbase E hle (algebraMap_mem_galoisClosure E) h u).symm

end Langlands.Ramification.Local
