import Langlands.Geometry.Building.KPLocalMoyPrasadGroups
import Langlands.Geometry.Building.KPLocalCorootComponentStatement

/-! # Commutator friendliness of the torus filtration over `F^ur`, from the coroot formula

Clause 1 of KP Lemma 7.2.3 over `K = F^ur`, for D1's filtration
`Z(K)_r = B.centralizerTorusFiltration hZ r`, derived from the `K`-level `Z`-component
formula `KPLocalCorootComponentStatement` (KP Proposition 7.1.1 over `K`, Task 5911).
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Geometry.Building.MaximalUnramified.BuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))} [IsAffineHom H.X.hom]
  (B : BuildingData F H) (hZ : IsTorus B.centralizer.Z)

/-- Clause 1 of KP Lemma 7.2.3 over `K` (commutator friendliness of `Z(K)_r`), assuming the
`K`-level coroot formula. -/
theorem centralizerTorusFiltration_isCommutatorFriendly_of_coroot
    (hcor : KPLocalCorootComponentStatement.{u}) :
    ∀ (x : B.Apartment) (a : relativeRoots B.i) (u u' : rationalPoints H),
      u ∈ B.rootGroup a.1 → u ≠ 1 → u' ∈ B.rootGroup (-a.1) → u' ≠ 1 →
      ∀ r : ℝ≥0, 0 < r → (((r : ℝ) : WithTop ℝ) = x.val a.1 u + x.val (-a.1) u') →
      ∀ (v' v : rationalPoints H) (z : rationalPoints B.centralizer.Z),
        v' ∈ B.rootGroup (-a.1) → v ∈ B.rootGroup a.1 →
        u'⁻¹ * u * u' * u⁻¹ = v' * rationalPoints.map B.centralizer.j z * v →
        z ∈ B.centralizerTorusFiltration hZ r := by
  intro x a u u' hu hu1 hu' hu1' r hr hdepth v' v z hv' hv hcomm
  obtain ⟨Ta, _, hTa, hind, f, hf⟩ := hcor F H B hZ a
  obtain ⟨c, rfl, hc⟩ := hf x u u' hu hu1 hu' hu1' r hr hdepth v' v z hv' hv hcomm
  have hcmem : c ∈ localTorusFiltration F Ta hTa r :=
    (mem_localTorusFiltration_of_induced F Ta hTa hind hr c).mpr hc
  exact map_localTorusFiltration_le F Ta hTa hZ f r ⟨c, hcmem, rfl⟩

end Langlands.Geometry.Building.MaximalUnramified.BuildingData
