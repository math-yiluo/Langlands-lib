import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.Geometry.Building.MaximalUnramifiedBuildingData

/-! # Chamber stabilizers of simply connected groups over the maximal unramified extension

For a simply connected group `G` over the maximal unramified extension
`K = inertiaFixedField F` of a nonarchimedean local field `F` and supplied building data `C`
of `G`, an element of `G(K)` stabilizing a chamber of the reduced building of `C` fixes it
pointwise (KP 4.1.12(1) and Remark 4.1.13, cf. 9.3.26).
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

namespace IntegerValuationBuildingData

variable {k : Type u} [Field k] {v : Valuation k (WithZero (Multiplicative ℤ))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (B : IntegerValuationBuildingData v G)

/-- The pointwise fixer of a subset of the reduced building stabilizes it. -/
theorem smul_image_eq_of_mem_pointwiseFixer {Y : Set B.ReducedBuilding}
    {g : rationalPoints G} (hg : g ∈ B.pointwiseFixer Y) : (g • ·) '' Y = Y := by
  rw [IntegerValuationBuildingData.pointwiseFixer, KPApartmentData.mem_pointwiseFixer] at hg
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    show g • z ∈ Y
    rw [hg z hz]
    exact hz
  · intro hy
    exact ⟨y, hy, hg y hy⟩

end IntegerValuationBuildingData

namespace MaximalUnramified

/-- **Chamber stabilizers fix chambers pointwise in the simply connected case**
(Kaletha–Prasad 4.1.12(1) and Remark 4.1.13 over `K`, cf. 9.3.26). Let `F` be a
nonarchimedean local field, `K = inertiaFixedField F` its maximal unramified extension and
`G` a simply connected `K`-group. For any supplied building data `C` of `G` for the
normalized valuation of `K`, any chamber `Y` of the reduced building of `C` and any
`g ∈ G(K)` with `g · Y = Y`, the element `g` fixes `Y` pointwise. -/
def SimplyConnectedChamberStabilizerStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))) [IsAffineHom G.X.hom],
    IsSimplyConnected G →
    ∀ (C : BuildingData F G) (Y : Set C.ReducedBuilding), C.IsChamber Y →
      ∀ g : rationalPoints G, (g • ·) '' Y = Y → g ∈ C.pointwiseFixer Y

/-- Under the statement, the stabilizer of a chamber is exactly its pointwise fixer. -/
theorem smul_image_eq_iff_mem_pointwiseFixer
    (h : SimplyConnectedChamberStabilizerStatement.{u})
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))} [IsAffineHom G.X.hom]
    (hG : IsSimplyConnected G) (C : BuildingData F G)
    {Y : Set C.ReducedBuilding} (hY : C.IsChamber Y) (g : rationalPoints G) :
    (g • ·) '' Y = Y ↔ g ∈ C.pointwiseFixer Y :=
  ⟨h F G hG C Y hY g, C.smul_image_eq_of_mem_pointwiseFixer⟩

end MaximalUnramified

end Langlands.Geometry.Building
