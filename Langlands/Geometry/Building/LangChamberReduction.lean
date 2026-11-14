import Langlands.Geometry.Building.IntegerValuationBuildingData
import Langlands.GroupTheory.LangFixedOrbit
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic

/-! # Lang correction for chambers with a specified closure point -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.IntegerValuationBuildingData

variable {k : Type u} [Field k]
  {v : Valuation k (WithZero (Multiplicative ℤ))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (B : IntegerValuationBuildingData v G)

/-- A chamber presentation retaining an apartment point in its facet closure
whose image is the specified building point. -/
def HasChamberClosurePresentation (Y : Set B.ReducedBuilding)
    (y : B.ReducedBuilding) : Prop :=
  ∃ (g : rationalPoints G) (x₀ x : B.Apartment),
    (∀ ψ ∈ B.affineRoots, ψ x₀ ≠ 0) ∧
    Y = (fun z => g • B.apartmentMap z) '' AffineRootSystem.facet B.affineRoots x₀ ∧
    x ∈ AffineRootSystem.facetClosure B.affineRoots x₀ ∧
    g • B.apartmentMap x = y

variable {B}

/-- A closure presentation gives chamberhood with the same generic facet. -/
theorem HasChamberClosurePresentation.isChamber
    {Y : Set B.ReducedBuilding} {y : B.ReducedBuilding}
    (hY : B.HasChamberClosurePresentation Y y) : B.IsChamber Y := by
  obtain ⟨g, x₀, x, hgeneric, hY, hx, hy⟩ := hY
  exact ⟨g, AffineRootSystem.facet B.affineRoots x₀, ⟨x₀, hgeneric, rfl⟩, hY⟩

/-- Translating the presentation translates its specified closure point. -/
theorem HasChamberClosurePresentation.smul
    {Y : Set B.ReducedBuilding} {y : B.ReducedBuilding}
    (hY : B.HasChamberClosurePresentation Y y) (a : rationalPoints G) :
    B.HasChamberClosurePresentation ((a • ·) '' Y) (a • y) := by
  obtain ⟨g, x₀, x, hgeneric, rfl, hx, hy⟩ := hY
  refine ⟨a * g, x₀, x, hgeneric, ?_, hx, ?_⟩
  · rw [Set.image_image]
    simp only [mul_smul]
  · rw [mul_smul, hy]

/-- An equivariant quotient Lang equation supplies a stable chamber while
retaining its concrete closure presentation through a fixed point. -/
theorem exists_stable_chamber_of_quotient_lang
    {Q : Type v} [Group Q] (P : Subgroup (rationalPoints G))
    (q : P →* Q) (hq : Function.Surjective q)
    (θ : P → P) (F : Q → Q) (τ : B.ReducedBuilding → B.ReducedBuilding)
    (hcompat : ∀ g : P, q (θ g) = F (q g))
    (hsemi : ∀ (g : P) (z : B.ReducedBuilding),
      τ ((g : rationalPoints G) • z) = (θ g : rationalPoints G) • τ z)
    (hlang : Langlands.GroupTheory.LangSurjective F)
    (y : B.ReducedBuilding) (hfix : P ≤ B.fixer y)
    (Y₀ : Set B.ReducedBuilding) (hY₀ : B.HasChamberClosurePresentation Y₀ y)
    (hker : ∀ g : P, q g = 1 → ((g : rationalPoints G) • ·) '' Y₀ = Y₀)
    (h : P) (hτ : τ '' Y₀ = ((h : rationalPoints G) • ·) '' Y₀) :
    ∃ Y : Set B.ReducedBuilding,
      B.IsChamber Y ∧ τ '' Y = Y ∧ B.HasChamberClosurePresentation Y y := by
  have hsemiSet : ∀ (g : P) (Y : Set B.ReducedBuilding),
      τ '' (g • Y) = θ g • (τ '' Y) := by
    intro g Y
    change τ '' (((g : rationalPoints G) • ·) '' Y) =
      ((θ g : rationalPoints G) • ·) '' (τ '' Y)
    rw [Set.image_image, Set.image_image]
    congr 1
    funext z
    exact hsemi g z
  obtain ⟨g, hg⟩ := Langlands.GroupTheory.exists_fixed_in_orbit_of_quotient_lang
    q hq θ F (fun Y => τ '' Y) hcompat hsemiSet hlang Y₀ hker h hτ
  have hgy : (g : rationalPoints G) • y = y := B.mem_fixer.mp (hfix g.property)
  have hpres : B.HasChamberClosurePresentation
      (((g : rationalPoints G) • ·) '' Y₀) y := by
    simpa only [hgy] using hY₀.smul (g : rationalPoints G)
  exact ⟨_, hpres.isChamber, hg, hpres⟩

end Langlands.Geometry.Building.IntegerValuationBuildingData
