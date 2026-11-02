import Langlands.AlgebraicGeometry.RelativeProjectiveSpace.GlobalLinearAction
import Mathlib.AlgebraicGeometry.RelativeGluing

/-! # Gluing relative projective schemes by coordinate cocycles -/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.RelativeProjectiveSpace

universe u

namespace Langlands.AlgebraicGeometry.ProjectiveBundle

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Scheme.{u}} (n : ℕ) (𝒰 : S.OpenCover)
  [Category* 𝒰.I₀] [𝒰.LocallyDirected]

/-- Invertible coordinate changes, with coefficients on the source chart,
satisfying the restriction cocycle law on a locally directed open cover. -/
structure CoordinateCocycle where
  transition {i j : 𝒰.I₀} (hij : i ⟶ j) :
    (Fin (n + 1) → Γ(𝒰.X i, ⊤)) ≃ₗ[Γ(𝒰.X i, ⊤)] (Fin (n + 1) → Γ(𝒰.X i, ⊤))
  transition_id (i : 𝒰.I₀) :
    transition (𝟙 i) = LinearEquiv.refl Γ(𝒰.X i, ⊤) _
  transition_comp {i j k : 𝒰.I₀} (hij : i ⟶ j) (hjk : j ⟶ k) :
    transition (hij ≫ hjk) =
      (transition hij).trans (coordinatePullback n (𝒰.trans hij) (transition hjk))

namespace CoordinateCocycle

variable {n 𝒰} (d : CoordinateCocycle n 𝒰)

/-- The actual diagram of relative projective charts and their twisted restriction maps. -/
def chartFunctor : 𝒰.I₀ ⥤ Scheme.{u} where
  obj i := RelativeProjectiveSpace (𝒰.X i) n
  map hij := globalLinearAction n (d.transition hij) ≫ map n (𝒰.trans hij)
  map_id i := by
    simp [d.transition_id]
  map_comp hij hjk := by
    rw [d.transition_comp, 𝒰.trans_comp, map_comp, ← globalLinearAction_comp]
    simp only [Category.assoc, map_globalLinearAction_assoc]

@[reassoc (attr := simp)]
lemma chartFunctor_map_toBase {i j : 𝒰.I₀} (hij : i ⟶ j) :
    d.chartFunctor.map hij ≫ toBase (𝒰.X j) n =
      toBase (𝒰.X i) n ≫ 𝒰.trans hij := by
  simp [chartFunctor]

/-- Twisting a relative projective restriction by an automorphism keeps the square Cartesian. -/
lemma isPullback_chartFunctor_map {i j : 𝒰.I₀} (hij : i ⟶ j) :
    IsPullback (toBase (𝒰.X i) n) (d.chartFunctor.map hij)
      (𝒰.trans hij) (toBase (𝒰.X j) n) := by
  refine (isPullback_map n (𝒰.trans hij)).of_iso'
    (globalLinearActionIso n (d.transition hij)) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ?_ ?_ ?_ ?_
  · simp
  · simp [chartFunctor]
  · simp
  · simp

/-- The coordinate cocycle gives actual equifibered gluing data over the cover. -/
def relativeGluingData : Scheme.Cover.RelativeGluingData 𝒰 where
  functor := d.chartFunctor
  natTrans :=
    { app i := toBase (𝒰.X i) n
      naturality hij := by
        simp }
  equifibered := by
    intro i j hij
    exact (d.isPullback_chartFunctor_map hij).flip

variable [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀]

/-- The scheme obtained by gluing actual projective charts using the coordinate cocycle. -/
def scheme : Scheme.{u} :=
  d.relativeGluingData.glued

/-- The structure morphism of the glued scheme. -/
def toBase : d.scheme ⟶ S :=
  d.relativeGluingData.toBase

/-- The open immersion from the projective chart over a member of the base cover. -/
def chart (i : 𝒰.I₀) : RelativeProjectiveSpace (𝒰.X i) n ⟶ d.scheme :=
  colimit.ι d.relativeGluingData.functor i

instance (i : 𝒰.I₀) : IsOpenImmersion (d.chart i) := by
  exact inferInstanceAs
    (IsOpenImmersion (d.relativeGluingData.cover.f i))

@[reassoc (attr := simp)]
lemma chart_toBase (i : 𝒰.I₀) :
    d.chart i ≫ d.toBase = RelativeProjectiveSpace.toBase (𝒰.X i) n ≫ 𝒰.f i := by
  exact d.relativeGluingData.ι_toBase i

@[reassoc (attr := simp)]
lemma transition_chart {i j : 𝒰.I₀} (hij : i ⟶ j) :
    globalLinearAction n (d.transition hij) ≫ map n (𝒰.trans hij) ≫ d.chart j =
      d.chart i := by
  exact colimit.w d.relativeGluingData.functor hij

/-- Each projective chart is exactly the inverse image of its base-cover member. -/
lemma isPullback_chart (i : 𝒰.I₀) :
    IsPullback (RelativeProjectiveSpace.toBase (𝒰.X i) n) (d.chart i) (𝒰.f i) d.toBase :=
  d.relativeGluingData.isPullback_natTrans_ι_toBase i

/-- The cover of the glued scheme by the given relative projective charts. -/
def openCover : d.scheme.OpenCover :=
  d.relativeGluingData.cover

end CoordinateCocycle

end Langlands.AlgebraicGeometry.ProjectiveBundle
