import Langlands.AlgebraicGeometry.ProjectiveBundle.CocycleGluing

/-! # Changes of coordinates between glued projective schemes -/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.RelativeProjectiveSpace

universe u

namespace Langlands.AlgebraicGeometry.ProjectiveBundle

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Scheme.{u}} {n : ℕ} {𝒰 : S.OpenCover}
  [Category* 𝒰.I₀] [𝒰.LocallyDirected]

namespace CoordinateCocycle

/-- Invertible changes of chart coordinates intertwining two coordinate cocycles. -/
structure Change (d e : CoordinateCocycle n 𝒰) where
  coordinate (i : 𝒰.I₀) :
    (Fin (n + 1) → Γ(𝒰.X i, ⊤)) ≃ₗ[Γ(𝒰.X i, ⊤)] (Fin (n + 1) → Γ(𝒰.X i, ⊤))
  compatible {i j : 𝒰.I₀} (hij : i ⟶ j) :
    (d.transition hij).trans (coordinatePullback n (𝒰.trans hij) (coordinate j)) =
      (coordinate i).trans (e.transition hij)

namespace Change

variable {d e : CoordinateCocycle n 𝒰} (c : Change d e)

/-- The chartwise coordinate isomorphisms form an actual natural isomorphism. -/
def naturalIso : d.relativeGluingData.functor ≅ e.relativeGluingData.functor :=
  NatIso.ofComponents (fun i => globalLinearActionIso n (c.coordinate i)) (by
    intro i j hij
    dsimp [relativeGluingData, chartFunctor]
    rw [Category.assoc, map_globalLinearAction, ← Category.assoc,
      globalLinearAction_comp, c.compatible, ← globalLinearAction_comp]
    simp only [Category.assoc])

variable [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀]

/-- A compatible chart coordinate change induces an actual isomorphism of glued schemes. -/
def schemeIso : d.scheme ≅ e.scheme :=
  asIso (colimMap c.naturalIso.hom)

@[reassoc (attr := simp)]
lemma chart_schemeIso_hom (i : 𝒰.I₀) :
    d.chart i ≫ c.schemeIso.hom =
      globalLinearAction n (c.coordinate i) ≫ e.chart i := by
  exact ι_colimMap c.naturalIso.hom i

@[reassoc (attr := simp)]
lemma chart_schemeIso_inv (i : 𝒰.I₀) :
    e.chart i ≫ c.schemeIso.inv =
      globalLinearAction n (c.coordinate i).symm ≫ d.chart i := by
  apply (cancel_mono c.schemeIso.hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    c.chart_schemeIso_hom, ← Category.assoc, globalLinearAction_comp]
  simp

@[reassoc (attr := simp)]
lemma schemeIso_hom_toBase :
    c.schemeIso.hom ≫ e.toBase = d.toBase := by
  apply colimit.hom_ext
  intro i
  change d.chart i ≫ _ = d.chart i ≫ _
  simp

@[reassoc (attr := simp)]
lemma schemeIso_inv_toBase :
    c.schemeIso.inv ≫ d.toBase = e.toBase := by
  rw [← c.schemeIso_hom_toBase, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The chart formulas determine the glued comparison morphism uniquely. -/
lemma hom_eq (f : d.scheme ⟶ e.scheme)
    (hf : ∀ i, d.chart i ≫ f =
      globalLinearAction n (c.coordinate i) ≫ e.chart i) :
    f = c.schemeIso.hom := by
  apply colimit.hom_ext
  intro i
  exact (hf i).trans (c.chart_schemeIso_hom i).symm

end Change

end CoordinateCocycle

end Langlands.AlgebraicGeometry.ProjectiveBundle
