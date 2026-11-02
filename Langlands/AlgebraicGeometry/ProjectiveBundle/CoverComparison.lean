import Langlands.AlgebraicGeometry.ProjectiveBundle.CocycleGluing
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-! # Comparison with Cartesian projective atlases -/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.RelativeProjectiveSpace

universe u

namespace Langlands.AlgebraicGeometry.ProjectiveBundle

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CoordinateCocycle

variable {S : Scheme.{u}} {n : ℕ} {𝒰 : S.OpenCover}
  [Category* 𝒰.I₀] [𝒰.LocallyDirected] [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀]
  (d : CoordinateCocycle n 𝒰)

/-- An actual Cartesian atlas with the specified projective transition maps. -/
structure CartesianAtlas (X : Scheme.{u}) (p : X ⟶ S) where
  chart (i : 𝒰.I₀) : RelativeProjectiveSpace (𝒰.X i) n ⟶ X
  compatible {i j : 𝒰.I₀} (hij : i ⟶ j) :
    d.chartFunctor.map hij ≫ chart j = chart i
  cartesian (i : 𝒰.I₀) :
    IsPullback (RelativeProjectiveSpace.toBase (𝒰.X i) n) (chart i) (𝒰.f i) p

namespace CartesianAtlas

variable {d} {X : Scheme.{u}} {p : X ⟶ S} (a : d.CartesianAtlas X p)

/-- The morphism from the actual glued projective scheme into the atlas. -/
def desc : d.scheme ⟶ X :=
  colimit.desc d.relativeGluingData.functor
    { pt := X
      ι := { app := a.chart
             naturality := fun i j hij => by
               simpa [relativeGluingData] using a.compatible hij } }

@[reassoc (attr := simp)]
lemma chart_desc (i : 𝒰.I₀) : d.chart i ≫ a.desc = a.chart i :=
  colimit.ι_desc _ i

@[reassoc (attr := simp)]
lemma desc_toBase : a.desc ≫ p = d.toBase := by
  apply colimit.hom_ext
  intro i
  change d.chart i ≫ a.desc ≫ p = d.chart i ≫ d.toBase
  rw [chart_desc_assoc, d.chart_toBase]
  exact (a.cartesian i).w.symm

instance (i : 𝒰.I₀) : IsOpenImmersion (a.chart i) := by
  apply MorphismProperty.of_isPullback (a.cartesian i)
  infer_instance

/-- Cartesian atlas charts cover because their base opens cover. -/
def openCover : X.OpenCover where
  I₀ := 𝒰.I₀
  X i := RelativeProjectiveSpace (𝒰.X i) n
  f := a.chart
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, fun i => inferInstance⟩
    obtain ⟨i, y, hy⟩ := 𝒰.exists_eq (p x)
    obtain ⟨z, _, hz⟩ := Scheme.exists_preimage_of_isPullback (a.cartesian i) y x hy
    exact ⟨i, z, hz⟩

/-- The descended morphism is Cartesian with the identity on each atlas chart. -/
lemma isPullback_desc (i : 𝒰.I₀) :
    IsPullback (d.chart i) (𝟙 _) a.desc (a.chart i) := by
  apply IsPullback.of_bot (h₂₁ := a.chart i)
    (v₂₁ := RelativeProjectiveSpace.toBase (𝒰.X i) n) (v₂₂ := p)
  · simpa using (d.isPullback_chart i).flip
  · simp
  · exact (a.cartesian i).flip

instance : IsIso a.desc := by
  apply IsZariskiLocalAtTarget.of_openCover (P := MorphismProperty.isomorphisms Scheme)
    a.openCover
  intro i
  change IsIso (pullback.snd a.desc (a.chart i))
  rw [← (a.isPullback_desc i).isoPullback_inv_snd]
  infer_instance

/-- The actual scheme isomorphism comparing the gluing and its Cartesian atlas. -/
def schemeIso : d.scheme ≅ X := asIso a.desc

@[reassoc (attr := simp)]
lemma schemeIso_hom_toBase : a.schemeIso.hom ≫ p = d.toBase :=
  a.desc_toBase

@[reassoc (attr := simp)]
lemma chart_schemeIso_hom (i : 𝒰.I₀) :
    d.chart i ≫ a.schemeIso.hom = a.chart i :=
  a.chart_desc i

/-- The chart equations determine the comparison uniquely. -/
lemma hom_eq (f : d.scheme ⟶ X)
    (hf : ∀ i, d.chart i ≫ f = a.chart i) : f = a.schemeIso.hom := by
  apply colimit.hom_ext
  intro i
  exact (hf i).trans (a.chart_desc i).symm

end CartesianAtlas

end CoordinateCocycle

end Langlands.AlgebraicGeometry.ProjectiveBundle
