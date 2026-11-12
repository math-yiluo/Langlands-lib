import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceLimitFlatnessDescent
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceLimitPureFibreDimensionDescent
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceBaseChangeMorphismComparison
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpacePointsIsoTransport

/-! # Reduction of the flatness-dimension theorem to connected-fibre descent -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Pure fibre dimension transports through an isomorphism of arrows. -/
theorem HasPureFibreDimension.of_arrow_iso {d : ℕ}
    {X Y X' Y' : AlgebraicSpace S} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (eX : X ≅ X') (eY : Y ≅ Y') (w : eX.hom ≫ f' = f ≫ eY.hom)
    (hf : HasPureFibreDimension d f) : HasPureFibreDimension d f' := by
  obtain ⟨A, B, a, b, φ, ha, hs, hb, hφl, hφp, hw⟩ := hf
  refine ⟨A, B, a ≫ hom eX.hom, b ≫ hom eY.hom, φ,
    ha.comp_iso ((forgetToPresheaf S).mapIso eX),
    hs.comp_iso ((forgetToPresheaf S).mapIso eX),
    hb.comp_iso ((forgetToPresheaf S).mapIso eY), hφl, hφp, ?_⟩
  have ww := (forgetToPresheaf S).congr_map w
  change hom eX.hom ≫ hom f' = hom f ≫ hom eY.hom at ww
  rw [Category.assoc, ww, ← Category.assoc, hw, Category.assoc]

/-- Once geometrically connected fibres descend, flatness and the conjunction
with every pure fibre dimension follow under exactly the original hypotheses. -/
def SpaceLimitFlatnessDimensionReductionStatement : Prop :=
  SpaceLimitPropertyDescends.{u} (fun f => HasGeometricallyConnectedFibres f) →
    SpaceLimitFlatnessDimensionDescentStatement.{u}

/-- First descend pure dimension, then apply connected-fibre descent to that
stage model, preserving pure dimension at the resulting incoming stage. -/
theorem spaceLimitFlatnessDimensionReduction :
    SpaceLimitFlatnessDimensionReductionStatement.{u} := by
  intro hconnected
  have : MorphismProperty.IsStableUnderBaseChange
      (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.inf
  refine ⟨spaceLimitFlatnessDescends, ?_⟩
  intro d I _ _ D _ c hc i X Y hXqs hX hYqs hY f
  have hdim := spaceLimitPureFibreDimensionDescends d I D c hc i X Y hXqs hX hYqs hY f
  have hconn := hconnected I D c hc i X Y hXqs hX hYqs hY f
  constructor
  · rintro ⟨hg, hp⟩
    obtain ⟨j, r, hj⟩ := hdim.mp hp
    let e := baseChangeCompNatIso (D.map r) (c.π.app j) (c.π.app i) (c.w r)
    have hg' : HasGeometricallyConnectedFibres
        (baseChangeMap (c.π.app j) (baseChangeMap (D.map r) f)) :=
      HasGeometricallyConnectedFibres.of_arrow_iso (e.app X).symm (e.app Y).symm
        (e.inv.naturality f).symm hg
    have hconn' := hconnected I D c hc j (baseChange (D.map r) X) (baseChange (D.map r) Y)
      (hXqs.baseChange (g := D.map r)) (hX.baseChange (g := D.map r))
      (hYqs.baseChange (g := D.map r)) (hY.baseChange (g := D.map r))
      (baseChangeMap (D.map r) f)
    obtain ⟨k, s, hk⟩ := hconn'.mp hg'
    let e' := baseChangeCompNatIso (D.map r) (D.map s) (D.map (s ≫ r))
      (D.map_comp s r).symm
    exact ⟨k, s ≫ r,
      HasGeometricallyConnectedFibres.of_arrow_iso (e'.app X) (e'.app Y)
        (e'.hom.naturality f).symm hk,
      HasPureFibreDimension.of_arrow_iso (e'.app X) (e'.app Y)
        (e'.hom.naturality f).symm (hj.baseChangeMap (D.map s))⟩
  · rintro ⟨j, r, hg, hp⟩
    exact ⟨hconn.mpr ⟨j, r, hg⟩, hdim.mpr ⟨j, r, hp⟩⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace
