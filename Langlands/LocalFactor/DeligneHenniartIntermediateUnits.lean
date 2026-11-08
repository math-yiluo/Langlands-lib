import Langlands.LocalFactor.DeligneHenniartUpperUnits
import Langlands.LocalFactor.CommonClosureIntermediateWeil

/-! # Unit levels at an intermediate field of the common closure -/

noncomputable section

universe uF

namespace Langlands.LocalFactor.NonabelianSystem.DeligneHenniart

open Weil.Local LocalClassField VirtualRepresentation.LocalWeil.Ramification
open Ramification.Padic CommonClosure

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The component at `E` of a common-closure family, read on the standalone local
Weil group of `E` through the published identification `intermediateWeilEquiv`. -/
def intermediateReciprocityCandidate (eC : ReciprocityFamily F) (E : Extension F) :
    RankOne.ReciprocityCandidate (E.asPadicField (p := p)) := by
  letI := (fieldData F E).topology
  exact (abelianizationCongr (intermediateWeilEquiv F E)).trans (eC E)

theorem reciprocityUnits_intermediateReciprocityCandidate (eC : ReciprocityFamily F)
    (E : Extension F) (w : localWeilGroup (E.asPadicField (p := p))) :
    RankOne.reciprocityUnits (E.asPadicField (p := p)) (intermediateReciprocityCandidate F eC E) w =
      reciprocityUnits F eC E (intermediateWeilEquiv F E w) :=
  rfl

/-- Geometricity of the intermediate components of every normalized common-closure
family. This is a proposition only; it is not proved here. -/
def IntermediateGeometricStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (eC : ReciprocityFamily F),
    NormalizedReciprocity F eC → ∀ E : Extension F,
      GeometricWeilReciprocityRelation (E.asPadicField (p := p))
        (E.asPadicField (p := p)).canonicalTopologicalData
        (intermediateReciprocityCandidate F eC E)

/-- The upper ramification group of the standalone Weil group of `E`, of real index
`s`, carried into the Weil subgroup `W_E` of the common closure. -/
def intermediateUpperGroup (E : Extension F) (s : ℝ) : Subgroup (weilSubgroup F E) :=
  (upperGroup (E.asPadicField (p := p)) s).map (intermediateWeilEquiv F E).toMonoidHom

theorem mem_intermediateUpperGroup (E : Extension F) {s : ℝ} (g : weilSubgroup F E) :
    g ∈ intermediateUpperGroup F E s ↔
      (intermediateWeilEquiv F E).symm g ∈ upperGroup (E.asPadicField (p := p)) s := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    change (intermediateWeilEquiv F E).symm (intermediateWeilEquiv F E w) ∈ _
    rwa [ContinuousMulEquiv.symm_apply_apply]
  · intro h
    exact ⟨_, h, (intermediateWeilEquiv F E).apply_symm_apply g⟩

/-- At an intermediate field whose component is geometric, the carried upper group of
index `s ≥ 0` maps onto the principal units of level `⌈s⌉` of that field. -/
theorem intermediateUpperGroup_map_reciprocityUnits
    (hreal : AbsoluteReciprocityRealUnitImages.{uF})
    (hcmp : UnitFiltrationComparison.{uF})
    (eC : ReciprocityFamily F) (E : Extension F)
    (hinert : AbsoluteUpperInertia (E.asPadicField (p := p))
      (E.asPadicField (p := p)).canonicalTopologicalData)
    (he : GeometricWeilReciprocityRelation (E.asPadicField (p := p))
      (E.asPadicField (p := p)).canonicalTopologicalData
      (intermediateReciprocityCandidate F eC E))
    {s : ℝ} (hs : 0 ≤ s) :
    letI := (fieldData F E).topology
    (intermediateUpperGroup F E s).map (reciprocityUnits F eC E).toMonoidHom =
      (fieldData F E).principalUnits ⌈s⌉₊ := by
  let := (fieldData F E).topology
  have hW := upperGroup_map_reciprocityUnits (E.asPadicField (p := p)) hreal hinert _ he hs
  rw [hcmp p (E.asPadicField (p := p)) (E.asPadicField (p := p)).canonicalTopologicalData] at hW
  rw [intermediateUpperGroup, Subgroup.map_map]
  exact hW

end Langlands.LocalFactor.NonabelianSystem.DeligneHenniart
