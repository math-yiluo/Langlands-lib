import Langlands.ClassFieldTheory.Local.AbsoluteReciprocityStatement
import Langlands.ClassFieldTheory.Local.WeilReciprocityStatement
import Langlands.ClassFieldTheory.Local.ProfiniteReciprocityCompletionProof
import Langlands.LocalFactor.Ramification.Herbrand.AbsoluteStatement
import Langlands.VirtualRepresentation.Weil.Ramification
import Langlands.LocalFactor.RankOne
import Langlands.LocalFactor.DeligneHenniartStatement
import Langlands.ClassFieldTheory.Local.CommonClosureGeometricStatement
import Langlands.ClassFieldTheory.Local.FiniteConductorStatement
import Langlands.HarmonicAnalysis.ConductorTransport

/-! # Upper ramification groups of the local Weil group and unit levels -/

noncomputable section

universe uF

namespace Langlands.LocalFactor.NonabelianSystem.DeligneHenniart

open Weil.Local LocalClassField VirtualRepresentation.LocalWeil.Ramification
open Ramification.Padic CommonClosure

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- After the Galois map of a Weil candidate, reciprocity on the local Weil
group is the abelianized projection to the absolute Galois group. -/
theorem candidateGaloisHom_reciprocityUnits (e : RankOne.ReciprocityCandidate F)
    (w : localWeilGroup F) :
    candidateGaloisHom F.canonicalTopologicalData (localResidueDegree F) e
        (RankOne.reciprocityUnits F e w) =
      localAbelianGaloisProjection F (localProjection F w) := by
  let := F.canonicalTopologicalData.topology
  change WeilQuotients.toGroupAbelianization (localResidueDegree F)
      (e.symm (e (WeilQuotients.projection (localResidueDegree F) w))) = _
  rw [e.symm_apply_apply]
  rfl

/-- Every element of absolute inertia is the Galois projection of a local
Weil element, namely of its degree-zero inclusion. -/
theorem absoluteInertia_le_range_localProjection :
    F.absoluteInertia F.canonicalTopologicalData ≤
      (localProjection F).toMonoidHom.range := by
  intro σ hσ
  exact ⟨localInertiaInclusion F ⟨σ, hσ⟩, rfl⟩

/-- For a geometric Weil reciprocity candidate, the upper ramification group
of index `s ≥ 0` of the local Weil group maps onto the unit level `⌈s⌉`.
The real-index unit images and the inertia comparison are hypotheses. -/
theorem upperGroup_map_reciprocityUnits
    (hreal : AbsoluteReciprocityRealUnitImages.{uF})
    (hinert : AbsoluteUpperInertia F F.canonicalTopologicalData)
    (e : RankOne.ReciprocityCandidate F)
    (he : GeometricWeilReciprocityRelation F F.canonicalTopologicalData e)
    {s : ℝ} (hs : 0 ≤ s) :
    letI := F.canonicalTopologicalData.topology
    (upperGroup F s).map (RankOne.reciprocityUnits F e).toMonoidHom =
      F.canonicalTopologicalData.unitFiltration ⌈s⌉₊ := by
  let := F.canonicalTopologicalData.topology
  set r := candidateGaloisHom F.canonicalTopologicalData (localResidueDegree F) e
  have hr := he.2
  have hinj : Function.Injective r :=
    (profiniteReciprocityCompletion p F F.canonicalTopologicalData r hr).1
  have hU := hreal p F F.canonicalTopologicalData r hr s hs
  ext u
  constructor
  · rintro ⟨w, hw, rfl⟩
    have h1 : r (RankOne.reciprocityUnits F e w) ∈
        localAbelianUpperRamificationGroup F s := by
      rw [candidateGaloisHom_reciprocityUnits]
      exact ⟨_, hw, rfl⟩
    rw [← hU] at h1
    obtain ⟨u, hu, hru⟩ := h1
    have heq : u = RankOne.reciprocityUnits F e w := hinj hru
    change RankOne.reciprocityUnits F e w ∈ _
    rwa [← heq]
  · intro hu
    have h1 : r u ∈ localAbelianUpperRamificationGroup F s := by
      rw [← hU]
      exact ⟨u, hu, rfl⟩
    obtain ⟨σ, hσ, hπ⟩ := h1
    have hσ0 : σ ∈ F.absoluteInertia F.canonicalTopologicalData := by
      rw [← hinert]
      exact absoluteUpperRamificationGroup_antitone F hs hσ
    obtain ⟨w, hw⟩ := absoluteInertia_le_range_localProjection F hσ0
    refine ⟨w, ?_, ?_⟩
    · change localProjection F w ∈ absoluteUpperRamificationGroup F s
      change localProjection F w = σ at hw
      rw [hw]
      exact hσ
    · apply hinj
      change r (RankOne.reciprocityUnits F e w) = r u
      rw [candidateGaloisHom_reciprocityUnits]
      change localProjection F w = σ at hw
      rw [hw]
      exact hπ

/-- Read through the bottom-field unit equivalence, the base component of a
common-closure family is the transported standalone candidate. -/
theorem baseFieldUnitsEquiv_reciprocityUnits (eC : ReciprocityFamily F)
    (g : weilSubgroup F (baseExtension F)) :
    Correspondence.baseFieldUnitsEquiv F (reciprocityUnits F eC (baseExtension F) g) =
      RankOne.reciprocityUnits F (Correspondence.baseReciprocityCandidate F eC) g.val :=
  (Correspondence.baseReciprocityCandidate_spec F eC).units_eq F g

/-- The bottom-field unit equivalence preserves and reflects every principal
unit level. -/
theorem mem_basePrincipalUnits_iff (n : ℕ) (u : (baseExtension F).fieldˣ) :
    Correspondence.baseFieldUnitsEquiv F u ∈ F.canonicalTopologicalData.principalUnits n ↔
      u ∈ (fieldData F (baseExtension F)).principalUnits n :=
  PadicField.ConductorTransport.mem_principalUnits_map_iff
    ((baseExtension F).asPadicField (p := p)) F (Correspondence.baseFieldPadicEquiv F) n u

/-- Clause (1) of the common-closure geometricity statement for the
transported base component of a normalized family. -/
theorem geometric_baseReciprocityCandidate
    (hgeo : CommonClosureGeometricStatement.{uF, uF})
    (eC : ReciprocityFamily F) (heC : NormalizedReciprocity F eC) :
    GeometricWeilReciprocityRelation F F.canonicalTopologicalData
      (Correspondence.baseReciprocityCandidate F eC) :=
  (hgeo p F eC heC).1 _ (Correspondence.baseReciprocityCandidate_spec F eC)

/-- The upper ramification group of real index `s` of the local Weil group,
viewed in the bottom Weil subgroup `weilSubgroup F (baseExtension F)`: its
pullback under the bottom inclusion. -/
def baseUpperGroup (s : ℝ) : Subgroup (weilSubgroup F (baseExtension F)) :=
  (upperGroup F s).comap (baseWeilInclusion F).toMonoidHom

theorem mem_baseUpperGroup {s : ℝ} (g : weilSubgroup F (baseExtension F)) :
    g ∈ baseUpperGroup F s ↔ g.val ∈ upperGroup F s :=
  Iff.rfl

/-- On the base component of a common-closure family whose transported base
candidate is geometric, the upper group of index `s ≥ 0`, viewed in the bottom
Weil subgroup, maps onto the principal units of level `⌈s⌉`. -/
theorem baseUpperGroup_map_reciprocityUnits
    (hreal : AbsoluteReciprocityRealUnitImages.{uF})
    (hinert : AbsoluteUpperInertia F F.canonicalTopologicalData)
    (hcmp : UnitFiltrationComparison.{uF})
    (eC : ReciprocityFamily F)
    (he : GeometricWeilReciprocityRelation F F.canonicalTopologicalData
      (Correspondence.baseReciprocityCandidate F eC))
    {s : ℝ} (hs : 0 ≤ s) :
    letI := (fieldData F (baseExtension F)).topology
    (baseUpperGroup F s).map (reciprocityUnits F eC (baseExtension F)).toMonoidHom =
      (fieldData F (baseExtension F)).principalUnits ⌈s⌉₊ := by
  let := (fieldData F (baseExtension F)).topology
  have hW := upperGroup_map_reciprocityUnits F hreal hinert _ he hs
  rw [hcmp p F F.canonicalTopologicalData] at hW
  ext u
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [← mem_basePrincipalUnits_iff]
    change Correspondence.baseFieldUnitsEquiv F (reciprocityUnits F eC (baseExtension F) g) ∈ _
    rw [baseFieldUnitsEquiv_reciprocityUnits, ← hW]
    exact ⟨g.val, hg, rfl⟩
  · intro hu
    rw [← mem_basePrincipalUnits_iff, ← hW] at hu
    obtain ⟨w, hw, hwu⟩ := hu
    have hmem : w ∈ weilSubgroup F (baseExtension F) := by
      rw [baseWeil_eq_top]
      trivial
    refine ⟨⟨w, hmem⟩, hw, ?_⟩
    have key := (baseFieldUnitsEquiv_reciprocityUnits F eC ⟨w, hmem⟩).trans hwu
    let : TopologicalSpace (Correspondence.baseExtension F).field :=
      (fieldData F (Correspondence.baseExtension F)).topology
    let : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
    exact (Correspondence.baseFieldUnitsEquiv F).injective key

end Langlands.LocalFactor.NonabelianSystem.DeligneHenniart
