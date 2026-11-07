import Langlands.Representation.Families.RenardFamilyFixedTensorProof
import Langlands.Representation.Plancherel.UnramifiedRationalNormalizedInducedFinitenessProof
import Langlands.Topology.LocallyProfiniteProof

/-! # Flatness of smooth coefficient families -/

noncomputable section

namespace Langlands.Renard.AlgebraicFamily

universe uB uG uV

/-- Compact-open fixed modules detect flatness of a smooth coefficient family. -/
theorem flatness_iff_fixed_flat
    {B : Type uB} [CommRing B] [Algebra ℂ B]
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : Topology.IsLocallyProfinite G)
    {V : Type uV} [AddCommGroup V] [Module B V]
    (ρ : Representation B G V) (hρ : IsSmooth ρ) :
    Module.Flat B V ↔ ∀ K : OpenSubgroup G, IsCompact (K : Set G) →
      Module.Flat B (fixedVectors ρ K.toSubgroup) := by
  constructor
  · intro hflat K hK
    let := hflat
    exact Module.Flat.of_retract (fixedVectors ρ K.toSubgroup).subtype
      (coefficientFixedProjection ρ hρ K hK) (coefficientFixedProjection_comp ρ hρ K hK)
  · intro hfixed
    let : LocallyCompactSpace G := hG.locallyCompactSpace
    let : NonarchimedeanGroup G :=
      { is_nonarchimedean := fun U hU => by
          obtain ⟨K, _, hKU⟩ := (Topology.LocallyProfiniteProof.vanDantzig G).mp hG |>.2 U hU
          exact ⟨K, hKU⟩ }
    exact Plancherel.RationalNormalized.flat_of_smooth_fixed_flat ρ hρ hfixed

/-- Renard VI.8.1 Remark at all three published universes. -/
theorem flatnessCriterion : FlatnessCriterionStatement.{uB, uG, uV} := by
  intro B _ _ _ _ _ G _ _ _ hG V _ _ ρ hρ
  exact flatness_iff_fixed_flat hG ρ hρ

end Langlands.Renard.AlgebraicFamily
