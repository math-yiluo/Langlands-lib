import Langlands.Global.AdelicLocalFactorUnitsStatement

/-! # Open units in actual adelic-level local factors -/

noncomputable section

universe u

open Topology

namespace Langlands.Global

/-- The existing unit topology on an open subring agrees with the subspace
unit topology, and the units are open. -/
theorem isOpenUnits_openSubring {B : Type u} [CommRing B]
    [TopologicalSpace B] [IsOpenUnits B] (A : Subring B)
    (hA : IsOpen (A : Set B)) : IsOpenUnits A := by
  let f : A →* B := A.subtype.toMonoidHom
  have hf : IsEmbedding f := IsEmbedding.subtypeVal
  have hrange : Set.range (Units.map f) = (A.toSubmonoid.units : Set Bˣ) := by
    ext b
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a.val.property, a.inv.property⟩
    · intro hb
      let a : Aˣ := ⟨⟨b.val, hb.1⟩, ⟨b.inv, hb.2⟩,
        Subtype.ext b.val_inv, Subtype.ext b.inv_val⟩
      exact ⟨a, Units.ext rfl⟩
  have hfu : IsOpenEmbedding (Units.map f) :=
    ⟨hf.units_map, hrange ▸ A.toSubmonoid.isOpen_units hA⟩
  refine ⟨IsOpenEmbedding.of_comp (Units.val : Aˣ → A)
    hA.isOpenEmbedding_subtypeVal ?_⟩
  exact (IsOpenUnits.isOpenEmbedding_unitsVal (M := B)).comp hfu

/-- Every actual local factor has open units and continuous inversion on units. -/
theorem adelicLocalFactorUnits : AdelicLocalFactorUnitsStatement.{u} := by
  constructor
  · intro k F _ _ _ S i
    cases i with
    | inl v => exact inferInstanceAs (IsOpenUnits (curvePlaceCompletion v.1))
    | inr v =>
      exact isOpenUnits_openSubring (curvePlaceCompletionIntegers v.1).toSubring
        (Valued.isOpen_valuationSubring (curvePlaceCompletion v.1))
  · intro K _ _ S i
    cases i with
    | inl v => exact inferInstanceAs (IsOpenUnits (InfiniteCompletion K v))
    | inr j =>
      cases j with
      | inl v => exact inferInstanceAs (IsOpenUnits (FiniteCompletion K v.1))
      | inr v =>
        exact isOpenUnits_openSubring (v.1.adicCompletionIntegers K).toSubring
          (Valued.isOpen_valuationSubring (FiniteCompletion K v.1))

end Langlands.Global
