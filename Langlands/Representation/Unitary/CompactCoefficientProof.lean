import Langlands.Representation.Unitary.SquareIntegrableProof
import Langlands.Topology.CompactOpen.NeighborhoodBasis
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-! # Positive forms from compact coefficient norms modulo the center -/

noncomputable section

open MeasureTheory

namespace Langlands

universe uG uV

namespace UnitaryCentralCharacter

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V}

/-- Integrating compactly supported coefficient norms against inverse left
Haar measure gives an invariant positive form on the original carrier. -/
def compactCoefficientPositiveForm (c : UnitaryCentralCharacter ρ)
    (hρ : IsSmooth ρ) (hirr : Representation.IsIrreducible ρ)
    (hcoeff : ∀ (ℓ : SmoothDual ρ) (v : V),
      HasCompactSupport (c.coefficientNorm ℓ.1 v))
    (hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K) :
    InvariantPositiveForm ρ := by
  have : IsClosed (Subgroup.center G : Set G) := by
    simpa only [Set.centralizer_univ, Subgroup.coe_center] using
      (Set.isClosed_centralizer (Set.univ : Set G))
  let hexists :=
    exists_nonzero_smoothDual_of_irreducible_compact_cofinal hcofinal ρ hρ hirr
  let ℓ : SmoothDual ρ := Classical.choose hexists
  have hℓ : ℓ.1 ≠ 0 := Classical.choose_spec hexists
  let Q := G ⧸ Subgroup.center G
  let : MeasurableSpace Q := borel Q
  have : BorelSpace Q := ⟨rfl⟩
  have hL2 : ∀ v : V, MemLp (c.coefficientNorm ℓ.1 v) 2
      (Measure.haar : Measure Q).inv := fun v =>
    (c.continuous_coefficientNorm ℓ.1 v (hρ v)).memLp_of_hasCompactSupport (hcoeff ℓ v)
  exact c.coefficientProductForm hρ hirr ℓ.1 hℓ (Measure.haar : Measure Q).inv hL2

/-- The positive form proves unitarizability with compact-open cofinality. -/
theorem isUnitarizable_of_compact_coefficientNorm (c : UnitaryCentralCharacter ρ)
    (hρ : IsSmooth ρ) (hirr : Representation.IsIrreducible ρ)
    (hcoeff : ∀ (ℓ : SmoothDual ρ) (v : V),
      HasCompactSupport (c.coefficientNorm ℓ.1 v))
    (hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K) :
    IsUnitarizable ρ :=
  ⟨c.compactCoefficientPositiveForm hρ hirr hcoeff hcofinal⟩

omit [IsTopologicalGroup G] in
/-- In a locally compact nonarchimedean group compact-open cofinality follows
from the compact-open neighborhood basis. -/
theorem isUnitarizable_of_compact_coefficientNorm_of_nonarchimedean
    [NonarchimedeanGroup G] (c : UnitaryCentralCharacter ρ)
    (hρ : IsSmooth ρ) (hirr : Representation.IsIrreducible ρ)
    (hcoeff : ∀ (ℓ : SmoothDual ρ) (v : V),
      HasCompactSupport (c.coefficientNorm ℓ.1 v)) :
    IsUnitarizable ρ := by
  apply c.isUnitarizable_of_compact_coefficientNorm hρ hirr hcoeff
  intro K
  obtain ⟨L, hL, hLK⟩ := compactOpenSubgroupBasis G (K : Set G) K.mem_nhds_one
  exact ⟨L, hL, fun _ hx => hLK hx⟩

end UnitaryCentralCharacter

end Langlands
