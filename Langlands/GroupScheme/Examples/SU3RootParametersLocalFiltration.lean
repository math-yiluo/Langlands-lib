import Langlands.GroupScheme.Examples.SU3RootFiltration
import Langlands.GroupScheme.Examples.SU3RootParametersLocalDepth

/-! # Nontrivial filtration subgroups for actual quadratic local-field coordinates -/

noncomputable section

open Algebra

universe u v

namespace Langlands.GroupScheme.SU3Root

variable (F : Type u) (L : Type v) [Field F] [Field L] [Algebra F L]
  [IsQuadraticExtension F L] [Algebra.IsSeparable F L]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- The root filtration formed from the actual normalized quadratic extension valuation. -/
def quadraticFiltration (r : ℝ) : Subgroup (rationalParameters F L) :=
  Parameters.filtration (quadraticValuation F L) (quadraticValuation_bar F L) r

/-- The central filtration, as a subgroup of the actual ambient coordinate group. -/
def quadraticCentralFiltration (r : ℝ) : Subgroup (rationalParameters F L) :=
  Parameters.centralFiltration (quadraticValuation F L) (quadraticValuation_bar F L) r

theorem mem_quadraticFiltration_iff_depth (r : ℝ) (p : rationalParameters F L) :
    p ∈ quadraticFiltration F L r ↔ (r : WithTop ℝ) ≤ quadraticDepth F L p :=
  Parameters.mem_filtration_iff_depth (quadraticValuation F L)
    (quadraticValuation_bar F L) r p

theorem mem_quadraticCentralFiltration_iff_depth (r : ℝ)
    (z : Parameters.central (fieldInvolution F L)) :
    z.val ∈ quadraticCentralFiltration F L r ↔
      (r : WithTop ℝ) ≤ quadraticCentralDepth F L z :=
  Parameters.mem_centralFiltration_iff_depth (quadraticValuation F L)
    (quadraticValuation_bar F L) r z

/-- Arbitrary root and central levels contain a common nonidentity central parameter. -/
theorem exists_ne_one_mem_quadraticFiltrations (r s : ℝ) :
    ∃ p : rationalParameters F L, p ≠ 1 ∧
      p ∈ quadraticFiltration F L r ∧ p ∈ quadraticCentralFiltration F L s := by
  obtain ⟨z, hz, hr, hs⟩ := exists_central_parameter_of_depth_ge F L (max r s)
  refine ⟨z.val, (fun h => hz (Subtype.ext h)), ?_, ?_⟩
  · apply (mem_quadraticFiltration_iff_depth F L r z.val).mpr
    exact (WithTop.coe_le_coe.mpr (le_max_left r s)).trans hr
  · apply (mem_quadraticCentralFiltration_iff_depth F L s z).mpr
    exact (WithTop.coe_le_coe.mpr (le_max_right r s)).trans hs

/-- Even the intersection of independently prescribed levels is nontrivial. -/
theorem quadraticFiltration_inf_central_ne_bot (r s : ℝ) :
    quadraticFiltration F L r ⊓ quadraticCentralFiltration F L s ≠ ⊥ := by
  obtain ⟨p, hp, hr, hs⟩ := exists_ne_one_mem_quadraticFiltrations F L r s
  exact (Subgroup.nontrivial_iff_ne_bot _).mp
    ((Subgroup.nontrivial_iff_exists_ne_one _).mpr ⟨p, ⟨hr, hs⟩, hp⟩)

theorem quadraticFiltration_ne_bot (r : ℝ) : quadraticFiltration F L r ≠ ⊥ := by
  obtain ⟨p, hp, hr, _⟩ := exists_ne_one_mem_quadraticFiltrations F L r r
  exact (Subgroup.nontrivial_iff_ne_bot _).mp
    ((Subgroup.nontrivial_iff_exists_ne_one _).mpr ⟨p, hr, hp⟩)

theorem quadraticCentralFiltration_ne_bot (r : ℝ) :
    quadraticCentralFiltration F L r ≠ ⊥ := by
  obtain ⟨p, hp, _, hr⟩ := exists_ne_one_mem_quadraticFiltrations F L r r
  exact (Subgroup.nontrivial_iff_ne_bot _).mp
    ((Subgroup.nontrivial_iff_exists_ne_one _).mpr ⟨p, hr, hp⟩)

end Langlands.GroupScheme.SU3Root
