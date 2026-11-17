import Langlands.Global.RankinSelberg.AdelicCompactRowMajorant
import Langlands.Global.RankinSelberg.AdelicSimpleRootGauge
import Langlands.Global.RankinSelberg.EqualUnfoldingKernel

/-! # Compact last-row bounds in the simple-root gauge coordinates -/

noncomputable section
universe u
open NumberField Set
open scoped Classical CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Global

local instance gaugeRowSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _

variable (F : Type u) [Field F] [NumberField F]

theorem isCompact_gaugeStandardCompact (n : ℕ) :
    IsCompact (gaugeStandardCompact F n : Set (Points F n)) := by
  change IsCompact ((GeneralLinearGroupPoints.adelicHomeomorph F n) ⁻¹'
    (PrimitiveAdelicHeight.standardCompact F n : Set (AdelicGL F n)))
  exact (GeneralLinearGroupPoints.adelicHomeomorph F n).isCompact_preimage.mpr
    (PrimitiveAdelicHeight.isCompact_standardCompact F n)

theorem lastRow_gaugeDiagonalPoint (r : ℕ) (d : Fin (r + 1) → Ideles F) :
    lastRow F r (gaugeDiagonalPoint F (r + 1) d) =
      coordinateRow F (r + 1) (Fin.last r) (d (Fin.last r) : Adeles F) :=
  lastRow_diagonalPoint F r d

/-- One one-dimensional Schwartz function bounds the last-row factor on
all diagonal points and all members of a fixed compact family. -/
theorem exists_compact_gaugeDiagonal_lastRow_majorant
    [CompactSpace (AdeleQuotient F)] (r : ℕ)
    {Φ : RowVector F (r + 1) → ℂ} (hΦ : Φ ∈ schwartzBruhat F (r + 1))
    {Q : Set (Points F (r + 1))} (hQ : IsCompact Q) :
    ∃ φ : RowVector F 1 → ℂ, φ ∈ schwartzBruhat F 1 ∧
      ∀ (d : Fin (r + 1) → Ideles F) (q : Points F (r + 1)), q ∈ Q →
        ‖Φ (lastRow F r (gaugeDiagonalPoint F (r + 1) d * q))‖ ≤
          ‖φ (singleRow F (d (Fin.last r) : Adeles F))‖ :=
  exists_compact_diagonal_lastRow_majorant F r hΦ hQ

/-- The same bound on the actual standard compact is unchanged by any
left adelic upper-unipotent factor. -/
theorem exists_standardCompact_lastRow_majorant
    [CompactSpace (AdeleQuotient F)] (r : ℕ)
    {Φ : RowVector F (r + 1) → ℂ} (hΦ : Φ ∈ schwartzBruhat F (r + 1)) :
    ∃ φ : RowVector F 1 → ℂ, φ ∈ schwartzBruhat F 1 ∧
      ∀ (d : Fin (r + 1) → Ideles F) (k : gaugeStandardCompact F (r + 1))
        (n : unipotentAdelic F (r + 1)),
        ‖Φ (lastRow F r ((n : Points F (r + 1)) *
          (gaugeDiagonalPoint F (r + 1) d * (k : Points F (r + 1)))))‖ ≤
            ‖φ (singleRow F (d (Fin.last r) : Adeles F))‖ := by
  obtain ⟨φ, hφ, hbound⟩ := exists_compact_gaugeDiagonal_lastRow_majorant F r hΦ
    (isCompact_gaugeStandardCompact F (r + 1))
  refine ⟨φ, hφ, fun d k n => ?_⟩
  rw [EqualUnfolding.lastRow_unipotent_mul]
  exact hbound d k k.2

end Langlands.Global.RankinSelbergGlobal
