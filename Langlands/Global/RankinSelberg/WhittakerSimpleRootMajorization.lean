import Langlands.Global.RankinSelberg.WhittakerSimpleRootMajorizationStatement
import Langlands.Global.RankinSelberg.WhittakerSimpleRootSchwartzBound
import Langlands.Global.RankinSelberg.SimpleRootActualGauge
import Langlands.Global.RankinSelberg.SimpleRootIwasawaBound

/-! # Global Whittaker majorization by an adelic simple-root gauge -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj Classical NNReal ENNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.GeneralLinear Langlands.GroupScheme.GeneralLinear
open Unfolding GaugeDescent

local instance rootMajorizationSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _

/-- Compact-uniform root decay gives the published pointwise gauge statement,
with gauge exponent zero and the given external determinant power. -/
theorem whittakerSimpleRootMajorization : WhittakerSimpleRootMajorizationStatement.{u} := by
  intro F _ _ _ r V R hV β hβ
  refine ⟨0, le_refl 0, ?_⟩
  intro ψ hψ f
  have hC : IsCompact (gaugeStandardCompact F (r + 1) : Set (Points F (r + 1))) :=
    (GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)).isCompact_preimage.mpr
      (PrimitiveAdelicHeight.isCompact_standardCompact F (r + 1))
  obtain ⟨c, Φ, _hc, hΦ, hbound, hsymm⟩ :=
    exists_simpleRoot_schwartzBruhat_bound F hV β hβ ψ hψ f hC
  obtain ⟨Ξ, hΞ, hformula, _hcontinuous⟩ :=
    exists_actual_simpleRoot_gauge F c Φ hΦ hsymm
  refine ⟨Ξ, hΞ, ?_⟩
  have hdiag : ∀ d : Fin (r + 1) → Ideles F,
      Ξ (gaugeDiagonalPoint F (r + 1) d) = ‖Φ (gaugeSimpleRootRow F r d)‖ₑ := by
    intro d
    let b : upperTriangularSubgroup (r + 1) (Adeles F) :=
      ⟨diagonalMatrixUnits (Adeles F) d, diagonalMatrixUnits_triangular d⟩
    simpa only [b, OneMemClass.coe_one, mul_one, triangularDiagonal_diagonal,
      gaugeDiagonalPoint] using hformula b 1
  intro g
  exact whittaker_le_of_simpleRoot_diagonal_bound F hV β ψ hψ f Φ Ξ
    hΞ.2.2.1 hΞ.2.2.2.1 hdiag (fun d k => hbound d k k.property) g

end Langlands.Global.RankinSelbergGlobal
