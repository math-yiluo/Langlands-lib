import Langlands.Global.RankinSelberg.RealStandardCompactFinite
import Langlands.Representation.Archimedean.RealPrincipalSeriesQuotientReduction

/-! # Closed smooth images of scalar principal-series intertwiners -/

noncomputable section

open Langlands.LocalFactor.Archimedean Langlands.Global.RankinSelbergGlobal
open scoped Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open DerivativeSmoothVectors RealStandardCompactBanach

attribute [local instance 100] LieRing.ofAssociativeRing

private local instance (n : ℕ) (ds : List RealBlock) : NormedAddCommGroup (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedAddCommGroup

private local instance (n : ℕ) (ds : List RealBlock) : NormedSpace ℂ (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedSpace

universe uV

local notation "K" n:max => Matrix.unitaryGroup (Fin n) ℝ
local notation "M" n:max => Matrix (Fin n) (Fin n) ℝ
local notation "I" n:max => matrixModel ℝ n
local notation "S" cs:max => List.map RealBlock.character cs
local notation "V₀" n:max cs:max =>
  kFiniteFunctions (realStandardModule n (S cs)) (unitaryCompact ℝ n)
local notation "P" rank:max cs:max => RealStandardCompactBanach.representation (n := rank) (S cs)
local notation "D" n:max R:max => DerivativeSmoothVectors (I n) R
local notation "j" rank:max cs:max => compactFiniteEquiv (n := rank) (S cs)

/-- An irreducible admissible real module has a scalar principal-series quotient and
embedding whose composite extends with closed range on the genuine smooth models. -/
def RealPrincipalSeriesClosedImageStatement : Prop :=
  ∀ (r : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (K (r + 1)) V) (π : (ℂ ⊗[ℝ] M (r + 1)) →ₗ⁅ℂ⁆ Module.End ℂ V),
    IsRealGKModule (r + 1) ρ π → IsIrreducibleGKModule ρ π → IsAdmissibleGKModule ρ →
    ∃ (cs es : List RealCharacterData) (q : V₀ (r + 1) cs →ₗ[ℂ] V) (B : V →ₗ[ℂ] V₀ (r + 1) es),
      cs.length = r + 1 ∧ es.length = r + 1 ∧ Function.Surjective q ∧ Function.Injective B ∧
      IsRealStandardIntertwiner (r + 1) ρ π (S cs) q ∧ IsRealStandardEmbedding (r + 1) ρ π (S es) B ∧
      ∃ T : D (r + 1) (P (r + 1) cs) →L[ℂ] D (r + 1) (P (r + 1) es),
        IsClosed (Set.range T) ∧ ∀ w : V₀ (r + 1) cs, T (((j (r + 1) cs) w).val) = ((j (r + 1) es) (B (q w))).val

end Langlands.Archimedean
