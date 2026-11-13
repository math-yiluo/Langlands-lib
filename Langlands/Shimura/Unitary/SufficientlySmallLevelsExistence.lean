import Langlands.Shimura.Unitary.SufficientlySmallLevels
import Langlands.Shimura.Unitary.TorsionFreeLevels
import Langlands.Global.PrimeToFiniteAdeles

/-! # Sufficiently small levels exist below every original level -/

noncomputable section

open Langlands.Global Langlands.Shimura.SmallLevels
open scoped NumberField

set_option autoImplicit false

universe u

namespace Langlands.Shimura.AlgebraInvolution

variable {A : Type u} [Ring A] [Algebra ℚ A] [Module.Finite ℚ A]
variable (σ : AlgebraInvolution ℚ A)

/-- The elements of the opposite finite-adelic points whose actual local image
at `v` lies in the principal congruence level modulo `q`. -/
def oppositeCongruenceSubgroup (v : FinitePlace ℚ) (q : ℕ) :
    Subgroup σ.FiniteAdelicPointsᵐᵒᵖ :=
  ((congruenceLevel σ v q).comap (σ.finiteLocalMap v).toMonoidHom).op

theorem mem_oppositeCongruenceSubgroup {v : FinitePlace ℚ} {q : ℕ}
    {g : σ.FiniteAdelicPointsᵐᵒᵖ} :
    g ∈ σ.oppositeCongruenceSubgroup v q ↔
      σ.pointsMap (finiteEvaluation v) (MulOpposite.unop g) ∈ congruenceLevel σ v q :=
  Iff.rfl

theorem isOpen_oppositeCongruenceSubgroup (v : FinitePlace ℚ) {q : ℕ} (hq : q ≠ 0) :
    IsOpen (σ.oppositeCongruenceSubgroup v q : Set σ.FiniteAdelicPointsᵐᵒᵖ) :=
  ((isOpen_congruenceLevel σ v hq).preimage (σ.finiteLocalMap v).continuous).preimage
    MulOpposite.continuous_unop

/-- The level `U` shrunk at `v`: the elements of `U` whose local image at `v`
lies in the principal congruence level modulo `q`. -/
def congruenceShrink (v : FinitePlace ℚ) {q : ℕ} (hq : q ≠ 0)
    (U : CompactOpenLevel σ.FiniteAdelicPointsᵐᵒᵖ) :
    CompactOpenLevel σ.FiniteAdelicPointsᵐᵒᵖ where
  openSubgroup :=
    { toSubgroup := U.subgroup ⊓ σ.oppositeCongruenceSubgroup v q
      isOpen' := U.openSubgroup.isOpen.inter (σ.isOpen_oppositeCongruenceSubgroup v hq) }
  isCompact := U.isCompact.inter_right
    (Subgroup.isClosed_of_isOpen _ (σ.isOpen_oppositeCongruenceSubgroup v hq))

variable {σ}

theorem congruenceShrink_le (v : FinitePlace ℚ) {q : ℕ} (hq : q ≠ 0)
    (U : CompactOpenLevel σ.FiniteAdelicPointsᵐᵒᵖ) :
    (σ.congruenceShrink v hq U).subgroup ≤ U.subgroup :=
  inf_le_left

/-- For a prime `q ≥ 3` contained in `v`, the shrunk level satisfies the local
finite-order condition at `v`. -/
theorem levelSmallAt_congruenceShrink [Nontrivial A] {v : FinitePlace ℚ} {q : ℕ}
    (hq : q.Prime) (hq3 : 3 ≤ q) (hv : (q : 𝓞 ℚ) ∈ v.asIdeal)
    (U : CompactOpenLevel σ.FiniteAdelicPointsᵐᵒᵖ) :
    σ.LevelSmallAt (σ.congruenceShrink v hq.ne_zero U) v :=
  fun _ hg hfin => congruenceLevel_torsionFree σ hq hq3 hv _ hg.2 hfin

/-- Every original compact-open level contains a sufficiently small level. -/
theorem exists_levelSufficientlySmall_le [Nontrivial A]
    (U : CompactOpenLevel σ.FiniteAdelicPointsᵐᵒᵖ) :
    ∃ V : σ.SmallLevelCategory, V.obj.subgroup ≤ U.subgroup := by
  obtain ⟨v, hv, -⟩ := existsUnique_finitePlace_natCast_mem 3 Nat.prime_three
  exact ⟨⟨σ.congruenceShrink v Nat.prime_three.ne_zero U,
      v, levelSmallAt_congruenceShrink Nat.prime_three le_rfl hv U⟩,
    congruenceShrink_le v Nat.prime_three.ne_zero U⟩

/-- If an original compact-open level exists, then so does a sufficiently
small one. -/
theorem nonempty_smallLevelCategory [Nontrivial A]
    [Nonempty (CompactOpenLevel σ.FiniteAdelicPointsᵐᵒᵖ)] :
    Nonempty σ.SmallLevelCategory := by
  obtain ⟨U⟩ := ‹Nonempty (CompactOpenLevel σ.FiniteAdelicPointsᵐᵒᵖ)›
  obtain ⟨V, -⟩ := exists_levelSufficientlySmall_le U
  exact ⟨V⟩

end Langlands.Shimura.AlgebraInvolution
