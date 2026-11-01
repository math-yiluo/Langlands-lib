import Langlands.Shimura.Unitary.Adelic
import Langlands.Shimura.Levels
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # The local finite-order condition on Harris levels -/

noncomputable section

universe u

namespace Langlands.Shimura.AlgebraInvolution

variable {A : Type u} [Ring A] [Algebra ℚ A]
variable (σ : AlgebraInvolution ℚ A)

/-- The condition at a specified finite place: every finite-order element in
the actual local projection of the subgroup is the identity. -/
def LevelSmallAt
    (U : CompactOpenLevel σ.FiniteAdelicPointsᵐᵒᵖ)
    (v : Global.FinitePlace ℚ) : Prop :=
  ∀ g ∈ U.subgroup,
    IsOfFinOrder (σ.pointsMap (finiteEvaluation v) (MulOpposite.unop g)) →
      σ.pointsMap (finiteEvaluation v) (MulOpposite.unop g) = 1

/-- Harris--Taylor's sufficiently small condition, using an actual finite
place and the existing finite-adelic coefficient evaluation. -/
def LevelSufficientlySmall
    (U : CompactOpenLevel σ.FiniteAdelicPointsᵐᵒᵖ) : Prop :=
  ∃ v : Global.FinitePlace ℚ, σ.LevelSmallAt U v

variable {σ}

/-- The local condition is inherited by every subgroup level. -/
theorem LevelSmallAt.mono
    {U V : CompactOpenLevel σ.FiniteAdelicPointsᵐᵒᵖ}
    {v : Global.FinitePlace ℚ}
    (hV : σ.LevelSmallAt V v) (hUV : U.subgroup ≤ V.subgroup) :
    σ.LevelSmallAt U v :=
  fun g hg hfin => hV g (hUV hg) hfin

/-- Sufficient smallness is inherited by every subgroup level. -/
theorem LevelSufficientlySmall.mono
    {U V : CompactOpenLevel σ.FiniteAdelicPointsᵐᵒᵖ}
    (hV : σ.LevelSufficientlySmall V) (hUV : U.subgroup ≤ V.subgroup) :
    σ.LevelSufficientlySmall U := by
  obtain ⟨v, hv⟩ := hV
  exact ⟨v, hv.mono hUV⟩

/-- The genuine transporter category restricted to sufficiently small levels;
its morphisms retain their actual translating elements. -/
abbrev SmallLevelCategory :=
  CategoryTheory.ObjectProperty.FullSubcategory σ.LevelSufficientlySmall

section Hecke

variable [Module.Finite ℚ A]

/-- The existing actual Hecke intersection is sufficiently small whenever
its first level is. -/
theorem LevelSufficientlySmall.heckeLevel
    {U : CompactOpenLevel σ.FiniteAdelicPointsᵐᵒᵖ}
    (hU : σ.LevelSufficientlySmall U)
    (V : CompactOpenLevel σ.FiniteAdelicPointsᵐᵒᵖ)
    (g : σ.FiniteAdelicPointsᵐᵒᵖ) :
    σ.LevelSufficientlySmall (CompactOpenLevel.heckeLevel U V g) :=
  hU.mono (fun _ hk => hk.1)

end Hecke

end Langlands.Shimura.AlgebraInvolution
