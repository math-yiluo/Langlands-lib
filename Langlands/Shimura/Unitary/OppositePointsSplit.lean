import Langlands.Shimura.Unitary.PointsSplit
import Langlands.Shimura.Unitary.SufficientlySmallLevels
import Langlands.Shimura.SplitLevelTower

/-! # The splitting of the opposite finite adelic points at the places dividing an integer

A splitting `G ≃ₜ* H × H'` of topological groups induces a splitting of the opposite groups. For
a rational involution and `m ≠ 0`, this splits `GG(A_f)ᵐᵒᵖ` as the opposite points at the places
dividing `m` times the opposite prime-to-`m` points. A level `K₀` at the places dividing `m` whose
elements have no nontrivial local component of finite order at one such place `v` makes every
level `e⁻¹ (K₀ × K')` sufficiently small. See `OppositePointsSplit.md`.
-/

noncomputable section

universe u v v₁ v₂

namespace Langlands.Shimura

namespace CompactOpenLevel

variable {G : Type v} {H : Type v₁} {H' : Type v₂} [Group G] [TopologicalSpace G] [Group H]
  [TopologicalSpace H] [Group H'] [TopologicalSpace H']

/-- A splitting `e : G ≃ₜ* H × H'` induces the splitting `Gᵐᵒᵖ ≃ₜ* Hᵐᵒᵖ × H'ᵐᵒᵖ` of the
opposite groups. -/
def oppositeSplit (e : G ≃ₜ* H × H') : Gᵐᵒᵖ ≃ₜ* Hᵐᵒᵖ × H'ᵐᵒᵖ where
  toFun g := (MulOpposite.op (e g.unop).1, MulOpposite.op (e g.unop).2)
  invFun p := MulOpposite.op (e.symm (p.1.unop, p.2.unop))
  left_inv g := by simp
  right_inv p := by simp
  map_mul' g g' := by
    simp only [MulOpposite.unop_mul, map_mul, Prod.fst_mul, Prod.snd_mul, MulOpposite.op_mul,
      Prod.mk_mul_mk]
  continuous_toFun :=
    (MulOpposite.continuous_op.comp
        (continuous_fst.comp ((map_continuous e).comp MulOpposite.continuous_unop))).prodMk
      (MulOpposite.continuous_op.comp
        (continuous_snd.comp ((map_continuous e).comp MulOpposite.continuous_unop)))
  continuous_invFun :=
    MulOpposite.continuous_op.comp ((map_continuous e.symm).comp
      ((MulOpposite.continuous_unop.comp continuous_fst).prodMk
        (MulOpposite.continuous_unop.comp continuous_snd)))

@[simp] theorem oppositeSplit_apply_fst (e : G ≃ₜ* H × H') (g : Gᵐᵒᵖ) :
    (oppositeSplit e g).1 = MulOpposite.op (e g.unop).1 :=
  rfl

@[simp] theorem oppositeSplit_apply_snd (e : G ≃ₜ* H × H') (g : Gᵐᵒᵖ) :
    (oppositeSplit e g).2 = MulOpposite.op (e g.unop).2 :=
  rfl

@[simp] theorem oppositeSplit_symm_apply (e : G ≃ₜ* H × H') (p : Hᵐᵒᵖ × H'ᵐᵒᵖ) :
    (oppositeSplit e).symm p = MulOpposite.op (e.symm (p.1.unop, p.2.unop)) :=
  rfl

end CompactOpenLevel

namespace AlgebraInvolution

open Langlands.Global CompactOpenLevel
open scoped NumberField

variable {A : Type u} [Ring A] [Algebra ℚ A] [Module.Finite ℚ A]
variable (σ : AlgebraInvolution ℚ A) (m : ℕ)

/-- For `m ≠ 0`, the opposite finite adelic points split as the opposite points at the places
whose prime ideal contains `m` times the opposite prime-to-`m` points. -/
def finiteAdelicPointsOpSplit (hm : m ≠ 0) :
    σ.FiniteAdelicPointsᵐᵒᵖ ≃ₜ* (σ.DividingPoints m)ᵐᵒᵖ × (σ.PrimeToPoints m)ᵐᵒᵖ :=
  oppositeSplit (σ.finiteAdelicPointsSplit m hm)

/-- The condition at a place `v` whose prime ideal contains `m`, on a level of the opposite points
at these places: every element whose component at `v` has finite order has trivial component at
`v`. -/
def DividingLevelSmallAt (K₀ : CompactOpenLevel (σ.DividingPoints m)ᵐᵒᵖ)
    (v : {v : FinitePlace ℚ // (m : 𝓞 ℚ) ∈ v.asIdeal}) : Prop :=
  ∀ h ∈ K₀.subgroup, IsOfFinOrder (σ.dividingLocalMap m v (MulOpposite.unop h)) →
    σ.dividingLocalMap m v (MulOpposite.unop h) = 1

/-- The condition `DividingLevelSmallAt` at some place whose prime ideal contains `m`. -/
def DividingLevelSufficientlySmall (K₀ : CompactOpenLevel (σ.DividingPoints m)ᵐᵒᵖ) : Prop :=
  ∃ v : {v : FinitePlace ℚ // (m : 𝓞 ℚ) ∈ v.asIdeal}, σ.DividingLevelSmallAt m K₀ v

variable {σ m}

/-- The local condition is inherited by every subgroup level. -/
theorem DividingLevelSmallAt.mono {K₀ L₀ : CompactOpenLevel (σ.DividingPoints m)ᵐᵒᵖ}
    {v : {v : FinitePlace ℚ // (m : 𝓞 ℚ) ∈ v.asIdeal}} (hL₀ : σ.DividingLevelSmallAt m L₀ v)
    (hKL : K₀.subgroup ≤ L₀.subgroup) : σ.DividingLevelSmallAt m K₀ v :=
  fun h hh hfin => hL₀ h (hKL hh) hfin

/-- Sufficient smallness at the places dividing `m` is inherited by every subgroup level. -/
theorem DividingLevelSufficientlySmall.mono {K₀ L₀ : CompactOpenLevel (σ.DividingPoints m)ᵐᵒᵖ}
    (hL₀ : σ.DividingLevelSufficientlySmall m L₀) (hKL : K₀.subgroup ≤ L₀.subgroup) :
    σ.DividingLevelSufficientlySmall m K₀ := by
  obtain ⟨v, hv⟩ := hL₀
  exact ⟨v, hv.mono hKL⟩

variable (hm : m ≠ 0)

/-- If `K₀` satisfies the local condition at a place `v` dividing `m`, then for every level `K'`
of the opposite prime-to-`m` points, the level `e⁻¹ (K₀ × K')` of `GG(A_f)ᵐᵒᵖ` satisfies the
local condition at `v`. -/
theorem levelSmallAt_transport_prod {K₀ : CompactOpenLevel (σ.DividingPoints m)ᵐᵒᵖ}
    {v : {v : FinitePlace ℚ // (m : 𝓞 ℚ) ∈ v.asIdeal}} (hK₀ : σ.DividingLevelSmallAt m K₀ v)
    (K' : CompactOpenLevel (σ.PrimeToPoints m)ᵐᵒᵖ) :
    σ.LevelSmallAt (transport (σ.finiteAdelicPointsOpSplit m hm).symm (prod K₀ K')) v.1 := by
  intro g hg
  have hg₀ : MulOpposite.op (σ.finiteAdelicPointsSplit m hm (MulOpposite.unop g)).1 ∈
      K₀.subgroup :=
    (mem_transport_symm_prod (σ.finiteAdelicPointsOpSplit m hm)).1 hg |>.1
  change IsOfFinOrder (σ.finiteLocalMap v.1 (MulOpposite.unop g)) →
    σ.finiteLocalMap v.1 (MulOpposite.unop g) = 1
  rw [← σ.dividingLocalMap_finiteAdelicPointsSplit m hm v]
  exact hK₀ _ hg₀

/-- If `K₀` is sufficiently small at the places dividing `m`, then every level `e⁻¹ (K₀ × K')`
of `GG(A_f)ᵐᵒᵖ` is sufficiently small. -/
theorem levelSufficientlySmall_transport_prod {K₀ : CompactOpenLevel (σ.DividingPoints m)ᵐᵒᵖ}
    (hK₀ : σ.DividingLevelSufficientlySmall m K₀)
    (K' : CompactOpenLevel (σ.PrimeToPoints m)ᵐᵒᵖ) :
    σ.LevelSufficientlySmall (transport (σ.finiteAdelicPointsOpSplit m hm).symm (prod K₀ K')) := by
  obtain ⟨v, hv⟩ := hK₀
  exact ⟨v.1, levelSmallAt_transport_prod hm hv K'⟩

end AlgebraInvolution

end Langlands.Shimura
