import Langlands.Representation.Archimedean.RealTemperedIrreducibleStatement

/-!
# The rank-zero real standard module

The empty-list standard module on the singleton group `GL₀(ℝ)` consists of
all complex-valued functions. Evaluation at the identity identifies its
compact-finite part with `ℂ`, so it is irreducible.
-/

noncomputable section

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

open scoped Manifold ContDiff Matrix Matrix.Norms.Operator

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RealRankZeroStandardModule

abbrev KF := kFiniteFunctions (realStandardModule 0 []) (unitaryCompact ℝ 0)

/-- On `GL₀(ℝ)` evaluation at the identity is injective, since the group
has just one element. -/
theorem eval_injective :
    Function.Injective (LinearMap.proj (R := ℂ)
      (φ := fun _ : Langlands.GeneralLinear 0 ℝ => ℂ) 1) := by
  intro f g h
  funext x
  have hx : x = 1 := Subsingleton.elim _ _
  change f 1 = g 1 at h
  simpa only [hx] using h

/-- Every constant function belongs to the compact-finite empty standard
module in rank zero. -/
theorem constant_mem (c : ℂ) :
    (fun _ : Langlands.GeneralLinear 0 ℝ => c) ∈
      kFiniteFunctions (realStandardModule 0 []) (unitaryCompact ℝ 0) := by
  have : FiniteDimensional ℂ (Langlands.GeneralLinear 0 ℝ → ℂ) :=
    FiniteDimensional.of_injective
      (LinearMap.proj (R := ℂ) (φ := fun _ : Langlands.GeneralLinear 0 ℝ => ℂ) 1)
      eval_injective
  refine ⟨⟨⟨contMDiff_const, ?_⟩, ?_⟩, ?_⟩
  · intro a u g
    simp [principalSeriesCharacter]
  · intro p d hp
    simp [realInducedBlockAt] at hp
  · apply (mem_kFiniteVectors_iff _ _ _).mpr
    infer_instance

/-- Evaluation at the identity identifies the rank-zero compact-finite
standard module with the one-dimensional complex vector space. -/
def evalEquiv : KF ≃ₗ[ℂ] ℂ where
  toFun f := (f : Langlands.GeneralLinear 0 ℝ → ℂ) 1
  invFun c := ⟨fun _ => c, constant_mem c⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    have hx : x = 1 := Subsingleton.elim _ _
    simp only [hx]
  right_inv c := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Every linear subspace of the rank-zero standard module is zero or
the whole space. -/
theorem submodule_eq_bot_or_top (U : Submodule ℂ KF) : U = ⊥ ∨ U = ⊤ := by
  by_cases hU : U = ⊥
  · exact Or.inl hU
  · right
    obtain ⟨f, hfU, hf⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
    have hf1 : evalEquiv f ≠ 0 := by
      intro h
      apply hf
      apply evalEquiv.injective
      simpa using h
    refine eq_top_iff.mpr fun g _ => ?_
    have hg : g = (evalEquiv g / evalEquiv f) • f := by
      apply evalEquiv.injective
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hf1]
    rw [hg]
    exact U.smul_mem _ hfU

/-- The rank-zero empty standard module is irreducible. -/
theorem isIrreducible :
    IsIrreducibleGKModule (realStandardRep 0 []) (realStandardLie 0 []) := by
  refine ⟨?_, fun U _ _ => submodule_eq_bot_or_top U⟩
  exact evalEquiv.symm.injective.nontrivial

/-- A list of real blocks of total rank zero must be empty. -/
theorem eq_nil_of_realRank_eq_zero (ds : List RealBlock) (h : realRank ds = 0) :
    ds = [] := by
  cases ds with
  | nil => rfl
  | cons x ds =>
      cases x <;> simp [realRank_cons, RealBlock.rank] at h

end RealRankZeroStandardModule

/-- The rank-zero case of real standard-module irreducibility. -/
def RealRankZeroStandardIrreducibleStatement : Prop :=
  ∀ ds : List RealBlock, realRank ds = 0 →
    IsIrreducibleGKModule (realStandardRep 0 ds) (realStandardLie 0 ds)

/-- The rank-zero case follows from evaluation at the identity. -/
theorem realRankZeroStandardIrreducible : RealRankZeroStandardIrreducibleStatement := by
  intro ds h
  rw [RealRankZeroStandardModule.eq_nil_of_realRank_eq_zero ds h]
  exact RealRankZeroStandardModule.isIrreducible

end Langlands.Archimedean
