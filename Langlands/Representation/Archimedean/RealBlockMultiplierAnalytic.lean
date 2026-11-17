import Langlands.Representation.Archimedean.RealBlockMultiplierOperators
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Analytic multiplier families on finite compact layers

These internal results use uniform finite Fourier support and finite-dimensional
separation by compact evaluations. No topology on the whole standard module is
chosen.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean
open RealBlockRotation RealBlockFourierFinite RealBlockJacquet
open RealBlockFrobeniusMap RealKTypeCount

namespace RealBlockMultiplierAnalytic

variable {n : ℕ} {ds es : List RealBlock} {p : ℕ} {ε : ℤ} {σ : ℂ}

abbrev KF (n : ℕ) (ds : List RealBlock) :=
  kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)

/-- Analyticity of every algebraic scalar coordinate of a family. -/
def IsWeaklyAnalyticAt {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : ℂ → V) (z₀ : ℂ) : Prop :=
  ∀ ℓ : V →ₗ[ℂ] ℂ, AnalyticAt ℂ (fun z => ℓ (f z)) z₀

theorem IsWeaklyAnalyticAt.const {V : Type*} [AddCommGroup V] [Module ℂ V]
    (v : V) (z₀ : ℂ) : IsWeaklyAnalyticAt (fun _ => v) z₀ :=
  fun _ => analyticAt_const

theorem IsWeaklyAnalyticAt.map {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {f : ℂ → V} {z₀ : ℂ} (hf : IsWeaklyAnalyticAt f z₀) (T : V →ₗ[ℂ] W) :
    IsWeaklyAnalyticAt (fun z => T (f z)) z₀ :=
  fun ℓ => hf (ℓ.comp T)

/-- A block Fourier coefficient at a fixed point is an algebraic linear
functional on the actual compact-finite standard-module functions. -/
def fourierEval (p : ℕ) (j : ℤ) (g : Langlands.GeneralLinear n ℝ) :
    KF n ds →ₗ[ℂ] ℂ where
  toFun f := blockFourierCoefficient n p j f g
  map_add' f f' := blockFourierCoefficient_add p j (continuous_coe f) (continuous_coe f') g
  map_smul' c f := blockFourierCoefficient_smul p j c f g

/-- A whole finite-dimensional subspace has a common Fourier cutoff, uniformly
over all points of the compact group. -/
theorem exists_uniform_bound (S : Submodule ℂ (KF n ds)) [FiniteDimensional ℂ S]
    (p : ℕ) :
    ∃ D : ℕ, ∀ f ∈ S, ∀ j : ℤ, (D : ℤ) < |j| →
      ∀ g ∈ unitaryCompact ℝ n, blockFourierCoefficient n p j f g = 0 := by
  classical
  let : Module.Free ℂ S := Module.Free.of_divisionRing ℂ S
  let b := Module.finBasis ℂ S
  choose D hD using fun i => exists_bound_coe p (b i : KF n ds)
  refine ⟨∑ i, D i, fun f hf j hj g hg => ?_⟩
  have hz : ∀ i, fourierEval p j g (b i : KF n ds) = 0 := by
    intro i
    apply hD i j _ g hg
    have hi : D i ≤ ∑ k, D k :=
      Finset.single_le_sum (fun k _ => Nat.zero_le (D k)) (Finset.mem_univ i)
    exact lt_of_le_of_lt (by exact_mod_cast hi) hj
  have heq := congrArg ((fourierEval p j g).comp S.subtype) (b.sum_repr ⟨f, hf⟩)
  change fourierEval p j g f = 0
  simpa only [map_sum, map_smul, LinearMap.comp_apply, Submodule.subtype_apply,
    hz, smul_zero, Finset.sum_const_zero] using heq.symm

/-- Every supplied symmetric block multiplier map is compact equivariant;
recurrence is unnecessary for this property. -/
theorem compactEquivariant {μ : ℤ → ℂ}
    (h : IsBlockFrobData n ds es p ε σ μ) :
    IsRealKEquivariant (realStandardModule n ds) (realStandardModule n es)
      (blockFrobMap h) := by
  intro k f
  refine ⟨rightTranslation_mem_kFiniteFunctions_realStandardModule n ds f.2 k.2,
    rightTranslation_mem_kFiniteFunctions_realStandardModule n es (blockFrobMap h f).2 k.2,
    ?_⟩
  exact blockFrobMap_mk_rightTranslation h k f _ _

theorem mem_layer_blockFrobMap {μ : ℤ → ℂ}
    (h : IsBlockFrobData n ds es p ε σ μ) {N : ℕ} {f : KF n ds}
    (hf : f ∈ layer (realStandardModule n ds) (degreeLE n N)) :
    blockFrobMap h f ∈ layer (realStandardModule n es) (degreeLE n N) :=
  mem_layer_degreeLE_of_isRealKEquivariant
    (fun _ hf => hf.1 :
      realStandardModule n ds ≤ principalSeries ℝ n (realPositionCharacter ds))
    (compactEquivariant h) hf

/-- On a fixed finite degree layer, coordinatewise analytic multipliers applied
to a weakly analytic family have analytic values at every compact point. -/
theorem analyticAt_compact_eval {μ : ℂ → ℤ → ℂ}
    (h : ∀ z, IsBlockFrobData n ds es p ε σ (μ z))
    {N : ℕ} {f : ℂ → KF n ds} {z₀ : ℂ}
    (hf : ∀ z, f z ∈ layer (realStandardModule n ds) (degreeLE n N))
    (ha : IsWeaklyAnalyticAt f z₀)
    (hμ : ∀ j, AnalyticAt ℂ (fun z => μ z j) z₀)
    {g : Langlands.GeneralLinear n ℝ} (hg : g ∈ unitaryCompact ℝ n) :
    AnalyticAt ℂ (fun z => (blockFrobMap (h z) (f z) :
      Langlands.GeneralLinear n ℝ → ℂ) g) z₀ := by
  let := finiteDimensional_layer (fun _ hf => hf.1 :
    realStandardModule n ds ≤ principalSeries ℝ n (realPositionCharacter ds)) (degreeLE n N)
  obtain ⟨D, hD⟩ := exists_uniform_bound
    (layer (realStandardModule n ds) (degreeLE n N)) p
  have heq : (fun z => (blockFrobMap (h z) (f z) :
      Langlands.GeneralLinear n ℝ → ℂ) g) =
      fun z => (2 * (Real.pi : ℂ))⁻¹ *
        ∑ j ∈ Finset.Icc (-(D : ℤ)) D, μ z j * fourierEval p j g (f z) := by
    funext z
    rw [blockFrobMap_apply_of_mem (h z) (f z) hg,
      finsum_eq_sum_of_support_subset (s := Finset.Icc (-(D : ℤ)) D)]
    · rfl
    · intro j hj
      rw [Finset.coe_Icc, Set.mem_Icc, ← abs_le]
      by_contra hjD
      apply hj
      change μ z j * blockFourierCoefficient n p j (f z) g = 0
      rw [hD (f z) (hf z) j (not_le.mp hjD) g hg, mul_zero]
  rw [heq]
  apply analyticAt_const.mul
  apply Finset.analyticAt_fun_sum
  intro j _
  exact (hμ j).mul (ha (fourierEval p j g))

/-- Analyticity of all scalar coordinates of the output. The proof uses the
finite target degree layer and separation by compact point evaluations. -/
theorem weaklyAnalyticAt_blockFrobMap {μ : ℂ → ℤ → ℂ}
    (h : ∀ z, IsBlockFrobData n ds es p ε σ (μ z))
    {N : ℕ} {f : ℂ → KF n ds} {z₀ : ℂ}
    (hf : ∀ z, f z ∈ layer (realStandardModule n ds) (degreeLE n N))
    (ha : IsWeaklyAnalyticAt f z₀)
    (hμ : ∀ j, AnalyticAt ℂ (fun z => μ z j) z₀) :
    IsWeaklyAnalyticAt (fun z => blockFrobMap (h z) (f z)) z₀ := by
  intro ℓ
  let ev : Matrix.unitaryGroup (Fin n) ℝ → KF n es →ₗ[ℂ] ℂ := fun κ =>
    (LinearMap.proj (R := ℂ) (φ := fun _ : Langlands.GeneralLinear n ℝ => ℂ)
      (Unitary.toUnits κ)).comp (KF n es).subtype
  let := finiteDimensional_layer (fun _ hf => hf.1 :
    realStandardModule n es ≤ principalSeries ℝ n (realPositionCharacter es)) (degreeLE n N)
  have hsep : ∀ s ∈ layer (realStandardModule n es) (degreeLE n N),
      (∀ κ, ev κ s = 0) → s = 0 := by
    intro s _ hs
    apply restrict_injective (fun _ hf => hf.1 :
      realStandardModule n es ≤ principalSeries ℝ n (realPositionCharacter es))
    rw [map_zero]
    funext κ
    exact hs κ
  obtain ⟨m, pt, c, hsum⟩ := exists_sum_of_separating ev
    (layer (realStandardModule n es) (degreeLE n N)) hsep ℓ
  have heq : (fun z => ℓ (blockFrobMap (h z) (f z))) =
      fun z => ∑ i, c i * ev (pt i) (blockFrobMap (h z) (f z)) := by
    funext z
    exact hsum _ (mem_layer_blockFrobMap (h z) (hf z))
  rw [heq]
  apply Finset.analyticAt_fun_sum
  intro i _
  exact analyticAt_const.mul (analyticAt_compact_eval h hf ha hμ (pt i).2)

end RealBlockMultiplierAnalytic
end Langlands.Archimedean
