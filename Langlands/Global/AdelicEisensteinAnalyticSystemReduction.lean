import Langlands.Global.AdelicEisensteinSystemDominationStatement
import Langlands.Global.AdelicEisensteinAnalyticSystemStatement

/-! # The Eisenstein analytic system from local finiteness and domination

`EisensteinAnalyticSystemStatement` follows from Bernstein–Lapid's Theorem 7.2
(`UniformGrowthLocalFinitenessStatement`) and Proposition 8.4 in domination form
(`EisensteinSystemDominationStatement`). The data of `Ξ_main` live on all of `ℂⁿ`. The closure of
the bounded set `W` is compact, so finitely many of the neighbourhoods given by Theorem 7.2
cover it, and one exponent `R` works for all of them. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct Manifold

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-- **The reduction.** Bernstein–Lapid's Theorem 7.2 in Fréchet form and Proposition 8.4 in
domination form imply the analytic system characterizing Eisenstein series. It is proved by
`eisensteinAnalyticSystemReduction` below. -/
def EisensteinAnalyticSystemReductionStatement : Prop :=
  UniformGrowthLocalFinitenessStatement.{u} → EisensteinSystemDominationStatement.{u} →
    EisensteinAnalyticSystemStatement.{u}

/-- Bernstein–Lapid, §8.4: Theorem 7.2 and Proposition 8.4 (with the domination of `Ξ_fnl` by a
system of §7.2) give the analytic system characterizing Eisenstein series. -/
theorem eisensteinAnalyticSystem_of_localFiniteness_of_domination
    (hLF : UniformGrowthLocalFinitenessStatement.{u})
    (hD : EisensteinSystemDominationStatement.{u}) :
    EisensteinAnalyticSystemStatement.{u} := by
  intro F _ _ G P M U A _ _ _ p _ iU l a r _ _ _ hA hT hG hU K hK N d rho hN hrho hsmooth hcalc
    φ hKmax hφ
  have := hsmooth
  have : Smooth G.X.hom := SmoothOfRelativeDimension.smooth (n := d) (f := G.X.hom)
  obtain ⟨R₀, hR₀⟩ := hD F G P M U A p iU l a r hA hT hG hU K hK rho hN hrho hsmooth hcalc φ
    hKmax hφ
  refine ⟨R₀, fun n e W hW => ?_⟩
  obtain ⟨T, iT, ν, hmax, hgen, Ua, instA, u, instC, t, nZ, z, hgroup, X, hX, L, hLo, hLc,
    R₁, hR⟩ := hR₀ n e W hW
  have hloc := fun s₀ : (⊤ : TopologicalSpace.Opens (Fin n → ℂ)) =>
    hLF F G T iT ν hG hmax hgen Ua u t nZ z hgroup rho hN hrho hsmooth hcalc n ⊤ X hX L hLo
      hLc s₀
  choose V hV using hloc
  have hVo : ∀ i, IsOpen (V i) := fun i => (hV i).1
  have hVmem : ∀ i, i ∈ V i := fun i => (hV i).2.1
  choose R' hR' using fun i => (hV i).2.2
  -- the compact closure of `W` is covered by finitely many of the sets `V i`
  have hKc : IsCompact (closure (W : Set (Fin n → ℂ))) := hW.isCompact_closure
  have hopen : ∀ i, IsOpen (Subtype.val '' V i) := fun i =>
    (⊤ : TopologicalSpace.Opens (Fin n → ℂ)).isOpen.isOpenEmbedding_subtypeVal.isOpenMap _
      (hVo i)
  have hcover : closure (W : Set (Fin n → ℂ)) ⊆ ⋃ i, Subtype.val '' V i := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨⟨x, trivial⟩, ⟨x, trivial⟩, hVmem _, rfl⟩
  obtain ⟨fin, hfin⟩ := hKc.elim_finite_subcover (fun i => Subtype.val '' V i) hopen hcover
  set R : ℝ := |R₁| + ∑ i ∈ fin, |R' i| with hRdef
  have hsum_nonneg : 0 ≤ ∑ i ∈ fin, |R' i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hR₁ : R₁ ≤ R := (le_abs_self R₁).trans (le_add_of_nonneg_right hsum_nonneg)
  have hR'le : ∀ i ∈ fin, R' i ≤ R := fun i hi =>
    (le_abs_self _).trans ((Finset.single_le_sum (fun j _ => abs_nonneg (R' j)) hi).trans
      (le_add_of_nonneg_left (abs_nonneg R₁)))
  obtain ⟨Idx, eqn, c, hAn, hdom, huniq, haut⟩ := hR R hR₁
  refine ⟨R, L, hLo, Idx, eqn, c, hAn, ?_, huniq, haut⟩
  -- local finite type on `W`
  intro s₀
  have hs₀ : (s₀ : Fin n → ℂ) ∈ closure (W : Set (Fin n → ℂ)) := subset_closure s₀.2
  obtain ⟨i, hi, y, hy, hys⟩ := Set.mem_iUnion₂.mp (hfin hs₀)
  let incl : W → (⊤ : TopologicalSpace.Opens (Fin n → ℂ)) :=
    TopologicalSpace.Opens.inclusion (le_top : W ≤ ⊤)
  have hincl : ContMDiff 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) 1 incl :=
    contMDiff_inclusion le_top
  refine ⟨incl ⁻¹' V i, (hVo i).preimage hincl.continuous, ?_, ?_⟩
  · have : incl s₀ = y := Subtype.ext hys.symm
    show incl s₀ ∈ V i
    rw [this]
    exact hy
  · obtain ⟨m, ℓ, hhol, hinj, hsub⟩ := hR' i R (hR'le i hi)
    refine ⟨m, fun s => ℓ (incl s), fun v lf => ?_, fun s hs => hinj _ hs,
      fun s hs => (hdom s).trans (hsub _ hs)⟩
    exact (hhol v lf).comp (hincl.mdifferentiable one_ne_zero).mdifferentiableOn
      (fun s hs => hs)

/-- The reduction `EisensteinAnalyticSystemReductionStatement` holds. -/
theorem eisensteinAnalyticSystemReduction : EisensteinAnalyticSystemReductionStatement.{u} :=
  fun hLF hD => eisensteinAnalyticSystem_of_localFiniteness_of_domination hLF hD

end Langlands.Global
