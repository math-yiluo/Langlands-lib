import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalConvergenceStatements
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalConstantTerm
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSquareIntegrableDecay
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.XiCompactComparison

/-! # Reductions of the actual central and radical convergence targets

This module reduces two of the closed targets of `RationalCuspidalConvergenceStatements` to
Library statements whose proofs are not yet available:

* `RationalSchwartzCentralConvergenceStatement` follows from
  `RationalSplitCenterHeightStatement` (the height properties of `A_G(F)`);
* for one group and one standard parabolic `P_J = M_J U_J`, the integrability of
  `v ↦ f(x v y)` on `U_J(F)` for every actual Schwartz function `f` follows from
  `RationalConstantTermEstimateStatement` (Proposition II.4.5), given a compact open `K0` with
  its structural premises and one compact open `K'` with `G(F) = P₀(F) K'` and
  `M_J(F) = (P₀(F) ∩ M_J(F)) (K' ∩ M_J(F))`. The compact open subgroup `K` defining the
  Schwartz space is arbitrary: the comparison of `Ξ_K` with `Ξ_{K'}` (`XiCompactComparison`)
  moves `f` to the Schwartz space for `K'`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

/-- **Central convergence from the heights of the split centre**: the proposition
`RationalSplitCenterHeightStatement` implies `RationalSchwartzCentralConvergenceStatement`. Its
second clause gives the actual `CentralWeights` for every Haar measure on `A_G(F)`, and these make
every central integral `a ↦ χ(a)⁻¹ f(a g)` absolutely convergent for a unitary `χ`. -/
theorem RationalSplitCenterHeightStatement.schwartzCentralConvergence
    (h : RationalSplitCenterHeightStatement.{u}) :
    RationalSchwartzCentralConvergenceStatement.{u} := by
  intro F _ _ _ _ G _ _ hG S i _ ν _ K hKc hPK N _ ρ hρ T s hs muA _ χ _ hχ
  have : Nonempty (CompactOpenSubgroup (rationalPoints G)) := ⟨⟨K, hKc⟩⟩
  exact (h.centralWeights K.isOpen hKc hPK ρ hG hs hρ muA).convergesOn _ _ _ hχ

section Radical

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}

/-- **Integrability of two-sided translates from an estimate at another compact subgroup**: let
`K`, `K'` be compact open subgroups of `G(F)` with `G(F) = P₀(F) K = P₀(F) K'`, and suppose the
estimate of Proposition II.4.5 (`ConstantTermEstimate`) holds for a measure `ν_U` on a subgroup
`U` and the weights `Ξ_{K'}`, `σ = rationalHeight ρ`. Then for every `f` in the Schwartz space
built from `Ξ_K` and `σ` and all `x, y ∈ G(F)`, the function `v ↦ f(x v y)` is
`ν_U`-integrable on `U`. -/
theorem integrable_mul_mul_of_constantTermEstimate {K K' : Subgroup (rationalPoints G)}
    (hKo : IsOpen (K : Set (rationalPoints G))) (hKc : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)
    (hK'o : IsOpen (K' : Set (rationalPoints G)))
    (hK'c : IsCompact (K' : Set (rationalPoints G)))
    (hPK' : IsIwasawaPair (standardParabolicPoints i ν ∅) K')
    {n : Type} [Fintype n] [DecidableEq n] [Nonempty n] (ρ : MatrixRepresentation G n)
    {M U : Subgroup (rationalPoints G)} {nuU : Measure U} {δ : M →* ℝ≥0ˣ} {ΞM σM : M → ℝ}
    (hest : ConstantTermEstimate nuU δ (rationalXi hK'c hPK') (rationalHeight (F := F) ρ) ΞM σM)
    {f : rationalPoints G → ℂ}
    (hf : f ∈ schwartzSubmodule (rationalXi hKc hPK) (rationalHeight (F := F) ρ))
    (x y : rationalPoints G) :
    Integrable (fun v : U => f (x * (v : rationalPoints G) * y)) nuU := by
  have : Nonempty (CompactOpenSubgroup (rationalPoints G)) := ⟨⟨⟨K', hK'o⟩, hK'c⟩⟩
  have hf' : f ∈ schwartzSubmodule (rationalXi hK'c hPK') (rationalHeight (F := F) ρ) := by
    rw [← rationalSchwartzSubmodule_eq hKo hKc hPK hK'o hK'c hPK' ρ]
    exact hf
  have ht := (rationalTranslationWeights hK'o hK'c hPK' ρ).translate_mem_schwartzSubmodule
    y x⁻¹ hf'
  have hint := hest.integrable_of_mem_schwartzSubmodule (rationalXi_pos hK'o hK'c hPK')
    (rationalHeight_nonneg ρ) ht 1
  simpa only [translate_apply, inv_inv, OneMemClass.coe_one, one_mul] using hint

/-- **Radical integrability from Proposition II.4.5**, for one group and one standard parabolic
`P_J = M_J U_J`: if `RationalConstantTermEstimateStatement` holds, `K0` is a compact open subgroup
with the structural premises `SimultaneousStandardBasisAt`, `FiniteCartanCovering` and
`StandardLeviCartanCovering` for `J`, and `K'` is a compact open subgroup with
`G(F) = P₀(F) K'` and `M_J(F) = (P₀(F) ∩ M_J(F)) (K' ∩ M_J(F))`, then for every compact open `K`
with `G(F) = P₀(F) K`, every closed `ρ`, every Haar measure `ν_U` on `U_J(F)`, every `f` in the
Schwartz space built from `Ξ_K` and `σ = rationalHeight ρ` and all `x, y ∈ G(F)`, the function
`v ↦ f(x v y)` is `ν_U`-integrable on `U_J(F)`. -/
theorem RationalConstantTermEstimateStatement.integrable_mul_mul
    (h : RationalConstantTermEstimateStatement.{u}) (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    {J : Set (characterLattice S)} (hJ : J ⊆ simpleRelativeRoots i ν)
    {K0 : Subgroup (rationalPoints G)} (hK0o : IsOpen (K0 : Set (rationalPoints G)))
    (hK0c : IsCompact (K0 : Set (rationalPoints G)))
    (hbasis : SimultaneousStandardBasisAt i ν K0)
    (hcover : Aubert.General.RationalPointFamily.FiniteCartanCovering F i ν K0)
    (hLcover : StandardLeviCartanCovering F i ν J K0)
    {K' : Subgroup (rationalPoints G)} (hK'o : IsOpen (K' : Set (rationalPoints G)))
    (hK'c : IsCompact (K' : Set (rationalPoints G)))
    (hPK' : IsIwasawaPair (standardParabolicPoints i ν ∅) K')
    (hM' : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))
      (K'.subgroupOf (standardLeviPoints i ν J)))
    {K : Subgroup (rationalPoints G)} (hKo : IsOpen (K : Set (rationalPoints G)))
    (hKc : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)
    {N : ℕ} [Nonempty (Fin N)] {ρ : MatrixRepresentation G (Fin N)} (hρ : IsClosedSubgroup ρ)
    (nuU : Measure (standardUnipotentPoints i ν J)) [nuU.IsHaarMeasure]
    {f : rationalPoints G → ℂ}
    (hf : f ∈ schwartzSubmodule (rationalXi hKc hPK) (rationalHeight (F := F) ρ))
    (x y : rationalPoints G) :
    Integrable (fun v : standardUnipotentPoints i ν J => f (x * (v : rationalPoints G) * y))
      nuU :=
  integrable_mul_mul_of_constantTermEstimate hKo hKc hPK hK'o hK'c hPK' ρ
    (h.constantTermEstimate hG hi hν hJ hK0o hK0c hbasis hcover hLcover hK'o hK'c hPK' hM' hρ
      nuU) hf x y

end Radical

end Langlands.HarishChandraSchwartz
