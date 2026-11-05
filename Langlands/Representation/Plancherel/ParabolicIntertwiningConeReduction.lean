import Langlands.Representation.Plancherel.ParabolicOppositeQuotient
import Langlands.Representation.Plancherel.CompactIntertwiningQuotientDecay

/-! # Convergence and domination on actual parabolic regions from the cone decay -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure Filter Topology
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.GroupScheme.MatrixRepresentation
open Aubert.General Induction StandardIntertwining

section Host

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {M G P P' U U' : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom]
  [IsAffine M.X.left]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)
  {p' : P' ⟶ G} {l' : M ⟶ P'} (r' : ParabolicRootPresentation p' l' a)
  (hLevi : l ≫ p = l' ≫ p')
  {n : U ⟶ P} {n' : U' ⟶ P'} (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
  (hn' : LeviSubgroup.IsGeometricUnipotentRadical n')

local instance coneReductionAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance coneReductionTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X
local instance coneReductionTopologicalGroup : IsTopologicalGroup (rationalPoints G) :=
  rationalPoint_isTopologicalGroup F G

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  [T2Space (rationalPoints G)]
  {Ppt Upt P'pt U'pt : Subgroup (rationalPoints G)}
  (hPpt : Ppt = (SubgroupFunctor.range p).carrier (Over.mk (𝟙 _)))
  (hUpt : Upt = (SubgroupFunctor.range (n ≫ p)).carrier (Over.mk (𝟙 _)))
  (hU'pt : U'pt = (SubgroupFunctor.range (n' ≫ p')).carrier (Over.mk (𝟙 _)))

/-- **The cone decay on the opposite chart.** For a closed representation `ρ₀` of `G` with
height `‖·‖ = rationalMatrixNorm F ρ₀` and a family of character regions `C R`: for every
exponent `d` and every `s` there is a threshold `R` such that, for the section `σ` of
`(U ∩ U') \ U'` with values in `Ū ∩ U'`, the weights `‖δ(m)‖ ‖χ(m)‖ ‖m‖ ^ d` decay like
`‖σ q‖ ^ (-s)`, locally uniformly on `C R`. This is the decay estimate behind Waldspurger IV.1.1;
it is a hypothesis here. -/
def ParabolicOppositeConeDecay (h : IsSemidirectDecomposition Ppt (parabolicLeviPointSubgroup p l) Upt)
    (hU : IsClosed (Upt : Set (rationalPoints G))) (K : OpenSubgroup (rationalPoints G))
    {N : ℕ} [Nonempty (Fin N)] (ρ₀ : MatrixRepresentation G (Fin N))
    (C : ℝ → Set (unramifiedCharacters (parabolicLeviRationalNormCharacters r))) : Prop :=
  ∀ (d : ℕ) (s : ℝ), ∃ R : ℝ,
    ∀ σ : QuotientSpace (U := Upt) U'pt → U'pt, (∀ q, Quotient.mk _ (σ q) = q) →
      (∀ q, ((σ q : U'pt) : rationalPoints G) ∈ parabolicOppositeRadicalPoints r) →
      IsLocallyUniformQuotientDecayOn h hU K (parabolicLeviRationalNormCharacters r) U'pt σ
        (fun m => rationalMatrixNorm F ρ₀ (m : rationalPoints G) ^ d)
        (fun q => rationalMatrixNorm F ρ₀ ((σ q : U'pt) : rationalPoints G) ^ (-s)) (C R)

include r r' hLevi hn hn' hPpt hUpt hU'pt in
/-- **Region inputs from the cone decay.** Under squared-modulus compatibility, admissibility
and a common coefficient growth exponent for `π` against the height of a closed
representation `ρ₀`, the cone decay gives one threshold `R` with full convergence of the actual
standard integral at every character of `C R` and local integrable domination of the compact
integrands on `C R`. These are exactly the per-representation conclusions asked for by the
remaining-inputs reduction of the conditional intertwining statement. -/
theorem exists_region_convergence_domination_of_coneDecay
    (h : IsSemidirectDecomposition Ppt (parabolicLeviPointSubgroup p l) Upt)
    (hU : IsClosed (Upt : Set (rationalPoints G)))
    (h' : IsSemidirectDecomposition P'pt (parabolicLeviPointSubgroup p l) U'pt)
    (hU' : IsClosed (U'pt : Set (rationalPoints G)))
    (hP : IsClosed (Ppt : Set (rationalPoints G)))
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (hPK : ∀ g : rationalPoints G, ∃ p : Ppt, ∃ k : K,
      g = (p : rationalPoints G) * (k : rationalPoints G))
    (hr : Continuous h.projection)
    [MeasurableSpace U'pt] [BorelSpace U'pt]
    [MeasurableSpace (Upt.subgroupOf U'pt)] [BorelSpace (Upt.subgroupOf U'pt)]
    [MeasurableSpace (QuotientSpace (U := Upt) U'pt)]
    [BorelSpace (QuotientSpace (U := Upt) U'pt)]
    (qν : Measure (QuotientSpace (U := Upt) U'pt))
    (μU' : Measure U'pt) (μI : Measure (Upt.subgroupOf U'pt))
    [IsHaarMeasure μU'] [μU'.Regular] [IsMulRightInvariant μU']
    [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
    (hqν : QuotientIntegration.IsCompatible (Upt.subgroupOf U'pt) μU' μI qν)
    (hsq : SquaredModulusCompatibility h hU h' hU')
    {N : ℕ} [Nonempty (Fin N)] (ρ₀ : MatrixRepresentation G (Fin N)) (hρ₀ : IsClosedSubgroup ρ₀)
    (C : ℝ → Set (unramifiedCharacters (parabolicLeviRationalNormCharacters r)))
    (hcone : ParabolicOppositeConeDecay r (U'pt := U'pt) h hU K ρ₀ C)
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)) (hadm : π.IsAdmissible)
    (hgrowth : ∃ d : ℕ, ∀ (v : π) (ℓ : SmoothDual π.representation),
      ∃ c : ℝ, 0 < c ∧ ∀ m, ‖ℓ.val (π.representation m v)‖ ≤
        c * rationalMatrixNorm F ρ₀ (m : rationalPoints G) ^ d) :
    ∃ R : ℝ,
      (∀ χ : C R, domain h hU U'pt
        (π.twist χ.val.val.toMonoidHom
          (unramifiedCharacter_isOpen_ker (parabolicLeviRationalNormCharacters r) χ.val)) qν = ⊤) ∧
      ∀ (hδ : IsUnimodularModulus Upt hU),
        CompactIntegralLocallyDominatedOn h hU hδ K hP hK hPK
          (parabolicLeviRationalNormCharacters r) (continuous_parabolicLeviRationalNormCharacters r)
          hr π U'pt qν (C R) := by
  obtain ⟨t, ht⟩ := BruhatTits.DynamicUnipotentContainment.exists_unit_tendsto_pow_zero (F := F)
  set hc := parabolic_isOpenCellContraction r r' hLevi hn hn' hPpt hUpt hU'pt h' t ht
  have : qν.Regular := hqν.regular
  obtain ⟨D, hD⟩ := exists_integrable_quotientChart_symm_rationalMatrixNorm r r' hLevi hn hn'
    hPpt hUpt hU'pt h' hU' ρ₀ hρ₀ t ht qν hqν.right_invariant
  obtain ⟨d, hd⟩ := hgrowth
  obtain ⟨R, hR⟩ := hcone d (D + 1)
  let σ : QuotientSpace (U := Upt) U'pt → U'pt := fun q => (hc.quotientChart.symm q : U'pt)
  have hσ : ∀ q, Quotient.mk _ (σ q) = q := fun q => by
    have h1 := hc.quotientChart.apply_symm_apply q
    rw [HarishChandraSchwartz.IsOpenCellContraction.quotientChart_apply] at h1
    exact h1
  have hσŪ : ∀ q, ((σ q : U'pt) : rationalPoints G) ∈ parabolicOppositeRadicalPoints r :=
    fun q => (hc.quotientChart.symm q).2
  have hdecay := hR σ hσ hσŪ
  have hW : Integrable (fun q => rationalMatrixNorm F ρ₀ ((σ q : U'pt) : rationalPoints G) ^
      (-((D : ℝ) + 1))) qν := hD _ (by linarith)
  have hξ : ∀ m : parabolicLeviPointSubgroup p l,
      0 ≤ rationalMatrixNorm F ρ₀ (m : rationalPoints G) ^ d :=
    fun m => pow_nonneg (zero_le_one.trans (one_le_rationalMatrixNorm F ρ₀ _)) d
  refine ⟨R, fun χ => ?_, fun hδ => ?_⟩
  · have hscalar := scalarDomain_twist_eq_top_of_quotientDecay h hU K
      (parabolicLeviRationalNormCharacters r) U'pt hK hPK π qν _ hξ hd σ hσ _ hW hdecay χ.val
      χ.2
    rw [← scalarDomain_eq_domain h hU U'pt _ qν h' hU' μU' μI hqν
      (isClosed_parabolicLeviPointSubgroup r)
      ((SmoothRep.isAdmissible_twist_iff _ _ π).mpr hadm) hsq]
    exact hscalar
  · exact compactIntegralLocallyDominatedOn_of_quotientDecay h hU K
      (parabolicLeviRationalNormCharacters r) U'pt hδ hP hK hPK
      (continuous_parabolicLeviRationalNormCharacters r) hr π qν _ hξ hd σ hσ _ hW hdecay

end Host

end Langlands.Plancherel
