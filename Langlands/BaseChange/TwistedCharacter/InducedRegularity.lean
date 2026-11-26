import Langlands.BaseChange.TwistedPaleyWiener
import Langlands.BaseChange.TwistedCharacterSeparation
import Langlands.Representation.Induction.FiniteTwistTrace
import Langlands.Representation.Induction.SurjectivityProof
import Langlands.Representation.Plancherel.RationalUnramifiedDensity

/-! # Finite character expansions of twisted induced distributions -/

noncomputable section

namespace Langlands.BaseChange

open HarmonicAnalysis MeasureTheory Induction

universe uG uM uX

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G]
  {M : Type uM} [Group M] [TopologicalSpace M]
  {X : Type uX} [AddCommGroup X] [Module ℂ X]

set_option maxHeartbeats 800000 in
/-- The twisted trace of a compact-quotient induction at a fixed test has a finite
character expansion, with coefficients chosen before the unramified character. -/
theorem exists_inducedTwistedDistribution_twistCoefficients
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
    (θ : MulAut G) (hθ : Continuous θ) (hθ' : Continuous θ.symm)
    {d : ℕ} (hd : 0 < d) (hθd : θ ^ d = 1)
    (P : Subgroup G) (hcl : IsClosed (P : Set G)) [CompactSpace (LeftQuotient P)]
    (hP : ∀ g, θ g ∈ P ↔ g ∈ P) (p : P →* M) (hpc : Continuous p)
    (θM : M ≃* M) (hp : ∀ x : P, p ⟨θ x, (hP x).2 x.2⟩ = θM (p x))
    (Ξ : Representation ℂ M X) (hΞ : IsAdmissible (Ξ.comp p))
    (B : Ξ.Equiv (Ξ.comp θM.toMonoidHom)) (f : SchwartzBruhat G) :
    ∃ c : M →₀ ℂ, ∀ (ψ : M →* ℂˣ), IsUnramifiedCharacter ψ →
      ∀ (hψθ : ∀ m, ψ (θM m) = ψ m)
        (hI : IsAdmissible (smoothInduced P ((twist ψ Ξ).comp p))),
        twistedDistribution μ _ hI
          (inducedTwistedIntertwiner θ hθ hθ' P hP p θM hp (twist ψ Ξ)
            (twistTwistedIntertwiner θM ψ hψθ B)).toLinearMap f =
          Finsupp.linearCombination ℂ (fun m : M => (ψ m : ℂ)) c := by
  classical
  obtain ⟨K₀, _, hK₀, hf₀⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G {f} ⊤
  obtain ⟨K, hK, hKK₀, hθK⟩ := exists_invariantCompactOpen_le θ hθ hd hθd K₀ hK₀
  have hf : f ∈ Hecke.TestFunction.biInvariant K.toSubgroup K.toSubgroup :=
    Hecke.TestFunction.biInvariant_antitone hKK₀ hKK₀ (hf₀ f (Finset.mem_singleton_self f))
  obtain ⟨t, hcover, hdistinct⟩ := exists_finset_doubleCoset_representatives P K
  have hfactor := hcover
  choose r hr q hq k hk he using hfactor
  let σ₀ := Ξ.comp p
  let U := (i : t) → fixedVectors σ₀ (conjOpenSubgroup P K i).toSubgroup
  let (i : t) : Module.Finite ℂ (fixedVectors σ₀ (conjOpenSubgroup P K i).toSubgroup) :=
    hΞ.2 _
  let b := Module.finBasis ℂ U
  let S := Hecke.fixedLevelActionSamples μ K f hf.2
  let x (y : t) (a : Fin S.size) : G := θ.symm ((y : G) * S.points a)
  let rep (y : t) (a : Fin S.size) : t := ⟨r (x y a), hr _⟩
  let par (y : t) (a : Fin S.size) : P := ⟨q (x y a), hq _⟩
  let coeff (j : Fin (Module.finrank ℂ U)) (y : t) (a : Fin S.size) : ℂ :=
    S.coefficients a * fixedModelCoordinate P σ₀ K t b j y
      (B (Ξ (p (par y a)) (b j (rep y a)).val))
  refine ⟨∑ j, ∑ y : t, ∑ a, Finsupp.single (p (par y a)) (coeff j y a), ?_⟩
  intro ψ hψ hψθ hI
  let χ := ψ.comp p
  let σ := (twist ψ Ξ).comp p
  have hχ (i : t) : (conjOpenSubgroup P K i).toSubgroup ≤ χ.ker := by
    intro g hg
    exact hψ ((conjOpenSubgroup P K i).toSubgroup.map p)
      ((isCompact_conjOpenSubgroup P hcl K hK i).image hpc) (p g) ⟨g, hg, rfl⟩
  let e : fixedVectors (smoothInduced P σ) K.toSubgroup ≃ₗ[ℂ] U :=
    fixedTwistEvaluationEquiv P σ₀ K hK t hcover hdistinct χ hχ
  let A := inducedTwistedIntertwiner θ hθ hθ' P hP p θM hp (twist ψ Ξ)
    (twistTwistedIntertwiner θM ψ hψθ B)
  let Aₖ := fixedVectorsTwistEquiv hθK A
  let T := (Hecke.integratedActionToFixed μ (smoothInduced P σ) hI.1 hf).comp
    ((fixedVectors (smoothInduced P σ) K.toSubgroup).subtype.comp Aₖ.toLinearMap)
  let := hI.2 K
  have htrace : twistedDistribution μ _ hI A.toLinearMap f = LinearMap.trace ℂ _ T := by
    have hrange : ((Hecke.integratedAction μ (smoothInduced P σ) hI.1 f).comp
        A.toLinearMap).range ≤ fixedVectors (smoothInduced P σ) K.toSubgroup := by
      rintro _ ⟨v, rfl⟩
      exact Hecke.integratedAction_mem_fixedVectors μ _ hI.1 hf (A v)
    rw [twistedDistribution_apply, FiniteRankEnd.trace_eq_subspace _ _ hrange]
    rfl
  change twistedDistribution μ _ hI A.toLinearMap f = _
  rw [htrace, ← LinearMap.trace_conj' T e, LinearMap.trace_eq_matrix_trace ℂ b]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
    ← Module.Basis.coord_apply, LinearEquiv.conj_apply_apply]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← fixedModelCoordinate_sum P σ₀ K t b j (e (T (e.symm (b j)))), map_sum]
  apply Finset.sum_congr rfl
  intro y _
  let L : SmoothFunctions P σ →ₗ[ℂ] ℂ :=
    { toFun := fun v => fixedModelCoordinate P σ₀ K t b j y (eval P σ v y)
      map_add' := fun _ _ => (fixedModelCoordinate P σ₀ K t b j y).map_add _ _
      map_smul' := fun _ _ => (fixedModelCoordinate P σ₀ K t b j y).map_smul _ _ }
  let v := e.symm (b j)
  change L (Hecke.integratedAction μ (smoothInduced P σ) hI.1 f (A v.val)) = _
  have hv : A v.val ∈ fixedVectors (smoothInduced P σ) K.toSubgroup :=
    (Aₖ v).property
  rw [Hecke.fixedLevelActionSamples_action μ K f hf.2 _ hI.1 _ hv, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_smul, Finsupp.linearCombination_single]
  have hval : eval P σ v.val (rep y a) = (b j (rep y a)).val := by
    have h := congrArg (fun u : U => (u (rep y a)).val) (e.apply_symm_apply (b j))
    exact h
  have hpoint : x y a = (par y a : G) * (rep y a : G) *
      (⟨k (x y a), hk (x y a)⟩ : K) := he (x y a)
  change S.coefficients a • fixedModelCoordinate P σ₀ K t b j y
    (eval P σ (A v.val) ((y : G) * S.points a)) =
      coeff j y a • (ψ (p (par y a)) : ℂ)
  rw [eval_inducedTwistedIntertwiner]
  change S.coefficients a • fixedModelCoordinate P σ₀ K t b j y
    (B (eval P σ v.val (x y a))) = _
  rw [hpoint, eval_mul_of_mem_fixedVectors P σ K.toSubgroup v.property,
    eval_covariant, hval]
  change S.coefficients a • fixedModelCoordinate P σ₀ K t b j y
    (B.toLinearMap ((ψ (p (par y a)) : ℂ) • Ξ (p (par y a)) (b j (rep y a)).val)) = _
  rw [map_smul, map_smul]
  simp only [coeff, smul_eq_mul]
  ring_nf
  rfl

omit [TopologicalSpace M] in
/-- A finite sum of character evaluations with integral exponent coordinates
is a Laurent polynomial in those coordinates. -/
theorem exists_finiteLaurentEvaluation_of_characterCoefficients {n : ℕ}
    (c : M →₀ ℂ) (exponent : M → (Fin n → ℤ))
    (ψ : (Fin n → ℂˣ) → M →* ℂˣ)
    (hψ : ∀ z m, (ψ z m : ℂ) = ∏ i, ((z i ^ exponent m i : ℂˣ) : ℂ)) :
    ∃ q : AddMonoidAlgebra ℂ (Fin n → ℤ), ∀ z,
      Finsupp.linearCombination ℂ (fun m : M => (ψ z m : ℂ)) c =
        Plancherel.finiteLaurentEvaluation z q := by
  refine ⟨∑ m ∈ c.support, AddMonoidAlgebra.single (exponent m) (c m), fun z => ?_⟩
  simp_rw [map_sum, Plancherel.finiteLaurentEvaluation_single, ← hψ]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul]

end Langlands.BaseChange
