import Langlands.Global.ArthurTruncationRapidDecayReduction
import Langlands.Global.AdelicEisensteinUnitaryGrowthStatement
import Langlands.Global.AdelicEisensteinContinuationLocalFrechet
import Langlands.Global.EisensteinContinuationNormalization
import Langlands.Automorphic.GroupSchemeUniformGrowthRemovableSingularity

/-! # Uniform moderate growth of Eisenstein series on compact sets of unitary parameters from
their meromorphic continuation

`EisensteinUnitaryUniformGrowthStatement` follows from the meromorphic continuation of
Eisenstein series in the Fréchet spaces of uniform moderate growth
(`EisensteinMeromorphicContinuationStatement`, Bernstein–Lapid Theorem 2.3 (1) with the
Corollary of §8.6). -/

noncomputable section

open CategoryTheory AlgebraicGeometry Filter Metric Set
open scoped CategoryTheory.MonObj Topology Manifold

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

section Growth

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] {N d : ℕ} {rho : MatrixRepresentation G (Fin N)}
  {hsmooth : SmoothOfRelativeDimension d G.X.hom}
  {hcalc : AdelicDifferentialCommutator F G hsmooth}
  {hN : 0 < N} {hrho : IsClosedSubgroup rho} {R : ℝ} {L : Subgroup (FiniteAdelicGroupPoints F G)}

/-- The derivative `u w` of a vector `w` of `𝔉^R_L` is bounded by the seminorm of `w` along `u`
times the weight `‖g‖^R`. -/
theorem UniformGrowthFrechetSpace.norm_evaluate_le (u : AdelicEnvelopingAlgebra F G hsmooth)
    (w : UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L)
    (g : AdelicGroupPoints F G) :
    ‖evaluate F G (adelicEnvelopingAction F G hsmooth hcalc u
        (w : uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L).val).val g‖ ≤
      ‖weightedDerivativeCLM F G rho hsmooth hcalc hN hrho R L u w‖ *
        RepresentationGrowth.adelicSourceNorm F G rho g ^ R := by
  have hpos : 0 < RepresentationGrowth.adelicSourceNorm F G rho g ^ R :=
    Real.rpow_pos_of_pos (RepresentationGrowth.adelicSourceNorm_pos F G rho hN g) R
  have h := lp.norm_apply_le_norm ENNReal.top_ne_zero
    (weightedDerivativeCLM F G rho hsmooth hcalc hN hrho R L u w) g
  rw [weightedDerivativeCLM_apply, weightedDerivative_apply, norm_mul, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos, ← div_eq_mul_inv,
    div_le_iff₀ hpos] at h
  exact h

end Growth

/-- Change of exponent: on `[c₀, ∞)` with `c₀ > 0`, `x^{R'} ≤ c₀^{R' - R} x^R` for `R' ≤ R`. -/
theorem rpow_le_rpow_sub_mul_rpow {c₀ x R R' : ℝ} (hc : 0 < c₀) (hx : c₀ ≤ x) (hR : R' ≤ R) :
    x ^ R' ≤ c₀ ^ (R' - R) * x ^ R := by
  have hx0 : 0 < x := hc.trans_le hx
  calc x ^ R' = x ^ (R' - R) * x ^ R := by rw [← Real.rpow_add hx0, sub_add_cancel]
    _ ≤ c₀ ^ (R' - R) * x ^ R := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos hc hx (by linarith)) (Real.rpow_nonneg hx0.le _)

/-- Real coordinates of the imaginary parameters, read in complex linear coordinates: for real
linear coordinates `e` of `X^*(P) ⊗ ℝ` there are complex linear coordinates `e₀` of
`X^*(P) ⊗ ℂ` and a continuous map `A` with `e₀ (A x) = i e(x)`. -/
theorem exists_imaginary_coordinates {F : Type} [Field F]
    {P : GroupScheme (Spec (CommRingCat.of F))}
    [FiniteDimensional ℂ (ComplexCharacterParameter F P)] {n : ℕ}
    (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P) :
    ∃ (m : ℕ) (e₀ : (Fin m → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P)
      (A : (Fin n → ℝ) → Fin m → ℂ), Continuous A ∧
      ∀ x, e₀ (A x) = imaginaryParameter F P (e x) := by
  let m := Module.finrank ℂ (ComplexCharacterParameter F P)
  let e₀ : (Fin m → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P :=
    (Module.finBasis ℂ (ComplexCharacterParameter F P)).equivFun.symm
  let Aℝ : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℂ) :=
    (e₀.symm.toLinearMap.restrictScalars ℝ) ∘ₗ (imaginaryParameter F P) ∘ₗ e.toLinearMap
  refine ⟨m, e₀, Aℝ, LinearMap.continuous_of_finiteDimensional Aℝ, fun x => ?_⟩
  simp only [Aℝ, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]

section Eisenstein

variable {F : Type} [Field F] [NumberField F]
  {G P M U : GroupScheme (Spec (CommRingCat.of F))}
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left]
  {iU : U ⟶ P} {l : M ⟶ P} {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a)
  [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
  [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
  (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)

/-- Given the meromorphic continuation of Eisenstein series, a pointwise continuation `E` of
the Eisenstein series of an automorphic form on `U(𝔸) M(F) \ G(𝔸)` is, near every point of a
linear chart, the underlying function of a meromorphic function with values in a space
`𝔉^R_L` of uniform moderate growth with `L` open, on the domain of holomorphy of that
function. -/
theorem exists_local_frechet_open_of_eisensteinContinuation
    (hMero : EisensteinMeromorphicContinuationStatement.{0}) (hG : IsConnectedReductive G)
    (hUR : LeviSubgroup.IsGeometricUnipotentRadical iU) {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) (hrho : IsClosedSubgroup rho)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (hKmax : IsMaximalCompactSubgroup F G K)
    {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
      (K.comap (ofInfinite F G).toMonoidHom) rho φ)
    {E : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ}
    {D : Set (ComplexCharacterParameter F P)}
    (hE : ∀ g, IsMeromorphicInCoordinatesOn (fun lam => E lam g) D)
    (hreg : ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → E lam = hK.eisensteinSeries φ lam)
    {m : ℕ} (e₀ : (Fin m → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P) (s₀ : Fin m → ℂ) :
    ∃ W : TopologicalSpace.Opens (Fin m → ℂ), s₀ ∈ W ∧
      ∃ (R : ℝ) (L : Subgroup (FiniteAdelicGroupPoints F G)),
        IsOpen (L : Set (FiniteAdelicGroupPoints F G)) ∧
        ∃ (f : W → UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L) (Df : Set W),
        IsMeromorphicOn 𝓘(ℂ, Fin m → ℂ) f Df ∧
        ∀ t ∈ Df, UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L (f t) =
          E (e₀ t) := by
  classical
  have := finiteDimensional_complexCharacterParameter r hG
  obtain ⟨Ea, ⟨R₀, hR₀⟩, hloc⟩ :=
    hMero F G P M U A p iU l a r hA hT hG hUR K hK rho hN hrho hsmooth hcalc φ hKmax hφ
  have hdata : ∀ s₁ : Fin m → ℂ,
      HasLocalMeromorphicData (fun (g : AdelicGroupPoints F G) s => Ea (e₀ s) g) s₁ := by
    intro s₁
    obtain ⟨W, hs₁, R, L, -, f, Df, hf, hfD⟩ := hloc m e₀ s₁
    refine hasLocalMeromorphicData_of_isMeromorphicOn hf (fun g => uniformGrowthEvalCLM g)
      (fun t ht g => ?_) hs₁
    change UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L (f t) g = _
    rw [(hfD t ht).1]
  obtain ⟨U₀, hU₀⟩ := exists_isMeromorphicOn_of_local hdata
  have hEa : ∀ g, IsMeromorphicInCoordinatesOn (fun lam => Ea lam g) (e₀ '' U₀) := fun g =>
    isMeromorphicInCoordinatesOn_of_coordinates e₀ (by
      rw [e₀.injective.preimage_image]
      exact hU₀ g)
  obtain ⟨R₁, hR₁⟩ := hreg
  have heq : ∀ g, EqOn (fun lam => E lam g) (fun lam => Ea lam g) (D ∩ e₀ '' U₀) := fun g =>
    r.eqOn_of_regularParameter hA hT hG (hE g) (hEa g) (max R₁ R₀) fun lam hlam => by
      rw [hR₁ lam (isRegularParameter_mono r hA hT (le_max_left _ _) hlam),
        hR₀ lam (isRegularParameter_mono r hA hT (le_max_right _ _) hlam)]
  obtain ⟨W, hs₀, R, L, hL, f, Df, hf, hfD⟩ := hloc m e₀ s₀
  have hO := ((hE 1).isOpenDenseInCoordinates.inter (hEa 1).isOpenDenseInCoordinates) m e₀
  refine ⟨W, hs₀, R, L, hL, f, Df ∩ Subtype.val ⁻¹' (e₀ ⁻¹' (D ∩ e₀ '' U₀)), ?_, ?_⟩
  · exact hf.mono_of_isOpen_of_dense (hf.1.inter (hO.1.preimage continuous_subtype_val))
      (hf.2.1.inter_of_isOpen_left (hO.2.preimage W.isOpen.isOpenMap_subtype_val) hf.1)
      inter_subset_left
  · rintro t ⟨htD, htU⟩
    funext g
    rw [(hfD t htD).1]
    exact (heq g htU).symm

/-- **Local uniform bounds.** Given the meromorphic continuation of Eisenstein series, let `E`
be a pointwise continuation of the Eisenstein series of an automorphic form on
`U(𝔸) M(F) \ G(𝔸)`, meromorphic in coordinates with domain of holomorphy `D`. Near every point
`s₀` of `D`, read in a linear chart `e₀`, there are a ball, an exponent `R`, an open level `L`
and vectors `v s ∈ 𝔉^R_L` with underlying functions `E (e₀ s)` on the ball, bounded in every
seminorm of `𝔉^R_L` on the ball. -/
theorem exists_local_uniformGrowth_bound
    (hMero : EisensteinMeromorphicContinuationStatement.{0}) (hG : IsConnectedReductive G)
    (hUR : LeviSubgroup.IsGeometricUnipotentRadical iU) {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) (hrho : IsClosedSubgroup rho)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (hKmax : IsMaximalCompactSubgroup F G K)
    {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
      (K.comap (ofInfinite F G).toMonoidHom) rho φ)
    {E : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ}
    {D : Set (ComplexCharacterParameter F P)}
    (hE : ∀ g, IsMeromorphicInCoordinatesOn (fun lam => E lam g) D)
    (hreg : ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → E lam = hK.eisensteinSeries φ lam)
    {m : ℕ} (e₀ : (Fin m → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P) {s₀ : Fin m → ℂ}
    (hs₀ : e₀ s₀ ∈ D) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ (R : ℝ) (L : Subgroup (FiniteAdelicGroupPoints F G)),
      IsOpen (L : Set (FiniteAdelicGroupPoints F G)) ∧
      ∃ v : (Fin m → ℂ) → UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L,
        (∀ s ∈ ball s₀ ε,
          UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L (v s) = E (e₀ s)) ∧
        ∀ u : AdelicEnvelopingAlgebra F G hsmooth, ∃ B : ℝ, ∀ s ∈ ball s₀ ε,
          ‖weightedDerivativeCLM F G rho hsmooth hcalc hN hrho R L u (v s)‖ ≤ B := by
  classical
  obtain ⟨W, hs₀W, R, L, hL, f, Df, hf, hfD⟩ :=
    exists_local_frechet_open_of_eisensteinContinuation r hA hT hK hMero hG hUR rho hN hrho
      hsmooth hcalc hKmax hφ hE hreg e₀ s₀
  let 𝔉 := UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L
  let eval : 𝔉 →ₗ[ℂ] (AdelicGroupPoints F G → ℂ) :=
    { toFun := UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  obtain ⟨W₁, U₁, den, H, hW₁o, hs₀W₁, hU₁o, hW₁U₁, hden, hH, hU₁⟩ :=
    IsMeromorphicOn.exists_flat_numerator hf eval (fun s => E (e₀ s)) hfD ⟨s₀, hs₀W⟩
  have hDo : IsOpen (e₀ ⁻¹' D) := ((hE 1).2 m e₀).1
  have hΦ : ∀ y, DifferentiableOn ℂ (fun s => E (e₀ s) y) (e₀ ⁻¹' D) := fun y =>
    differentiableOn_of_isHolomorphicOn ((hE y).2 m e₀).2.2.1
  set U₀ := W₁ ∩ e₀ ⁻¹' D with hU₀
  have hU₀o : IsOpen U₀ := hW₁o.inter hDo
  have hs₀U₀ : s₀ ∈ U₀ := ⟨hs₀W₁, hs₀⟩
  -- the relation between numerator, denominator and `E` on `U₀`
  have heq : ∀ s ∈ U₀, ∀ y,
      UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L (H s) y =
        den s * E (e₀ s) y := by
    intro s hs y
    have hcl : U₀ ⊆ closure (U₀ ∩ U₁) := fun t ht => hU₀o.inter_closure ⟨ht, hW₁U₁ ht.1⟩
    have hL' : ContinuousOn (fun t =>
        UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L (H t) y) U₀ :=
      ((hH (uniformGrowthEvalCLM y)).mono inter_subset_left).continuousOn
    have hR' : ContinuousOn (fun t => den t * E (e₀ t) y) U₀ :=
      ((hden.mono inter_subset_left).mul ((hΦ y).mono inter_subset_right)).continuousOn
    refine EqOn.of_subset_closure (fun t ht => ?_) hL' hR' inter_subset_left hcl hs
    have h := congrFun (hU₁ t ht.2).2.2 y
    rw [Pi.smul_apply, smul_eq_mul] at h
    exact h
  -- the denominator has nonzero germ at `s₀`
  have hdne : ¬ den =ᶠ[𝓝 s₀] 0 := by
    intro h0
    obtain ⟨t, ht0, htU⟩ := mem_closure_iff_nhds.mp (hW₁U₁ hs₀W₁) _ h0
    exact (hU₁ t htU).2.1 ht0
  obtain ⟨V, hVU, hVo, hs₀V, v, hv, hvE⟩ :=
    UniformGrowthFrechetSpace.exists_weaklyHolomorphic_of_mul_eq_eval F G rho hsmooth hcalc hN
      hrho R L hL hU₀o hs₀U₀ (hden.mono inter_subset_left)
      hdne (fun test => (hH test).mono inter_subset_left)
      (fun y => (hΦ y).mono inter_subset_right) heq
  have hvc : ContinuousOn v V :=
    UniformGrowthFrechetSpace.continuousOn_of_differentiableOn_dual F G rho hsmooth hcalc hN hrho
      R L hVo hv
  obtain ⟨δ, hδ, hδV⟩ := Metric.isOpen_iff.mp hVo s₀ hs₀V
  refine ⟨δ / 2, half_pos hδ, R, L, hL, v, fun s hs => hvE s (hδV (ball_subset_ball
    (half_le_self hδ.le) hs)), fun u => ?_⟩
  have hsub : closedBall s₀ (δ / 2) ⊆ V :=
    (closedBall_subset_ball (half_lt_self hδ)).trans hδV
  obtain ⟨B, hB⟩ := (isCompact_closedBall s₀ (δ / 2)).exists_bound_of_continuousOn
    (((weightedDerivativeCLM F G rho hsmooth hcalc hN hrho R L u).continuous.comp_continuousOn
      hvc).mono hsub)
  exact ⟨B, fun s hs => hB s (ball_subset_closedBall hs)⟩

/-- **Uniform growth on a compact set of unitary parameters, `N > 0`.** Given the meromorphic
continuation of Eisenstein series, a pointwise continuation `E` of the Eisenstein series of an
automorphic form on `U(𝔸) M(F) \ G(𝔸)` whose domain of holomorphy contains `i𝔞_P^*` has uniform
moderate growth on every compact set of real coordinates of `i𝔞_P^*`. -/
theorem exists_uniformGrowthFamily_of_pos
    (hMero : EisensteinMeromorphicContinuationStatement.{0}) (hG : IsConnectedReductive G)
    (hUR : LeviSubgroup.IsGeometricUnipotentRadical iU) {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) (hrho : IsClosedSubgroup rho)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (hKmax : IsMaximalCompactSubgroup F G K)
    {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
      (K.comap (ofInfinite F G).toMonoidHom) rho φ)
    {E : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ}
    {D : Set (ComplexCharacterParameter F P)} (hD : range (imaginaryParameter F P) ⊆ D)
    (hE : ∀ g, IsMeromorphicInCoordinatesOn (fun lam => E lam g) D)
    (hreg : ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → E lam = hK.eisensteinSeries φ lam)
    {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P) {C : Set (Fin n → ℝ)}
    (hC : IsCompact C) :
    ∃ (L : Subgroup (FiniteAdelicGroupPoints F G)) (R : ℝ)
      (f : (Fin n → ℝ) → FinitePlotSmoothRationalFunctions F G),
      IsOpen (L : Set (FiniteAdelicGroupPoints F G)) ∧
      (∀ x ∈ C, evaluate F G (f x).val = E (imaginaryParameter F P (e x))) ∧
      IsUniformGrowthFamily rho hsmooth hcalc L R f C := by
  classical
  have := (hE 1).1
  obtain ⟨m, e₀, Aℝ, hAc, hAe⟩ := exists_imaginary_coordinates (F := F) (P := P) e
  have hAD : ∀ x, e₀ (Aℝ x) ∈ D := fun x => by rw [hAe]; exact hD ⟨e x, rfl⟩
  choose ε hε R L hL v hvE hvB using fun x : Fin n → ℝ =>
    exists_local_uniformGrowth_bound r hA hT hK hMero hG hUR rho hN hrho hsmooth hcalc hKmax hφ
      hE hreg e₀ (hAD x)
  choose B hB using hvB
  -- a finite subcover of `C`
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun x : C => Aℝ ⁻¹' ball (Aℝ x) (ε x))
    (fun x => isOpen_ball.preimage hAc)
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hε x)⟩)
  have hidx : ∀ x ∈ C, ∃ i : C, i ∈ t ∧ Aℝ x ∈ ball (Aℝ i) (ε i) := fun x hx => by
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (ht hx)
    exact ⟨i, hi, hxi⟩
  choose idx hidxt hidxb using hidx
  -- one exponent, one level and one lower bound for the norm
  set Rm : ℝ := ∑ i ∈ t, |R i| with hRm
  have hRle : ∀ i ∈ t, R i ≤ Rm := fun i hi =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun j : C => |R j|)
      (fun j _ => abs_nonneg _) hi)
  let Lm : Subgroup (FiniteAdelicGroupPoints F G) := ⨅ i : t, L (i : C)
  have hLm : IsOpen (Lm : Set (FiniteAdelicGroupPoints F G)) := by
    simp only [Lm, Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun i => hL _
  have hLle : ∀ i ∈ t, Lm ≤ L i := fun i hi => iInf_le (fun j : t => L (j : C)) ⟨i, hi⟩
  obtain ⟨c₀, hc₀, hc₀le⟩ := Langlands.Global.ArthurTruncation.exists_pos_le_adelicSourceNorm (F := F) (G := G) rho hN
  -- the family
  let f : (Fin n → ℝ) → FinitePlotSmoothRationalFunctions F G := fun x =>
    if hx : x ∈ C then
      ((v (idx x hx) (Aℝ x) : uniformGrowthLevelSubmodule F G rho hsmooth hcalc
        (R (idx x hx)) (L (idx x hx)))).val
    else 0
  have hf : ∀ x (hx : x ∈ C), f x = ((v (idx x hx) (Aℝ x) : uniformGrowthLevelSubmodule F G
      rho hsmooth hcalc (R (idx x hx)) (L (idx x hx)))).val := fun x hx => by
    simp only [f, dite_eq_left hx]
  refine ⟨Lm, Rm, f, hLm, fun x hx => ?_, fun x hx => ?_, fun u => ?_⟩
  · rw [hf x hx, ← hAe x]
    exact hvE (idx x hx) (Aℝ x) (hidxb x hx)
  · intro l hl
    rw [hf x hx]
    exact (v (idx x hx) (Aℝ x) : uniformGrowthLevelSubmodule F G rho hsmooth hcalc
      (R (idx x hx)) (L (idx x hx))).property.1 l (hLle _ (hidxt x hx) hl)
  · refine ⟨∑ i ∈ t, max (B i u) 0 * c₀ ^ (R i - Rm), fun x hx g => ?_⟩
    set i := idx x hx
    have hi : i ∈ t := hidxt x hx
    have hnorm := hc₀le g
    have hterm : max (B i u) 0 * c₀ ^ (R i - Rm) ≤
        ∑ j ∈ t, max (B j u) 0 * c₀ ^ (R j - Rm) :=
      Finset.single_le_sum (f := fun j : C => max (B j u) 0 * c₀ ^ (R j - Rm))
        (fun j _ => mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hc₀.le _)) hi
    rw [hf x hx]
    calc _ ≤ ‖weightedDerivativeCLM F G rho hsmooth hcalc hN hrho (R i) (L i) u
            (v i (Aℝ x))‖ * RepresentationGrowth.adelicSourceNorm F G rho g ^ R i :=
          UniformGrowthFrechetSpace.norm_evaluate_le u (v i (Aℝ x)) g
      _ ≤ max (B i u) 0 * RepresentationGrowth.adelicSourceNorm F G rho g ^ R i :=
          mul_le_mul_of_nonneg_right ((hB i u (Aℝ x) (hidxb x hx)).trans (le_max_left _ _))
            (Real.rpow_nonneg (hc₀.le.trans hnorm) _)
      _ ≤ max (B i u) 0 * (c₀ ^ (R i - Rm) *
            RepresentationGrowth.adelicSourceNorm F G rho g ^ Rm) :=
          mul_le_mul_of_nonneg_left (rpow_le_rpow_sub_mul_rpow hc₀ hnorm (hRle i hi))
            (le_max_right _ _)
      _ = (max (B i u) 0 * c₀ ^ (R i - Rm)) *
            RepresentationGrowth.adelicSourceNorm F G rho g ^ Rm := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hterm
            (Real.rpow_nonneg (hc₀.le.trans hnorm) _)

end Eisenstein

section RankZero

variable {F : Type} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]

/-- **Uniform growth for a closed embedding into `GL_0`.** Then `G(𝔸)` is a point; a family `E`
of functions on it, meromorphic in the parameter with a domain of holomorphy containing
`i𝔞_P^*`, has uniform moderate growth with exponent `0` on every compact set of real
coordinates of `i𝔞_P^*`. -/
theorem exists_uniformGrowthFamily_of_rank_zero {d : ℕ}
    (rho : MatrixRepresentation G (Fin 0)) (hrho : IsClosedSubgroup rho)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth)
    {E : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ}
    {D : Set (ComplexCharacterParameter F P)} (hD : range (imaginaryParameter F P) ⊆ D)
    (hE : ∀ g, IsMeromorphicInCoordinatesOn (fun lam => E lam g) D)
    {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P) {C : Set (Fin n → ℝ)}
    (hC : IsCompact C) :
    ∃ (L : Subgroup (FiniteAdelicGroupPoints F G)) (R : ℝ)
      (f : (Fin n → ℝ) → FinitePlotSmoothRationalFunctions F G),
      IsOpen (L : Set (FiniteAdelicGroupPoints F G)) ∧
      (∀ x ∈ C, evaluate F G (f x).val = E (imaginaryParameter F P (e x))) ∧
      IsUniformGrowthFamily rho hsmooth hcalc L R f C := by
  classical
  have := (hE 1).1
  have hsub := subsingleton_adelicGroupPoints_of_rank_zero rho hrho
  obtain ⟨m, e₀, Aℝ, hAc, hAe⟩ := exists_imaginary_coordinates (F := F) (P := P) e
  -- the values at the single point of `G(𝔸)` are continuous in the real coordinates
  let c : (Fin n → ℝ) → ℂ := fun x => E (imaginaryParameter F P (e x)) 1
  have hc : Continuous c := by
    have h1 : ContinuousOn (fun s => E (e₀ s) 1) (e₀ ⁻¹' D) :=
      (differentiableOn_of_isHolomorphicOn ((hE 1).2 m e₀).2.2.1).continuousOn
    have h2 := h1.comp_continuous hAc (fun x => show e₀ (Aℝ x) ∈ D by
      rw [hAe]; exact hD ⟨e x, rfl⟩)
    refine h2.congr fun x => ?_
    simp only [Function.comp_apply, hAe, c]
  obtain ⟨Bc, hBc⟩ := hC.exists_bound_of_continuousOn hc.continuousOn
  -- the constant function `1`
  let one : FinitePlotSmoothRationalFunctions F G :=
    ofRationalSmoothFunction F G (fun _ => (1 : ℂ)) (fun _ _ _ => rfl)
      ⟨continuous_const, fun _ => G.isPlotSmooth_const _ _ 1, ⊤,
        by rw [Subgroup.coe_top]; exact isOpen_univ, fun _ _ _ => rfl⟩
  refine ⟨⊤, 0, fun x => c x • one, by rw [Subgroup.coe_top]; exact isOpen_univ,
    fun x _ => ?_, fun x _ l _ => ?_, fun u => ?_⟩
  · funext g
    change c x * 1 = E (imaginaryParameter F P (e x)) g
    rw [mul_one, Subsingleton.elim g 1]
  · rw [Subsingleton.elim (AdelicGroupPoints.ofFinite F G l) 1, map_one]
    rfl
  · refine ⟨Bc * ‖evaluate F G (adelicEnvelopingAction F G hsmooth hcalc u one).val 1‖,
      fun x hx g => ?_⟩
    rw [Real.rpow_zero, mul_one, Subsingleton.elim g 1, map_smul]
    calc _ = ‖c x‖ * ‖evaluate F G (adelicEnvelopingAction F G hsmooth hcalc u one).val 1‖ :=
          norm_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (hBc x hx) (norm_nonneg _)

end RankZero

/-- The meromorphic continuation of Eisenstein series implies their uniform moderate growth on
compact sets of unitary parameters. -/
def EisensteinUnitaryUniformGrowthReductionStatement : Prop :=
  EisensteinMeromorphicContinuationStatement.{0} → EisensteinUnitaryUniformGrowthStatement

theorem eisensteinUnitaryUniformGrowthReduction :
    EisensteinUnitaryUniformGrowthReductionStatement := by
  intro hMero F _ _ G P M U A _ _ _ _ _ _ p _ iU l a r _ _ _ hA hT hG hUR K hK N d rho hsmooth
    hcalc φ hKmax hrho hφ E D hD hE hreg n e C hC
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact exists_uniformGrowthFamily_of_rank_zero rho hrho hsmooth hcalc hD hE e hC
  · exact exists_uniformGrowthFamily_of_pos r hA hT hK hMero hG hUR rho hN hrho hsmooth hcalc
      hKmax hφ.1 hD hE hreg e hC

end Langlands.Global
