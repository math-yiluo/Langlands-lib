import Langlands.Global.ImaginaryAxisLocalDivision
import Langlands.Global.AdelicEisensteinImaginaryHolomorphyStatement
import Langlands.Global.AdelicBoundedWavePacketStatement
import Langlands.Global.AdelicEisensteinJointRootHyperplaneStatement
import Langlands.Global.AdelicIwasawaCompatibleMeasureStatement
import Langlands.GroupScheme.Rational.LeviRetraction
import Langlands.Analysis.SeveralComplex.MeromorphicDomainExtension
import Langlands.Analysis.SeveralComplex.RealHyperplaneDivision
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # Lapid's Proposition 6 from its premises

Conditional proof of `Langlands.Global.EisensteinImaginaryAxisHolomorphyStatement` from the
joint root-hyperplane statement, Lapid's Lemma 10 (bound (19)) and the existence of an
Iwasawa-compatible Haar measure on `M(𝔸)`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct Set Topology Filter
open scoped CategoryTheory.MonObj TensorProduct ENNReal ComplexConjugate

set_option autoImplicit false

namespace Langlands.Global.ImaginaryAxis

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

section InnerProduct

variable {F : Type} [Field F] [NumberField F]
  {G P M : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]

omit [LocallyOfFiniteType G.X.hom] in
/-- The induced inner product is sesquilinear in the scalar: `(a φ, a φ)_P = a ā (φ, φ)_P`. -/
theorem inducedInnerProduct_const_mul (K : Subgroup (AdelicGroupPoints F G))
    (hKc : IsCompact (K : Set (AdelicGroupPoints F G))) (p : P ⟶ G) (l : M ⟶ P)
    (μM : Measure (AdelicGroupPoints F M)) {n : ℕ}
    (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P) (β : (Fin n → ℝ) → ℝ)
    (φ : AdelicGroupPoints F G → ℂ) (a : ℂ) :
    inducedInnerProduct K hKc p l μM e β (fun g => a * φ g) (fun g => a * φ g) =
      (a * conj a) * inducedInnerProduct K hKc p l μM e β φ φ := by
  simp only [inducedInnerProduct]
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun k => ?_)
  simp only
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [map_mul]
  ring

end InnerProduct

section Density

/-- The complement of the zero set of a product of powers of nonzero linear forms is dense. -/
theorem dense_setOf_prod_ne_zero {n : ℕ} {Idx : Type*} (S : Finset Idx)
    (ℓ : Idx → (Fin n → ℂ) →ₗ[ℂ] ℂ) (m : ℕ) (s₀ : Fin n → ℂ) (hℓ : ∀ β ∈ S, ℓ β ≠ 0) :
    Dense {s : Fin n → ℂ | (∏ β ∈ S, (ℓ β (s - s₀)) ^ m) ≠ 0} := by
  have hcont : ∀ β, Continuous (ℓ β) := fun β => (ℓ β).continuous_of_finiteDimensional
  have hone : ∀ β ∈ S, Dense {s : Fin n → ℂ | ℓ β (s - s₀) ≠ 0} := by
    intro β hβ
    have hker : Dense ((LinearMap.ker (ℓ β) : Set (Fin n → ℂ))ᶜ) := by
      rw [← interior_eq_empty_iff_dense_compl]
      by_contra hne
      have htop := (LinearMap.ker (ℓ β)).eq_top_of_nonempty_interior'
        (Set.nonempty_iff_ne_empty.mpr hne)
      exact hℓ β hβ (LinearMap.ker_eq_top.mp htop)
    have : {s : Fin n → ℂ | ℓ β (s - s₀) ≠ 0} =
        (Homeomorph.subRight s₀) ⁻¹' ((LinearMap.ker (ℓ β) : Set (Fin n → ℂ))ᶜ) := by
      ext s; simp
    rw [this]
    exact hker.preimage (Homeomorph.subRight s₀).isOpenMap
  have hinter : Dense (⋂ β ∈ (S : Set Idx), {s : Fin n → ℂ | ℓ β (s - s₀) ≠ 0}) :=
    dense_biInter_of_isOpen
      (fun β _ => isOpen_ne_fun ((hcont β).comp (continuous_id.sub continuous_const))
        continuous_const)
      S.countable_toSet hone
  refine hinter.mono fun s hs => ?_
  simp only [mem_iInter, Finset.mem_coe] at hs
  exact Finset.prod_ne_zero_iff.mpr fun β hβ => pow_ne_zero m (hs β hβ)

end Density

section Main

attribute [local instance] quotient_opensMeasurableSpace

/-- **Lapid's Proposition 6 from its premises.** -/
theorem eisensteinImaginaryAxisHolomorphy_of_premises
    (hN1 : EisensteinJointRootHyperplaneStatement.{0})
    (hL10 : BoundedWavePacketNormBoundStatement)
    (hIw : IwasawaCompatibleMeasureExistenceStatement) :
    EisensteinImaginaryAxisHolomorphyStatement := by
  intro F _ _ G P M U A _ _ _ _ _ _ p _ iU l a r _ _ _ hA hT hG hU K hK N d rho hsmooth
    hcalc φ hKmax hrho hφ E D hE hreg
  classical
  have hfdC : FiniteDimensional ℂ (ComplexCharacterParameter F P) := (hE 1).1
  have hfdR : FiniteDimensional ℝ (RealCharacterParameter F P) :=
    finiteDimensional_real (X := GroupScheme.rationalCharacters P)
  set n := Module.finrank ℝ (RealCharacterParameter F P) with hn
  set eR : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P :=
    realCoordinates (X := GroupScheme.rationalCharacters P) with heR
  set e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P :=
    complexCoordinates (X := GroupScheme.rationalCharacters P) with he
  have he_slice : ∀ x : Fin n → ℝ, e (imaginarySlice x) = imaginaryParameter F P (eR x) :=
    fun x => complexCoordinates_imaginarySlice x
  have hloc : ∀ x₀ : Fin n → ℝ, ∃ W' : Set (Fin n → ℂ), IsOpen W' ∧ imaginarySlice x₀ ∈ W' ∧
      ∀ g, ∃ u : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ u W' ∧
        ∀ s ∈ W', e s ∈ D → u s = E (e s) g := by
    intro x₀
    set s₀ : Fin n → ℂ := imaginarySlice x₀ with hs₀
    obtain ⟨S, m, W, h, hSU, hSne, hWo, hs₀W, hhcont, hhol, hinv, hhE⟩ :=
      hN1 F G P M U A p iU l a r hA hT hG hU K hK rho hsmooth hcalc φ hKmax hrho hφ.1 E D hE
        hreg n e s₀
    -- the root forms in the coordinates `e` and their product `Q`
    set ℓ : characterLattice A → (Fin n → ℂ) →ₗ[ℂ] ℂ :=
      fun β => (r.rootFunctional hA hT β).comp e.toLinearMap with hℓ
    set Q : (Fin n → ℂ) → ℂ := fun s => ∏ β ∈ S, (ℓ β (s - s₀)) ^ m with hQ
    have hQE : ∀ s, (∏ β ∈ S, r.rootFunctional hA hT β (e s - e s₀)) ^ m = Q s := by
      intro s
      simp only [Q, ℓ, LinearMap.comp_apply, LinearEquiv.coe_coe, map_sub, Finset.prod_pow]
    have hℓd : ∀ β, Differentiable ℂ (ℓ β) := fun β => by
      simpa using (LinearMap.toContinuousLinearMap (ℓ β)).differentiable
    have hQdiff : Differentiable ℂ Q := by
      have key : ∀ T : Finset (characterLattice A),
          Differentiable ℂ (fun s => ∏ β ∈ T, (ℓ β (s - s₀)) ^ m) := by
        intro T
        induction T using Finset.induction_on with
        | empty => simp
        | insert β T hβ ih =>
          simp only [Finset.prod_insert hβ]
          exact (((hℓd β).comp (differentiable_id.sub_const s₀)).pow m).mul ih
      exact key S
    have hQcont : Continuous Q := hQdiff.continuous
    by_cases htriv : S = ∅ ∨ m = 0
    · -- no root hyperplane: `h` itself extends `E`
      have hQ1 : ∀ s, Q s = 1 := by
        intro s
        rcases htriv with h0 | h0
        · simp [Q, h0]
        · simp [Q, h0]
      refine ⟨W, hWo, hs₀W, fun g => ⟨fun s => h s g, hhol g, fun s hs hD => ?_⟩⟩
      show h s g = E (e s) g
      rw [hhE g s hs hD, hQE, hQ1, one_mul]
    · push Not at htriv
      obtain ⟨hSne', hm⟩ := htriv
      obtain ⟨β₀, hβ₀⟩ := hSne'
      have hβ₀U : β₀ ∈ r.unipotentRoots := hSU hβ₀
      obtain ⟨R, hR⟩ := hreg
      -- a neighbourhood `W₁` of `s₀` disjoint from the regular region
      set φ₀ : (Fin n → ℂ) →ₗ[ℝ] ℝ := (r.realRootFunctional hA hT β₀).comp
        ((parameterRealPart F P).comp (e.toLinearMap.restrictScalars ℝ)) with hφ₀
      have hφ₀c : Continuous φ₀ := φ₀.continuous_of_finiteDimensional
      have hφ₀s₀ : φ₀ s₀ = 0 := by
        have h1 : e s₀ = imaginaryParameter F P (eR x₀) := he_slice x₀
        simp only [φ₀, LinearMap.comp_apply, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
          h1]
        exact realRootFunctional_parameterRealPart_imaginaryParameter r hA hT β₀ _
      set W₁ : Set (Fin n → ℂ) := W ∩ {s | φ₀ s < 1} with hW₁
      have hW₁o : IsOpen W₁ := hWo.inter (isOpen_lt hφ₀c continuous_const)
      have hs₀W₁ : s₀ ∈ W₁ := ⟨hs₀W, by simp [hφ₀s₀]⟩
      set R' := max R 1 with hR'
      have hnotreg : ∀ s ∈ W₁, ¬ r.IsRegularParameter hA hT R' (e s) := by
        intro s hs
        refine not_isRegularParameter_of_le r hA hT hβ₀U ?_
        have h1 : φ₀ s < 1 := hs.2
        exact (le_of_lt h1).trans (le_max_right _ _)
      -- the continuation `E₁`, holomorphic on `W₁` off the root hyperplanes
      set W₂ : Set (Fin n → ℂ) := W₁ ∩ {s | Q s ≠ 0} with hW₂
      have hW₂o : IsOpen W₂ := hW₁o.inter (isOpen_ne_fun hQcont continuous_const)
      obtain ⟨E₁, D₁, hΛ₁, -, hmer₁, hE₁D, hE₁O⟩ :=
        exists_isMeromorphicInCoordinatesOn_extension E D hE (e '' W₁) (e '' W₂) (by
          rintro _ ⟨s₁, hs₁, rfl⟩
          refine ⟨n, e, W₂, hW₂o, by simpa using hs₁, image_mono inter_subset_left,
            fun g => ⟨fun s => h s g / Q s, ?_, ?_⟩⟩
          · simp_rw [div_eq_mul_inv]
            exact ((hhol g).mono fun s (hs : s ∈ W₂) => hs.1.1).mul
              (hQdiff.differentiableOn.inv fun s (hs : s ∈ W₂) => hs.2)
          · intro s hs hD
            show h s g / Q s = E (e s) g
            rw [hhE g s hs.1.1 hD, hQE, mul_div_cancel_left₀ _ hs.2])
      have hreg₁ : ∀ lam, r.IsRegularParameter hA hT R' lam →
          E₁ lam = hK.eisensteinSeries φ lam := by
        intro lam hlam
        have hnot : lam ∉ e '' W₁ := by
          rintro ⟨s, hs, rfl⟩
          exact hnotreg s hs hlam
        rw [hE₁O lam hnot]
        exact hR lam fun α hα => lt_of_le_of_lt (le_max_left R 1) (hlam α hα)
      have hE₁W₂ : ∀ g, ∀ s ∈ W₂, E₁ (e s) g = h s g / Q s := by
        intro g
        have hmer := (hmer₁ g).2 n e
        have hd1 : DifferentiableOn ℂ (fun s => E₁ (e s) g) (e ⁻¹' D₁) :=
          (isHolomorphicOn_iff_differentiableOn _ _).1 hmer.2.2.1
        have hDe := (hE g).2 n e
        have hW₂D₁ : W₂ ⊆ e ⁻¹' D₁ := fun s hs => hΛ₁ ⟨s, hs, rfl⟩
        have hc1 : ContinuousOn (fun s => E₁ (e s) g) W₂ := (hd1.mono hW₂D₁).continuousOn
        have hc2 : ContinuousOn (fun s => h s g / Q s) W₂ :=
          ContinuousOn.div ((hhol g).mono fun s (hs : s ∈ W₂) => hs.1.1).continuousOn
            hQcont.continuousOn fun s (hs : s ∈ W₂) => hs.2
        have heq : EqOn (fun s => E₁ (e s) g) (fun s => h s g / Q s) (W₂ ∩ e ⁻¹' D) := by
          intro s hs
          show E₁ (e s) g = h s g / Q s
          rw [hE₁D _ hs.2, hhE g s hs.1.1.1 hs.2, hQE, mul_div_cancel_left₀ _ hs.1.2]
        exact heq.of_subset_closure hc1 hc2 inter_subset_left
          (hDe.2.1.open_subset_closure_inter hW₂o)
      -- Lemma 10 data: Levi retraction, instances for `U`, compatible measure, weight
      obtain ⟨-, -, π, -, -, hπ, -⟩ := r.isCompatible.levi.exists_unipotentRadical_retraction
      have hUci : IsClosedImmersion iU.hom.hom.left := hU.1.isClosedSubgroup
      have : IsAffine U.X.left := isAffine_of_isAffineHom iU.hom.hom.left
      have : IsClosedImmersion (iU ≫ p).hom.hom.left :=
        IsClosedSubgroup.comp (i := iU) (j := p) hU.1.isClosedSubgroup
          ‹IsClosedImmersion p.hom.hom.left›
      have : LocallyOfFiniteType P.X.hom :=
        IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
      obtain ⟨μM, hμMHaar, hμM⟩ := hIw F G P M U A p iU l a r hG hU K hK hKmax
      let bump : ContDiffBump (0 : Fin n → ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
      set β : (Fin n → ℝ) → ℝ := bump.normed volume with hβ
      set C : ℝ := (Nat.card (weylParameterSet p l p l π) : ℝ) *
        (inducedInnerProduct K hK.isCompact p l μM eR β φ φ).re with hC
      set k : (Fin n → ℝ) → AdelicGroupPoints F G → ℂ :=
        fun x g => E₁ (imaginaryParameter F P (eR x)) g with hkdef
      have hk : ∀ x, imaginarySlice x ∈ W₁ → Q (imaginarySlice x) ≠ 0 → ∀ g,
          k x g = h (imaginarySlice x) g / Q (imaginarySlice x) := by
        intro x hx hQx g
        show E₁ (imaginaryParameter F P (eR x)) g = _
        rw [← he_slice x]
        exact hE₁W₂ g _ ⟨hx, hQx⟩
      have hwave : ∀ (c' : (Fin n → ℝ) → ℂ) (A' : Set (Fin n → ℝ)), IsCompact A' →
          A' ⊆ {x | imaginarySlice x ∈ W₁ ∧ Q (imaginarySlice x) ≠ 0} →
          Measurable c' → (∃ B : ℝ, ∀ x, ‖c' x‖ ≤ B) → (∀ x ∉ A', c' x = 0) →
          MemLp (fun y : LeftCosetSpace (rationalSubgroup F G) =>
              ∫ x, c' x * k x y.out ∂((ENNReal.ofReal (2 * Real.pi))⁻¹ ^ n • volume)) 2
              (LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F G)
                (isDiscrete_rationalSubgroup F G) Measure.haar) ∧
            ∫ y, ‖∫ x, c' x * k x y.out ∂((ENNReal.ofReal (2 * Real.pi))⁻¹ ^ n • volume)‖ ^ 2
                ∂(LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F G)
                  (isDiscrete_rationalSubgroup F G) Measure.haar) ≤
              C * ∫ x, ‖c' x‖ ^ 2 ∂((ENNReal.ofReal (2 * Real.pi))⁻¹ ^ n • volume) := by
        intro c' A' hA' hA'T hc'm hc'B hc'0
        have himg : (fun x => imaginaryParameter F P (eR x)) '' A' ⊆ D₁ := by
          rintro _ ⟨x, hx, rfl⟩
          show imaginaryParameter F P (eR x) ∈ D₁
          rw [← he_slice x]
          exact hΛ₁ ⟨_, hA'T hx, rfl⟩
        have L := hL10 F G P M U A p iU l a r hA hT π hG hU hπ K hK rho hsmooth hcalc hKmax hrho
          μM hμM eR β bump.continuous_normed bump.hasCompactSupport_normed bump.integral_normed
          1 (fun _ => φ) (fun _ => c') A' (fun _ => E₁) D₁ (fun _ => hφ) hA'
          (fun _ => ⟨hc'm, hc'B, hc'0⟩) himg (fun _ g => hmer₁ g) (fun _ => ⟨R', hreg₁⟩)
        obtain ⟨-, hmem, hle⟩ := L
        simp only [Fin.sum_univ_one] at hmem hle
        refine ⟨hmem, hle.trans (le_of_eq ?_)⟩
        simp only [inducedInnerProduct_const_mul, Complex.mul_conj', ← Complex.ofReal_pow,
          Complex.re_ofReal_mul]
        rw [integral_mul_const]
        simp only [C, spectralMeasure]
        ring
      -- a ball of the real slice inside `W₁`
      obtain ⟨ρ, hρpos, hρ⟩ : ∃ ρ > 0, ∀ x ∈ Metric.ball (0 : Fin n → ℝ) ρ,
          (fun j => s₀ j + Complex.I * (x j : ℂ)) ∈ W₁ := by
        have hc : Continuous fun x : Fin n → ℝ => (fun j => s₀ j + Complex.I * (x j : ℂ)) :=
          continuous_pi fun j => continuous_const.add
            (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply j)))
        have h0 : (fun j => s₀ j + Complex.I * (((0 : Fin n → ℝ) j : ℝ) : ℂ)) = s₀ := by
          ext j; simp
        have hmem : (fun x : Fin n → ℝ => (fun j => s₀ j + Complex.I * (x j : ℂ))) ⁻¹' W₁ ∈
            𝓝 (0 : Fin n → ℝ) := by
          refine hc.continuousAt.preimage_mem_nhds ?_
          rw [h0]
          exact hW₁o.mem_nhds hs₀W₁
        obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hmem
        exact ⟨ρ, hρ, fun x hx => hball hx⟩
      -- the root forms are real on real points and nonzero
      have he_ofReal : ∀ x : Fin n → ℝ, e (fun j => (x j : ℂ)) = complexify (eR x) :=
        fun x => complexCoordinates_ofReal x
      have hℓreal : ∀ β ∈ S, ∀ x : Fin n → ℝ, (ℓ β (fun j => (x j : ℂ))).im = 0 := by
        intro β _ x
        simp only [ℓ, LinearMap.comp_apply, LinearEquiv.coe_coe]
        rw [he_ofReal, rootFunctional_complexify]
        exact Complex.ofReal_im _
      have hℓne : ∀ β ∈ S, ℓ β ≠ 0 := by
        intro β hβ h0
        apply hSne β hβ
        refine LinearMap.ext fun y => ?_
        have h1 := LinearMap.congr_fun h0 (fun j => ((eR.symm y) j : ℂ))
        simp only [ℓ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.zero_apply] at h1
        rw [he_ofReal, rootFunctional_complexify, LinearEquiv.apply_symm_apply] at h1
        exact_mod_cast h1
      -- local division at `s₀`
      have hc0 : ((ENNReal.ofReal (2 * Real.pi))⁻¹ ^ n) ≠ 0 :=
        pow_ne_zero n (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)
      have hctop : ((ENNReal.ofReal (2 * Real.pi))⁻¹ ^ n) ≠ ⊤ :=
        ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (by positivity)).ne')
      obtain ⟨W', hW'o, hs₀W', hW'W₁, hW'⟩ := exists_local_division (rationalSubgroup F G)
        (isDiscrete_rationalSubgroup F G) Measure.haar ((ENNReal.ofReal (2 * Real.pi))⁻¹ ^ n)
        hc0 hctop x₀ W₁ hW₁o h (hhcont.mono (prod_mono inter_subset_left subset_rfl))
        (fun g => (hhol g).mono inter_subset_left) (fun s hs => hinv s hs.1) Q hQcont k hk C
        hwave ρ hρ (by
          obtain ⟨W', a1, a2, a3, a4⟩ :=
            Langlands.Analysis.SeveralComplex.exists_open_forall_tendsto_eq_rootProduct_mul S ℓ
              hℓne hℓreal m s₀ hW₁o hρpos hρ
          exact ⟨W', a1, a2, a3, fun L _ Hk Hlim h1 h2 h3 h4 => a4 L Hk Hlim h1 h2 h3 h4⟩)
      refine ⟨W', hW'o, hs₀W', fun g => ?_⟩
      obtain ⟨H', hH'd, hH'eq⟩ := hW' g
      refine ⟨H', hH'd, ?_⟩
      have hDe := (hE g).2 n e
      set t := W' ∩ e ⁻¹' D with ht
      have hto : IsOpen t := hW'o.inter hDe.1
      have hc1 : ContinuousOn H' t := hH'd.continuousOn.mono inter_subset_left
      have hc2 : ContinuousOn (fun s => E (e s) g) t :=
        ((isHolomorphicOn_iff_differentiableOn _ _).1 hDe.2.2.1).continuousOn.mono
          inter_subset_right
      have hQd : Dense {s | Q s ≠ 0} := dense_setOf_prod_ne_zero S ℓ m s₀ hℓne
      have heq : EqOn H' (fun s => E (e s) g) (t ∩ {s | Q s ≠ 0}) := by
        rintro s ⟨⟨hsW', hsD⟩, hQs⟩
        have h1 := hH'eq s hsW'
        have h2 := hhE g s (hW'W₁ hsW').1 hsD
        rw [hQE] at h2
        exact mul_left_cancel₀ hQs (h1.symm.trans h2)
      have hall := heq.of_subset_closure hc1 hc2 inter_subset_left
        (hQd.open_subset_closure_inter hto)
      exact fun s hs hD => hall ⟨hs, hD⟩
  obtain ⟨E', D', hΛ, -, hmer, hEq, -⟩ := exists_isMeromorphicInCoordinatesOn_extension E D hE
    univ (Set.range (imaginaryParameter F P)) (by
      rintro _ ⟨y, rfl⟩
      obtain ⟨W', hW'o, hx₀, hW'⟩ := hloc (eR.symm y)
      refine ⟨n, e, W', hW'o, ?_, subset_univ _, hW'⟩
      have h1 : e (imaginarySlice (eR.symm y)) = imaginaryParameter F P y := by
        rw [he_slice, LinearEquiv.apply_symm_apply]
      rw [← h1, LinearEquiv.symm_apply_apply]
      exact hx₀)
  exact ⟨E', D', hΛ, hmer, fun lam hlam => hEq lam hlam.1⟩

end Main

end Langlands.Global.ImaginaryAxis

namespace Langlands.Global

/-- Lapid's Proposition 6 (`EisensteinImaginaryAxisHolomorphyStatement`) follows from the joint
root-hyperplane form of Eisenstein series (`EisensteinJointRootHyperplaneStatement`), Lapid's
Lemma 10 bound (`BoundedWavePacketNormBoundStatement`) and the existence of an
Iwasawa-compatible Haar measure on `M(𝔸)` (`IwasawaCompatibleMeasureExistenceStatement`). -/
def EisensteinImaginaryAxisHolomorphyReductionStatement : Prop :=
  EisensteinJointRootHyperplaneStatement.{0} → BoundedWavePacketNormBoundStatement →
    IwasawaCompatibleMeasureExistenceStatement → EisensteinImaginaryAxisHolomorphyStatement

theorem eisensteinImaginaryAxisHolomorphyReduction :
    EisensteinImaginaryAxisHolomorphyReductionStatement :=
  fun hN1 hL10 hIw => ImaginaryAxis.eisensteinImaginaryAxisHolomorphy_of_premises hN1 hL10 hIw

end Langlands.Global
