import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalDiscreteCoefficientRadicalIntegrability
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalLowerInclusionStatement
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitCentralFiberAdapter
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalDiscreteSeriesOrbitFiniteness
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSpecialCompactConstantTermPremises
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSchwartzCentralConvergenceProof
import Langlands.Representation.Plancherel.RationalCentralQuotient

/-! # The direct cusp lift of discrete-series coefficients -/

noncomputable section

universe u uG uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj TensorProduct Pointwise

namespace Langlands.HarishChandraSchwartz.DiscreteCoefficientCuspLift

open DiscreteCoefficientCutoff

/-! ### A transversal cutoff -/

section Transversal

variable {Γ : Type uG} [Group Γ] (N A : Subgroup Γ)

/-- The indicator, on `Γ ⧸ N`, of the classes of the chosen representatives `Quotient.out m`
of the cosets `m` of `N ⊔ A`. -/
def transversalCutoff : Γ ⧸ N → ℂ :=
  Set.indicator (Set.range fun m : Γ ⧸ (N ⊔ A) => (QuotientGroup.mk (Quotient.out m) : Γ ⧸ N))
    fun _ => 1

/-- If `Γ ⧸ (N ⊔ A)` is finite, the cutoff has finite support. -/
theorem support_transversalCutoff_finite [Finite (Γ ⧸ (N ⊔ A))] :
    (Function.support (transversalCutoff N A)).Finite :=
  (Set.finite_range _).subset Set.support_indicator_subset

/-- On a topological group with `N` open, the quotient `Γ ⧸ N` is discrete, so the cutoff has
compact support when `Γ ⧸ (N ⊔ A)` is finite. -/
theorem hasCompactSupport_transversalCutoff [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (hN : IsOpen (N : Set Γ)) [Finite (Γ ⧸ (N ⊔ A))] :
    HasCompactSupport (transversalCutoff N A) := by
  have : DiscreteTopology (Γ ⧸ N) := QuotientGroup.discreteTopology hN
  unfold HasCompactSupport tsupport
  rw [closure_discrete]
  exact (support_transversalCutoff_finite N A).isCompact

/-- Along the central subgroup `A`, the cutoff is the indicator of one coset of `A ∩ N`:
for every `g` there is `a₀ ∈ A` such that `x ↦ c(a g)` is the indicator of
`{a ∈ A | a₀⁻¹ a ∈ N}`. -/
theorem exists_transversalCutoff_mul_eq_indicator [N.Normal] (hA : A ≤ Subgroup.center Γ)
    (g : Γ) : ∃ a₀ : A, ∀ a : A,
      transversalCutoff N A (QuotientGroup.mk ((a : Γ) * g)) =
        Set.indicator ((fun b : A => a₀⁻¹ * b) ⁻¹' (N.comap A.subtype : Set A))
          (fun _ => (1 : ℂ)) a := by
  obtain ⟨⟨h, hh⟩, hw⟩ := QuotientGroup.mk_out_eq_mul (N ⊔ A) g
  have hh' : h ∈ ((N : Set Γ) * (A : Set Γ)) := by
    rw [← Subgroup.normal_mul]; exact hh
  obtain ⟨n, hn, b, hb, rfl⟩ := hh'
  refine ⟨⟨b, hb⟩, fun a => ?_⟩
  have hcent : ∀ (z : A) (x : Γ), x * (z : Γ) = (z : Γ) * x := fun z x =>
    Subgroup.mem_center_iff.mp (hA z.2) x
  have key : (g * (n * b))⁻¹ * ((a : Γ) * g) = n⁻¹ * (b⁻¹ * (a : Γ)) := by
    have h1 : (a : Γ) * g = g * (a : Γ) := (hcent a g).symm
    have h2 : b⁻¹ * n⁻¹ = n⁻¹ * b⁻¹ :=
      (Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ (hA hb)) n⁻¹).symm
    calc (g * (n * b))⁻¹ * ((a : Γ) * g) = b⁻¹ * n⁻¹ * (g⁻¹ * ((a : Γ) * g)) := by group
      _ = b⁻¹ * n⁻¹ * (a : Γ) := by rw [h1]; group
      _ = n⁻¹ * (b⁻¹ * (a : Γ)) := by rw [h2]; group
  have hiff : (QuotientGroup.mk ((a : Γ) * g) : Γ ⧸ N) ∈
      Set.range (fun m : Γ ⧸ (N ⊔ A) => (QuotientGroup.mk (Quotient.out m) : Γ ⧸ N)) ↔
      a ∈ (fun b' : A => (⟨b, hb⟩ : A)⁻¹ * b') ⁻¹' (N.comap A.subtype : Set A) := by
    simp only [Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_comap, Subgroup.coe_subtype,
      Subgroup.coe_mul, Subgroup.coe_inv]
    constructor
    · rintro ⟨m, hm⟩
      have hm' := QuotientGroup.eq.mp hm
      have hmg : m = (QuotientGroup.mk g : Γ ⧸ (N ⊔ A)) := by
        rw [← QuotientGroup.out_eq' m]
        rw [QuotientGroup.eq]
        have : (Quotient.out m)⁻¹ * g =
            ((Quotient.out m)⁻¹ * ((a : Γ) * g)) * (a : Γ)⁻¹ := by
          rw [← hcent a g]; group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hm')
          (Subgroup.mem_sup_right (Subgroup.inv_mem _ a.2))
      rw [hmg, hw, key] at hm'
      have := Subgroup.mul_mem _ hn hm'
      simpa using this
    · intro hS
      refine ⟨QuotientGroup.mk g, ?_⟩
      rw [QuotientGroup.eq, hw, key]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hn) hS
  unfold transversalCutoff
  classical
  rw [Set.indicator_apply, Set.indicator_apply]
  exact if_congr hiff rfl rfl

/-- **The central mass.** For a left-invariant measure on the central subgroup `A`, the
integral of `a ↦ c(a g)` is the measure of `A ∩ N`, for every `g`. -/
theorem integral_transversalCutoff [N.Normal] (hA : A ≤ Subgroup.center Γ)
    [TopologicalSpace Γ] [IsTopologicalGroup Γ] (hN : IsOpen (N : Set Γ))
    [MeasurableSpace A] [OpensMeasurableSpace A] [MeasurableMul A] (muA : Measure A)
    [muA.IsMulLeftInvariant] (g : Γ) :
    ∫ a, transversalCutoff N A (QuotientGroup.mk ((a : Γ) * g)) ∂muA =
      (muA.real (N.comap A.subtype : Set A) : ℂ) := by
  obtain ⟨a₀, h⟩ := exists_transversalCutoff_mul_eq_indicator N A hA g
  have hK : IsOpen (N.comap A.subtype : Set A) := hN.preimage continuous_subtype_val
  have hS : MeasurableSet ((fun b : A => a₀⁻¹ * b) ⁻¹' (N.comap A.subtype : Set A)) :=
    (hK.preimage (continuous_const_mul _)).measurableSet
  simp_rw [h]
  rw [integral_indicator_const _ hS, Complex.real_smul, mul_one]
  simp [Measure.real, measure_preimage_mul]

/-- **Central projection of the cut-off coefficient.** If `f(a g) = χ(a) f(g)` for `a ∈ A`, then
`p_χ(f c) = μ_A(A ∩ N) f`. -/
theorem centralProjection_mul_transversalCutoff [N.Normal] (hA : A ≤ Subgroup.center Γ)
    [TopologicalSpace Γ] [IsTopologicalGroup Γ] (hN : IsOpen (N : Set Γ))
    [MeasurableSpace A] [OpensMeasurableSpace A] [MeasurableMul A] (muA : Measure A)
    [muA.IsMulLeftInvariant] (χ : A →* ℂˣ) {f : Γ → ℂ} (hf : ∀ (a : A) (g : Γ), f ((a : Γ) * g) = (χ a : ℂ) * f g) :
    centralProjection muA χ (fun g => f g * transversalCutoff N A g) =
      fun g => (muA.real (N.comap A.subtype : Set A) : ℂ) * f g := by
  funext g
  unfold centralProjection
  have hpt : ∀ a : A, (((χ a)⁻¹ : ℂˣ) : ℂ) * (f ((a : Γ) * g) *
      transversalCutoff N A (QuotientGroup.mk ((a : Γ) * g))) =
      f g * transversalCutoff N A (QuotientGroup.mk ((a : Γ) * g)) := by
    intro a
    rw [hf, ← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul]
  simp_rw [hpt]
  rw [integral_const_mul, integral_transversalCutoff N A hA hN muA g, mul_comm]

/-- The cut-off and rescaled coefficient is a preimage: if `f(a g) = χ(a) f(g)` for `a ∈ A` and
`m = μ_A(A ∩ N) ≠ 0`, then `p_χ(m⁻¹ f c) = f`. -/
theorem centralProjection_smul_mul_transversalCutoff [N.Normal] (hA : A ≤ Subgroup.center Γ)
    [TopologicalSpace Γ] [IsTopologicalGroup Γ] (hN : IsOpen (N : Set Γ))
    [MeasurableSpace A] [OpensMeasurableSpace A] [MeasurableMul A] (muA : Measure A)
    [muA.IsMulLeftInvariant] (χ : A →* ℂˣ) {f : Γ → ℂ}
    (hf : ∀ (a : A) (g : Γ), f ((a : Γ) * g) = (χ a : ℂ) * f g)
    (hm : muA.real (N.comap A.subtype : Set A) ≠ 0) :
    centralProjection muA χ (((muA.real (N.comap A.subtype : Set A) : ℂ)⁻¹) •
      fun g => f g * transversalCutoff N A g) = f := by
  funext g
  have h := congrFun (centralProjection_mul_transversalCutoff N A hA hN muA χ hf) g
  have hm' : (muA.real (N.comap A.subtype : Set A) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hm
  unfold centralProjection at h ⊢
  calc ∫ a, (((χ a)⁻¹ : ℂˣ) : ℂ) * (((muA.real (N.comap A.subtype : Set A) : ℂ)⁻¹) •
          fun g => f g * transversalCutoff N A g) ((a : Γ) * g) ∂muA
      = ∫ a, ((muA.real (N.comap A.subtype : Set A) : ℂ))⁻¹ * ((((χ a)⁻¹ : ℂˣ) : ℂ) *
          (f ((a : Γ) * g) * transversalCutoff N A (QuotientGroup.mk ((a : Γ) * g)))) ∂muA := by
        congr 1
        funext a
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
    _ = ((muA.real (N.comap A.subtype : Set A) : ℂ))⁻¹ * ∫ a, (((χ a)⁻¹ : ℂˣ) : ℂ) *
          (f ((a : Γ) * g) * transversalCutoff N A (QuotientGroup.mk ((a : Γ) * g))) ∂muA :=
        integral_const_mul _ _
    _ = f g := by
        rw [h]
        field_simp

/-- Multiplying by a function of the coset modulo a normal subgroup `N ⊇ H` preserves
`H`-bi-invariance. -/
theorem isBiInvariant_mul_quotient [N.Normal] {H : Subgroup Γ} (hH : H ≤ N) {f : Γ → ℂ}
    (hf : IsBiInvariant H f) (c : Γ ⧸ N → ℂ) :
    IsBiInvariant H (fun g => f g * c (QuotientGroup.mk g)) := by
  intro h₁ hh₁ h₂ hh₂ g
  have hq : (QuotientGroup.mk (h₁ * g * h₂) : Γ ⧸ N) = QuotientGroup.mk g := by
    rw [QuotientGroup.eq]
    have e : (h₁ * g * h₂)⁻¹ * g = h₂⁻¹ * (g⁻¹ * h₁⁻¹ * g⁻¹⁻¹) := by group
    rw [e]
    exact N.mul_mem (N.inv_mem (hH hh₂)) (‹N.Normal›.conj_mem _ (N.inv_mem (hH hh₁)) g⁻¹)
  simp only [hf h₁ hh₁ h₂ hh₂ g, hq]

/-- Multiplying by a function of the coset modulo a normal subgroup `N ⊇ U` preserves
integrable cuspidality along `U`: the factor is constant on every translate `x U y`. -/
theorem isIntegrableUnipotentCuspidal_mul_quotient [MeasurableSpace Γ] [N.Normal]
    {U : Subgroup Γ} (hU : U ≤ N) (muU : Measure U) {f : Γ → ℂ}
    (hf : IsIntegrableUnipotentCuspidal muU f) (c : Γ ⧸ N → ℂ) :
    IsIntegrableUnipotentCuspidal muU (fun g => f g * c (QuotientGroup.mk g)) := by
  intro x y
  have hpt : ∀ v : U, f (x * v * y) * c (QuotientGroup.mk (x * v * y)) =
      f (x * v * y) * c (QuotientGroup.mk (x * y)) := fun v => by
    rw [quotient_mk_mul_mul_of_mem N (hU v.2) x y]
  simp only [hpt]
  exact ⟨(hf x y).1.mul_const _, by rw [integral_mul_const, (hf x y).2, zero_mul]⟩

end Transversal

/-! ### Coefficients with a central character -/

section Coefficients

variable {Γ : Type uG} [Group Γ] [TopologicalSpace Γ]

/-- If the subgroup `Z` acts on `A` by the character `χ`, every element `f` of the coefficient
space of `A` satisfies `f(a g) = χ(a) f(g)` for `a ∈ Z`. -/
theorem coefficientFunctionSpace_mul_left (Z : Subgroup Γ) (χ : Z →* ℂˣ)
    (A : SmoothRep.{0, uG, uV} ℂ Γ)
    (hA : ∀ (a : Z) (v : A), A.representation (a : Γ) v = (χ a : ℂ) • v)
    {f : Γ → ℂ} (hf : f ∈ coefficientFunctionSpace A) (a : Z) (g : Γ) :
    f ((a : Γ) * g) = (χ a : ℂ) * f g := by
  let E : Submodule ℂ (Γ → ℂ) :=
    { carrier := {f | ∀ (a : Z) (g : Γ), f ((a : Γ) * g) = (χ a : ℂ) * f g}
      add_mem' := fun {f₁ f₂} h₁ h₂ a g => by
        simp only [Set.mem_ofPred_eq, Pi.add_apply] at h₁ h₂ ⊢
        rw [h₁ a g, h₂ a g, mul_add]
      zero_mem' := fun a g => by simp
      smul_mem' := fun c f h a g => by
        simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul] at h ⊢
        rw [h a g]
        ring }
  have hle : coefficientFunctionSpace A ≤ E := by
    refine iSup_le fun ℓ => ?_
    rintro _ ⟨v, rfl⟩ a g
    change ℓ.val (A.representation ((a : Γ) * g) v) = (χ a : ℂ) * ℓ.val (A.representation g v)
    rw [map_mul, Module.End.mul_apply, hA, map_smul, smul_eq_mul]
  exact hle hf a g

end Coefficients
/-! ### Rational points -/

section Rational

open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open Langlands.BruhatTits.SpecialCompact
open Aubert.General Aubert.General.RationalPointFamily

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalDecaySecondCountable
  rationalDecayT2 rationalDecayNonarchimedean

/-- **The central mass is positive and finite.** For a Haar measure `muA` on `A_G(F)`, the
measure of `A_G(F) ∩ G¹` is a positive real number: the subgroup is open (as `G¹` is open)
and compact (`isCompact_splitComponent_inf_commonNormKernel`). -/
theorem centralNormKernelMass_pos (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {s : T.toGrp ⟶ G}
    (hs : IsSplitComponent s) (muA : Measure (rationalPoints.map s).range)
    [muA.IsHaarMeasure] :
    0 < muA.real ((rationalCommonNormKernel G).comap
      (rationalPoints.map s).range.subtype : Set (rationalPoints.map s).range) := by
  have hopen : IsOpen ((rationalCommonNormKernel G).comap
      (rationalPoints.map s).range.subtype : Set (rationalPoints.map s).range) :=
    (isOpen_rationalCommonNormKernel G).preimage continuous_subtype_val
  have hcpt : IsCompact ((rationalCommonNormKernel G).comap
      (rationalPoints.map s).range.subtype : Set (rationalPoints.map s).range) := by
    rw [Subtype.isCompact_iff]
    convert isCompact_splitComponent_inf_commonNormKernel G s hG hs using 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hx, hx'⟩
      exact ⟨⟨x, hx⟩, hx', rfl⟩
  rw [measureReal_def]
  exact ENNReal.toReal_pos (hopen.measure_pos muA ⟨1, one_mem _⟩).ne' hcpt.measure_lt_top.ne

/-- **The direct cusp lift (Waldspurger VIII.4.2, inclusion `⊇`, at a fixed level).** Let `A`
be square integrable modulo `A_G(F)` with `A_G(F)` acting by `χ`. Assume the structural data
`K0` of Corollary III.1.2 and that every Schwartz function of the realization (`K`, `ρ`) is
integrable along every two-sided translate of every proper standard radical. Then every
coefficient `f` of `A` is the central projection `p_χ(φ)` of a cuspidal Schwartz function `φ`
that is bi-invariant under every compact subgroup under which `f` is bi-invariant. Explicitly
`φ = m⁻¹ f c`, with `c` the transversal cutoff on `G(F) ⧸ G¹` and `m = μ_A(A_G(F) ∩ G¹)`. -/
theorem exists_cuspidal_lift (hG : IsConnectedReductive G)
    {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice S}
    (hν : IsGenericCocharacter i ν) {K0 : Subgroup (rationalPoints G)}
    (hK0c : IsCompact (K0 : Set (rationalPoints G)))
    (hbasis : SimultaneousStandardBasisAt i ν K0) (hcover : FiniteCartanCovering F i ν K0)
    {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
    {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {s : T.toGrp ⟶ G}
    (hs : IsSplitComponent s) (muA : Measure (rationalPoints.map s).range)
    [muA.IsHaarMeasure] :
    letI := (rationalPoints.map s).range.normal_of_le_center
      hs.isCentralSplitTorus.isCentral.range_le_center
    letI : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
    ∀ (mu : Measure (rationalPoints G ⧸ (rationalPoints.map s).range)) [mu.IsHaarMeasure]
      (χ : (rationalPoints.map s).range →* ℂˣ) (A : SmoothRep.{0, u, uV} ℂ (rationalPoints G)),
      IsSquareIntegrableModCentralSubgroup (rationalPoints.map s).range
          hs.isCentralSplitTorus.isCentral.range_le_center A.representation mu →
      (∀ (a : (rationalPoints.map s).range) (v : A),
        A.representation (a : rationalPoints G) v = (χ a : ℂ) • v) →
      (∀ (I : Finset (SimpleRoot i ν)), rootSet i ν I ≠ simpleRelativeRoots i ν →
        ∀ (muU : Measure (standardUnipotentPoints i ν (rootSet i ν I))) [muU.IsHaarMeasure]
          (φ : RationalSchwartzSpace hKc hPK ρ) (x y : rationalPoints G),
          Integrable (fun v : standardUnipotentPoints i ν (rootSet i ν I) =>
            (φ : rationalPoints G → ℂ) (x * v * y)) muU) →
      ∀ f ∈ coefficientFunctionSpace A, ∃ φ : RationalSchwartzSpace hKc hPK ρ,
        φ ∈ rationalCuspidalSubmodule hKc hPK ρ ∧
        centralProjection muA χ (φ : rationalPoints G → ℂ) = f ∧
        ∀ H : Subgroup (rationalPoints G), IsCompact (H : Set (rationalPoints G)) →
          IsBiInvariant H f → IsBiInvariant H (φ : rationalPoints G → ℂ) := by
  let := (rationalPoints.map s).range.normal_of_le_center
    hs.isCentralSplitTorus.isCentral.range_le_center
  let : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
  intro mu _ χ A hsq hχA hconv f hf
  have : BorelSpace (rationalPoints.map s).range := Subtype.borelSpace _
  have : MeasurableMul (rationalPoints.map s).range :=
    ⟨fun c => (continuous_const.mul continuous_id).measurable,
      fun c => (continuous_id.mul continuous_const).measurable⟩
  have hZc := hs.isCentralSplitTorus.isCentral.range_le_center
  have hfZ := coefficientFunctionSpace_mul_left _ χ A hχA hf
  have hf' : f ∈ (LinearMap.range (coefficientTensorMap A)).map (LocallyConstant.coeFnₗ ℂ) :=
    coefficientFunctionSpace_eq_map A ▸ hf
  obtain ⟨f₀, ⟨t, rfl⟩, rfl⟩ := hf'
  have hD := hasRapidlyDecreasingCoefficientsOn_of_squareIntegrable K.isOpen hKc hPK hG hi hν
    hK0c hbasis hcover ρ hs mu A hsq
  have : Finite (rationalPoints G ⧸
      (rationalCommonNormKernel G ⊔ (rationalPoints.map s).range)) :=
    finite_rationalCentralQuotient s hs.isCentralSplitTorus.isCentral
      (finiteIndex_splitValuationImage_of_isSplitComponent hG s hs)
  have hc := hasCompactSupport_transversalCutoff (rationalCommonNormKernel G)
    (rationalPoints.map s).range (isOpen_rationalCommonNormKernel G)
  have hmem := mul_mem_rationalSchwartz K.isOpen hKc hPK ρ hD
    (f := coefficientTensorMap A t) ⟨t, rfl⟩ hc
  have hm := (centralNormKernelMass_pos hG hs muA).ne'
  let φ₀ : RationalSchwartzSpace hKc hPK ρ := (⟨_, hmem⟩ : schwartzSubmodule _ _)
  refine ⟨((muA.real ((rationalCommonNormKernel G).comap
    (rationalPoints.map s).range.subtype : Set (rationalPoints.map s).range) : ℂ)⁻¹) • φ₀,
    ?_, ?_, ?_⟩
  · rw [mem_rationalCuspidalSubmodule]
    intro I hI muU hmuU
    rw [Space.coe_smul]
    refine (integrableUnipotentCuspidalSubmodule muU).smul_mem _ ?_
    have hcf := DiscreteCoefficientCutoff.coefficientFunctionSpace_le_integrableUnipotentCuspidalSubmodule
      hG hi hν hK0c hbasis hcover K.isOpen hKc hPK ρ hs mu A hsq I hI muU (hconv I hI muU) hf
    exact isIntegrableUnipotentCuspidal_mul_quotient (rationalCommonNormKernel G)
      (standardUnipotentPoints_le_rationalCommonNormKernel hG hi hν I) muU hcf _
  · rw [Space.coe_smul]
    exact centralProjection_smul_mul_transversalCutoff _ _ hZc
      (isOpen_rationalCommonNormKernel G) muA χ hfZ hm
  · intro H hH hfH
    rw [Space.coe_smul]
    exact (isBiInvariant_mul_quotient _ (compactSubgroup_le_rationalCommonNormKernel G H hH)
      hfH _).smul _

/-- **Same-level coefficient lifting from the two analytic premises.** Under
`JointSpecialCompactBasisExistenceStatement` (which supplies the structural data of
Corollary III.1.2) and `RationalSchwartzConstantTermConvergenceStatement` (radical convergence
for all Schwartz functions), the published target `RationalCuspidalFixedCoefficientLiftingStatement`
holds: the direct cusp lift of an `H`-bi-invariant coefficient is `H`-bi-invariant. -/
theorem rationalCuspidalFixedCoefficientLifting_of_joint
    (hJoint : JointSpecialCompactBasisExistenceStatement.{u})
    (hconv : RationalSchwartzConstantTermConvergenceStatement.{u}) :
    RationalCuspidalFixedCoefficientLiftingStatement.{u, uV} := by
  intro F _ _ _ _ G _ _ hG S i hi ν hν K hKc hPK N _ ρ hρ T s hs muA _
  let := (rationalPoints.map s).range.normal_of_le_center
    hs.isCentralSplitTorus.isCentral.range_le_center
  let : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
  intro mu _ χ hχ hu H hH ω hω f hf hHf
  obtain ⟨K0, -, hK0c, -, hbasis, hcover, -⟩ :=
    exists_constantTermPremises_of_joint hJoint hG hi hν
  have hsq : IsSquareIntegrableModCentralSubgroup (rationalPoints.map s).range
      hs.isCentralSplitTorus.isCentral.range_le_center ω.val.out.obj.representation mu := by
    have h := ω.property
    rw [← Quotient.out_eq ω.val] at h
    exact h
  have hχA : ∀ (a : (rationalPoints.map s).range) (v : ω.val.out.obj),
      ω.val.out.obj.representation (a : rationalPoints G) v = (χ a : ℂ) • v := by
    have h := hω.1
    rw [← Quotient.out_eq ω.val] at h
    exact h
  obtain ⟨φ, hφ, hφf, hφH⟩ := exists_cuspidal_lift hG hi hν hK0c hbasis hcover hKc hPK ρ hs
    muA mu χ ω.val.out.obj hsq hχA
    (fun I hI muU _ φ x y => hconv F G hG S i hi ν hν K hKc hPK N ρ hρ φ I hI muU x y) f hf
  exact ⟨φ, ⟨hφ, hφH H.toSubgroup hH hHf⟩, hφf⟩

/-- **The inclusion `⊇` of Theorem VIII.4.2 from the two analytic premises.** Under
`JointSpecialCompactBasisExistenceStatement` and `RationalSchwartzConstantTermConvergenceStatement`,
the canonical sum of discrete-series coefficient spaces with central character `χ` lies in the
raw central-integral image of the cuspidal Schwartz space. -/
theorem rationalCuspidalDiscreteCoefficientLowerInclusion_of_joint
    (hJoint : JointSpecialCompactBasisExistenceStatement.{u})
    (hconv : RationalSchwartzConstantTermConvergenceStatement.{u}) :
    RationalCuspidalDiscreteCoefficientLowerInclusionStatement.{u, uV} := by
  intro F _ _ _ _ G _ _ hG S i hi ν hν K hKc hPK N _ ρ hρ T s hs muA _
  let := (rationalPoints.map s).range.normal_of_le_center
    hs.isCentralSplitTorus.isCentral.range_le_center
  let : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
  intro mu _ χ hχ hu
  obtain ⟨K0, -, hK0c, -, hbasis, hcover, -⟩ :=
    exists_constantTermPremises_of_joint hJoint hG hi hν
  have hc : CentralIntegralConvergesOn (rationalCuspidalSubmodule hKc hPK ρ) muA χ :=
    fun φ _ g => rationalSchwartzCentralConvergence F G hG S i hi ν hν K hKc hPK N ρ hρ T s hs
      muA χ hχ hu φ Submodule.mem_top g
  have hspan := coe_schwartzCentralIntegralSpan_eq_image _ _ _ hc
  have hle : discreteSeriesCentralCoefficientSpace.{u, uV} (rationalPoints.map s).range
      hs.isCentralSplitTorus.isCentral.range_le_center mu χ ≤
        schwartzCentralIntegralSpan (rationalCuspidalSubmodule hKc hPK ρ) muA χ := by
    refine (discreteSeriesCentralCoefficientSpace_le_iff _ _ _ _ _).mpr ?_
    intro ω hω f hf
    have hsq : IsSquareIntegrableModCentralSubgroup (rationalPoints.map s).range
        hs.isCentralSplitTorus.isCentral.range_le_center ω.val.out.obj.representation mu := by
      have h := ω.property
      rw [← Quotient.out_eq ω.val] at h
      exact h
    have hχA : ∀ (a : (rationalPoints.map s).range) (v : ω.val.out.obj),
        ω.val.out.obj.representation (a : rationalPoints G) v = (χ a : ℂ) • v := by
      have h := hω
      rw [← Quotient.out_eq ω.val] at h
      exact h
    obtain ⟨φ, hφ, hφf, -⟩ := exists_cuspidal_lift hG hi hν hK0c hbasis hcover hKc hPK ρ hs
      muA mu χ ω.val.out.obj hsq hχA
      (fun I hI muU _ φ x y => hconv F G hG S i hi ν hν K hKc hPK N ρ hρ φ I hI muU x y) f hf
    exact Submodule.subset_span ⟨φ, hφ, hφf⟩
  intro f hf
  exact (Set.ext_iff.mp hspan f).mp (hle hf)

end Rational

end Langlands.HarishChandraSchwartz.DiscreteCoefficientCuspLift
