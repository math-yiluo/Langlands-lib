import Langlands.Representation.Induction.SurjectivityProof
import Langlands.Representation.Induction.CompactQuotientDuality
import Langlands.Representation.Induction.FiniteProductTensorBijectiveProof
import Langlands.Representation.Induction.FixedVectorModel
import Langlands.Representation.Smooth.Contragredient.FixedLevelPairing

/-!
# Duality of induction from a compact quotient for every smooth representation

`exists_integralDualEquiv_of_pos` (module `CompactQuotientDuality`) identifies the
smooth dual of the induction of `σ` with the induction of the smooth dual of `σ`
when the former induction is admissible. Here admissibility is replaced by a
continuous section `s : M →* P` of `m`, closedness of `P` and compactness of
`P \ G`. At each compact open level `L`, the `L`-fixed vectors of an induced
representation are a finite sum of double-coset sections, the integral pairing
of a section with an `L`-fixed function is a nonzero multiple of the coefficient
pairing at its representative, and every functional on the fixed coefficient
space of the compact group `P ∩ x L x⁻¹` comes from a smooth functional of `σ`.

* `character_mul_self_eq_one_of_isCompact`: `χ²` is trivial on compact subgroups.
* `isCompact_conjOpenSubgroup`: `P ∩ x L x⁻¹` is compact for closed `P`.
* `fixedSectionMap`, `dual_apply_eq_sum_fixedDoubleCosetSection`: a functional on
  the `L`-fixed induced vectors is a sum over the double cosets `P \ G / L`.
* `exists_fixed_smoothDual_of_section`: functionals on fixed coefficient spaces.
* `pairing_section_mul`, `pairing_section_of_ne`: the pointwise pairing with a
  double-coset section.
* `exists_integral_section_eq`: the scalar formula for the pairing with a section.
* `integralBilinearPairing_fixed_surjective`: surjectivity at each compact open level.
* `exists_integralDualEquiv_of_section`: the duality equivalence.
-/

noncomputable section

open MeasureTheory Topology
open scoped NNReal

namespace Langlands.Induction

open FiniteProductTensorBijective

universe uG uM uV

section Character

variable {Q : Type*} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]

/-- A character with open kernel whose square takes nonnegative real values has
trivial square on every compact subgroup. -/
theorem character_mul_self_eq_one_of_isCompact (χ : Q →* ℂˣ) (hχ : IsOpen (χ.ker : Set Q))
    (δ : Q → ℝ≥0) (hδ : ∀ q : Q, (χ q : ℂ) * χ q = ((δ q : ℝ) : ℂ))
    (H : Subgroup Q) (hH : IsCompact (H : Set Q)) {h : Q} (hh : h ∈ H) :
    (χ h : ℂ) * χ h = 1 := by
  have : CompactSpace H := isCompact_iff_compactSpace.mp hH
  let N : Subgroup H := (χ.comp H.subtype).ker
  have hN : IsOpen (N : Set H) := hχ.preimage continuous_subtype_val
  have : Finite (H ⧸ N) := Subgroup.quotient_finite_of_isOpen N hN
  have hn : N.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hpow : χ h ^ N.index = 1 := by
    have hmem := N.pow_index_mem ⟨h, hh⟩
    rw [MonoidHom.mem_ker, map_pow] at hmem
    exact hmem
  have hc : (χ h : ℂ) ^ N.index = 1 := by
    rw [← Units.val_pow_eq_pow_val, hpow, Units.val_one]
  have h1 : ((δ h : ℝ) : ℂ) ^ N.index = 1 := by
    rw [← hδ, mul_pow, hc, one_mul]
  have h2 : (δ h : ℝ) ^ N.index = 1 := by exact_mod_cast h1
  have h3 : (δ h : ℝ) = 1 := (pow_eq_one_iff_of_nonneg (δ h).2 hn).mp h2
  rw [hδ, h3, Complex.ofReal_one]

end Character

section Sections

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {W : Type*} [AddCommGroup W] [Module ℂ W]
variable (P : Subgroup G) (τ : Representation ℂ P W) (L : OpenSubgroup G)
  (hL : IsCompact (L : Set G))

/-- The double-coset section at `x`, as a linear map into the `L`-fixed vectors of
the smooth induction. -/
def fixedSectionMap (x : G) :
    fixedVectors τ (conjOpenSubgroup P L x).toSubgroup →ₗ[ℂ]
      fixedVectors (smoothInduced P τ) L.toSubgroup :=
  (sectionMap P τ L hL x).codRestrict _ fun v => (fixedDoubleCosetSection P τ L hL x v).2

theorem fixedSectionMap_apply (x : G) (v : fixedVectors τ (conjOpenSubgroup P L x).toSubgroup) :
    fixedSectionMap P τ L hL x v = fixedDoubleCosetSection P τ L hL x v :=
  rfl

theorem fixedDoubleCosetSection_val (x : G) (v : W)
    (hv : v ∈ fixedVectors τ (conjOpenSubgroup P L x).toSubgroup) :
    (fixedDoubleCosetSection P τ L hL x ⟨v, hv⟩ : SmoothFunctions P τ) =
      (compactDoubleCosetSection P τ L hL x v hv).val :=
  rfl

theorem pointEvaluation_val (x : G) (f : fixedVectors (smoothInduced P τ) L.toSubgroup) :
    (pointEvaluation P τ L x f : W) = eval P τ f.1 x :=
  rfl

/-- A linear functional on the `L`-fixed induced vectors is the sum of its values
on the double-coset sections through the values of a vector at representatives of
the finitely many double cosets. -/
theorem dual_apply_eq_sum_fixedDoubleCosetSection
    [Fintype (DoubleCoset.Quotient (P : Set G) (L.toSubgroup : Set G))]
    (φ : Module.Dual ℂ (fixedVectors (smoothInduced P τ) L.toSubgroup))
    (f : fixedVectors (smoothInduced P τ) L.toSubgroup) :
    φ f = ∑ q : DoubleCoset.Quotient (P : Set G) (L.toSubgroup : Set G),
      φ (fixedDoubleCosetSection P τ L hL q.out (pointEvaluation P τ L q.out f)) := by
  have h := LinearMap.congr_fun (subtype_eq_sum P τ L hL) f
  rw [LinearMap.sum_apply, Submodule.subtype_apply] at h
  have hf : f = ∑ q : DoubleCoset.Quotient (P : Set G) (L.toSubgroup : Set G),
      fixedDoubleCosetSection P τ L hL q.out (pointEvaluation P τ L q.out f) := by
    apply Subtype.ext
    rw [h, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [LinearMap.comp_apply]
    rfl
  rw [← map_sum]
  exact congrArg φ hf

end Sections

section Smooth

variable {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  [WeaklyLocallyCompactSpace G]
variable {M : Type uM} [Group M] [TopologicalSpace M] [IsTopologicalGroup M]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (P : Subgroup G) (m : P →* M) (χ : P →* ℂˣ) (δ : P → ℝ≥0)

omit [WeaklyLocallyCompactSpace G] in
/-- Given a continuous section `s` of `m`, every linear functional on the vectors
of `twist χ (σ.comp m)` fixed by a compact open subgroup `H` of `P` is the
pairing with a smooth functional of `σ` fixed by `H` in `twist χ (σ̃.comp m)`. -/
theorem exists_fixed_smoothDual_of_section (hm : Continuous m)
    (hχ : IsOpen (χ.ker : Set P)) (hδ : ∀ q : P, (χ q : ℂ) * χ q = ((δ q : ℝ) : ℂ))
    (s : M →* P) (hs : Continuous s) (hms : ∀ n : M, m (s n) = n)
    (σ : Representation ℂ M V) (hσ : IsSmooth σ) (H : OpenSubgroup P)
    (hH : IsCompact (H : Set P))
    (φ : Module.Dual ℂ (fixedVectors (twist χ (σ.comp m)) H.toSubgroup)) :
    ∃ lam ∈ fixedVectors (twist χ ((smoothContragredient σ).comp m)) H.toSubgroup,
      ∀ v : fixedVectors (twist χ (σ.comp m)) H.toSubgroup,
        smoothDualPairing σ lam v = φ v := by
  have hτ : IsSmooth (twist χ (σ.comp m)) := by
    intro v
    obtain ⟨U, hU⟩ := hσ v
    exact exists_twist_comp_fixed P m hm χ hχ σ v U hU
  obtain ⟨ℓ, hℓ⟩ := (smoothDualFixedRestriction_bijective _ hτ H hH).2 φ
  obtain ⟨U, hU⟩ := ℓ.1.2
  let Hχ : OpenSubgroup P := ⟨χ.ker, hχ⟩
  let U' : OpenSubgroup M := (U ⊓ Hχ).comap s hs
  have hsm : ℓ.1.1 ∈ smoothVectors σ.dual := by
    refine ⟨U', ?_⟩
    rintro ⟨u, hu⟩
    obtain ⟨hu₁, hu₂⟩ := OpenSubgroup.mem_inf.mp (OpenSubgroup.mem_comap.mp hu)
    have hχu : χ (s u) = 1 := hu₂
    have hfix := hU ⟨s u, hu₁⟩
    change (twist χ (σ.comp m)).dual (s u) ℓ.1.1 = ℓ.1.1 at hfix
    change σ.dual u ℓ.1.1 = ℓ.1.1
    refine LinearMap.ext fun v => ?_
    have hv := LinearMap.congr_fun hfix v
    change ℓ.1.1 (((χ (s u)⁻¹ : ℂˣ) : ℂ) • σ (m (s u)⁻¹) v) = ℓ.1.1 v at hv
    change ℓ.1.1 (σ u⁻¹ v) = ℓ.1.1 v
    rwa [map_inv χ, map_inv m, hχu, hms, inv_one, Units.val_one, one_smul] at hv
  let lam : SmoothDual σ := ⟨ℓ.1.1, hsm⟩
  refine ⟨lam, ?_, fun v => LinearMap.congr_fun hℓ v⟩
  rintro ⟨h, hh⟩
  have h2 := character_mul_self_eq_one_of_isCompact χ hχ δ hδ H.toSubgroup hH hh
  have hinv : ((χ h⁻¹ : ℂˣ) : ℂ) = χ h := by
    rw [map_inv, Units.val_inv_eq_inv_val]
    exact inv_eq_of_mul_eq_one_right h2
  have hfix := ℓ.2 ⟨h, hh⟩
  change (χ h : ℂ) • smoothContragredient σ (m h) lam = lam
  apply Subtype.ext
  refine LinearMap.ext fun v => ?_
  have hv := congrArg (fun F : SmoothDual (twist χ (σ.comp m)) => F.1 v) hfix
  change ℓ.1.1 (((χ h⁻¹ : ℂˣ) : ℂ) • σ (m h⁻¹) v) = ℓ.1.1 v at hv
  change (χ h : ℂ) * ℓ.1.1 (σ (m h)⁻¹ v) = ℓ.1.1 v
  rwa [map_smul, smul_eq_mul, hinv, map_inv m] at hv

omit [WeaklyLocallyCompactSpace G] in
/-- The coefficient pairing of a double-coset section for `twist χ (σ̃.comp m)`
with an `L`-fixed function, at a point `a * (x * b)` of its double coset. -/
theorem pairing_section_mul (σ : Representation ℂ M V) (L : OpenSubgroup G)
    (hL : IsCompact (L : Set G)) (x : G) (lam : SmoothDual σ)
    (hlam : lam ∈ fixedVectors (twist χ ((smoothContragredient σ).comp m))
      (conjOpenSubgroup P L x).toSubgroup)
    {f : SmoothFunctions P (twist χ (σ.comp m))}
    (hf : f ∈ fixedVectors (smoothInduced P (twist χ (σ.comp m))) L.toSubgroup)
    (a : P) (b : L) :
    smoothDualPairing σ
        (eval P _ (compactDoubleCosetSection P _ L hL x lam hlam).val ((a : G) * (x * b)))
        (eval P _ f ((a : G) * (x * b))) =
      ((χ a : ℂ) * χ a) * smoothDualPairing σ lam (eval P _ f x) := by
  rw [dualPairing_covariant, compactDoubleCosetSection_apply_mul,
    eval_mul_of_mem_fixedVectors P _ L.toSubgroup hf b x]

omit [WeaklyLocallyCompactSpace G] in
/-- The coefficient pairing of a double-coset section with any induced function
vanishes off its double coset. -/
theorem pairing_section_of_ne (σ : Representation ℂ M V) (L : OpenSubgroup G)
    (hL : IsCompact (L : Set G)) (x : G) (lam : SmoothDual σ)
    (hlam : lam ∈ fixedVectors (twist χ ((smoothContragredient σ).comp m))
      (conjOpenSubgroup P L x).toSubgroup)
    (f : SmoothFunctions P (twist χ (σ.comp m))) {y : G}
    (hy : doubleClass P L y ≠ doubleClass P L x) :
    smoothDualPairing σ (eval P _ (compactDoubleCosetSection P _ L hL x lam hlam).val y)
      (eval P _ f y) = 0 := by
  rw [section_eval_of_ne P _ L hL x lam hlam hy, map_zero, LinearMap.zero_apply]

variable (K : Subgroup G) [MeasurableSpace K] (μ : Measure K)

omit [WeaklyLocallyCompactSpace G] in
/-- The integral pairing of the double-coset section through `lam` at `x` with an
`L`-fixed induced function `f` is `c * ⟨lam, f x⟩`, for a constant `c ≠ 0`
depending only on `x` and `L`. -/
theorem exists_integral_section_eq (hm : Continuous m)
    (hχ : IsOpen (χ.ker : Set P)) (hδ : ∀ q : P, (χ q : ℂ) * χ q = ((δ q : ℝ) : ℂ))
    (hpos : ∀ U : Set K, IsOpen U → (1 : K) ∈ U → 0 < μ U)
    (hscalar : ∀ φ : G → ℂ, IsLocallyConstant φ →
      (∀ (q : P) (x : G), φ ((q : G) * x) = ((δ q : ℝ) : ℂ) * φ x) →
      ∀ g : G, Integrable (fun k : K => φ ((k : G) * g)) μ ∧
        (∫ k : K, φ ((k : G) * g) ∂μ) = ∫ k : K, φ (k : G) ∂μ)
    (hP : IsClosed (P : Set G)) (s : M →* P) (hs : Continuous s)
    (hms : ∀ n : M, m (s n) = n) (σ : Representation ℂ M V) (hσ : IsSmooth σ)
    (L : OpenSubgroup G) (hL : IsCompact (L : Set G)) (x : G) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ (lam : SmoothDual σ)
      (hlam : lam ∈ fixedVectors (twist χ ((smoothContragredient σ).comp m))
        (conjOpenSubgroup P L x).toSubgroup)
      (f : SmoothFunctions P (twist χ (σ.comp m))),
      f ∈ fixedVectors (smoothInduced P (twist χ (σ.comp m))) L.toSubgroup →
      (∫ k : K, smoothDualPairing σ
          (eval P _ (compactDoubleCosetSection P _ L hL x lam hlam).val k)
          (eval P _ f k) ∂μ) =
        c * smoothDualPairing σ lam (eval P _ f x) := by
  classical
  have hH := isCompact_conjOpenSubgroup P hP L hL x
  have hsplit : ∀ y : G, doubleClass P L x = doubleClass P L y →
      ∃ (a : P) (b : L), y = (a : G) * (x * b) := by
    intro y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.eq.mp hy
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, mul_assoc a x b⟩
  by_cases hz : ∃ v₁ : fixedVectors (twist χ (σ.comp m)) (conjOpenSubgroup P L x).toSubgroup,
      v₁ ≠ 0
  · obtain ⟨v₁, hv₁⟩ := hz
    obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ
        (fixedVectors (twist χ (σ.comp m)) (conjOpenSubgroup P L x).toSubgroup), φ v₁ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hv₁ ((Module.forall_dual_apply_eq_zero_iff ℂ v₁).mp hcon)
    obtain ⟨lam₁, hlam₁, hlam₁φ⟩ :=
      exists_fixed_smoothDual_of_section P m χ δ hm hχ hδ s hs hms σ hσ _ hH φ
    have hc₀ : smoothDualPairing σ lam₁ v₁ ≠ 0 := by
      rw [hlam₁φ]
      exact hφ
    let f₁ := fixedDoubleCosetSection P (twist χ (σ.comp m)) L hL x v₁
    have hf₁x : eval P _ f₁.1 x = v₁ := fixedDoubleCosetSection_eval_self P _ L hL x v₁
    let h₁ := (compactDoubleCosetSection P _ L hL x lam₁ hlam₁).val
    let ψ₁ : G → ℂ := fun y => smoothDualPairing σ (eval P _ h₁ y) (eval P _ f₁.1 y)
    have hpt : ∀ (lam : SmoothDual σ)
        (hlam : lam ∈ fixedVectors (twist χ ((smoothContragredient σ).comp m))
          (conjOpenSubgroup P L x).toSubgroup)
        (f : SmoothFunctions P (twist χ (σ.comp m))),
        f ∈ fixedVectors (smoothInduced P (twist χ (σ.comp m))) L.toSubgroup → ∀ y : G,
        smoothDualPairing σ lam₁ v₁ * smoothDualPairing σ
            (eval P _ (compactDoubleCosetSection P _ L hL x lam hlam).val y) (eval P _ f y) =
          smoothDualPairing σ lam (eval P _ f x) * ψ₁ y := by
      intro lam hlam f hf y
      by_cases hy : doubleClass P L x = doubleClass P L y
      · obtain ⟨a, b, rfl⟩ := hsplit y hy
        simp only [ψ₁, h₁]
        rw [pairing_section_mul P m χ σ L hL x lam hlam hf a b,
          pairing_section_mul P m χ σ L hL x lam₁ hlam₁ f₁.2 a b, hf₁x]
        ring
      · have hy' : doubleClass P L y ≠ doubleClass P L x := Ne.symm hy
        simp only [ψ₁, h₁]
        rw [pairing_section_of_ne P m χ σ L hL x lam hlam f hy',
          pairing_section_of_ne P m χ σ L hL x lam₁ hlam₁ f₁.1 hy', mul_zero, mul_zero]
    have hcov₁ : ∀ (q : P) (y : G), ψ₁ ((q : G) * y) = ((δ q : ℝ) : ℂ) * ψ₁ y := by
      intro q y
      simp only [ψ₁]
      rw [dualPairing_covariant, hδ]
    have hloc₁ : IsLocallyConstant ψ₁ :=
      bilinearPairing_isLocallyConstant P _ _ (smoothDualPairing σ) h₁ f₁.1
    obtain ⟨hint₁, heq₁⟩ := hscalar ψ₁ hloc₁ hcov₁ x
    have hne := integral_ne_zero_of_doubleCoset_of_pos P δ K μ hpos ψ₁ hcov₁ x hint₁ L
      (smoothDualPairing σ lam₁ v₁) hc₀ ?_ ?_
    · rw [heq₁] at hne
      refine ⟨(∫ k : K, ψ₁ k ∂μ) / smoothDualPairing σ lam₁ v₁, div_ne_zero hne hc₀,
        fun lam hlam f hf => ?_⟩
      have hI : smoothDualPairing σ lam₁ v₁ * (∫ k : K, smoothDualPairing σ
            (eval P _ (compactDoubleCosetSection P _ L hL x lam hlam).val k)
            (eval P _ f k) ∂μ) =
          smoothDualPairing σ lam (eval P _ f x) * ∫ k : K, ψ₁ k ∂μ := by
        rw [← integral_const_mul, ← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun k => hpt lam hlam f hf k)
      field_simp
      linear_combination hI
    · intro l
      simp only [ψ₁, h₁]
      rw [compactDoubleCosetSection_apply_mul,
        eval_mul_of_mem_fixedVectors P _ L.toSubgroup f₁.2 l x, hf₁x]
    · intro y hy
      apply compactDoubleCosetSection_mem_of_ne_zero P _ L hL x lam₁ hlam₁ y
      intro h0
      apply hy
      simp only [ψ₁, h₁]
      rw [h0, map_zero, LinearMap.zero_apply]
  · push Not at hz
    refine ⟨1, one_ne_zero, fun lam hlam f hf => ?_⟩
    have hfx : eval P _ f x = 0 :=
      congrArg Subtype.val (hz ⟨_, eval_mem_fixedVectors P _ L x hf⟩)
    have h0 : ∀ y : G, smoothDualPairing σ
        (eval P _ (compactDoubleCosetSection P _ L hL x lam hlam).val y) (eval P _ f y) = 0 := by
      intro y
      by_cases hy : doubleClass P L x = doubleClass P L y
      · obtain ⟨a, b, rfl⟩ := hsplit y hy
        rw [pairing_section_mul P m χ σ L hL x lam hlam hf a b, hfx, map_zero, mul_zero]
      · exact pairing_section_of_ne P m χ σ L hL x lam hlam f (Ne.symm hy)
    rw [hfx, map_zero, mul_zero]
    simp only [h0, integral_zero]

omit [WeaklyLocallyCompactSpace G] in
/-- At each compact open level `L`, every linear functional on the `L`-fixed
vectors of the induction of `σ` is the integral pairing with an `L`-fixed vector
of the induction of the smooth dual of `σ`. -/
theorem integralBilinearPairing_fixed_surjective (hm : Continuous m)
    (hχ : IsOpen (χ.ker : Set P)) (hδ : ∀ q : P, (χ q : ℂ) * χ q = ((δ q : ℝ) : ℂ))
    (hpos : ∀ U : Set K, IsOpen U → (1 : K) ∈ U → 0 < μ U)
    (hscalar : ∀ φ : G → ℂ, IsLocallyConstant φ →
      (∀ (q : P) (x : G), φ ((q : G) * x) = ((δ q : ℝ) : ℂ) * φ x) →
      ∀ g : G, Integrable (fun k : K => φ ((k : G) * g)) μ ∧
        (∫ k : K, φ ((k : G) * g) ∂μ) = ∫ k : K, φ (k : G) ∂μ)
    [CompactSpace (LeftQuotient P)] (hP : IsClosed (P : Set G)) (s : M →* P)
    (hs : Continuous s) (hms : ∀ n : M, m (s n) = n)
    (σ : Representation ℂ M V) (hσ : IsSmooth σ)
    (hint : ∀ (h : SmoothFunctions P (twist χ ((smoothContragredient σ).comp m)))
      (f : SmoothFunctions P (twist χ (σ.comp m))),
      Integrable (fun k : K => smoothDualPairing σ (eval P _ h k) (eval P _ f k)) μ)
    (L : OpenSubgroup G) (hL : IsCompact (L : Set G))
    (φ : Module.Dual ℂ
      (fixedVectors (smoothInduced P (twist χ (σ.comp m))) L.toSubgroup)) :
    ∃ h ∈ fixedVectors (smoothInduced P (twist χ ((smoothContragredient σ).comp m)))
        L.toSubgroup,
      ∀ f : fixedVectors (smoothInduced P (twist χ (σ.comp m))) L.toSubgroup,
        integralBilinearPairing P _ _ (smoothDualPairing σ) K μ hint h f = φ f := by
  have := finite_doubleCosetQuotient P L
  let _ := Fintype.ofFinite (DoubleCoset.Quotient (P : Set G) (L.toSubgroup : Set G))
  choose c hc hcf using fun q : DoubleCoset.Quotient (P : Set G) (L.toSubgroup : Set G) =>
    exists_integral_section_eq P m χ δ K μ hm hχ hδ hpos hscalar hP s hs hms σ hσ L hL q.out
  choose lam hlam hlamφ using fun q : DoubleCoset.Quotient (P : Set G) (L.toSubgroup : Set G) =>
    exists_fixed_smoothDual_of_section P m χ δ hm hχ hδ s hs hms σ hσ
      (conjOpenSubgroup P L q.out) (isCompact_conjOpenSubgroup P hP L hL q.out)
      ((c q)⁻¹ • (φ ∘ₗ fixedSectionMap P (twist χ (σ.comp m)) L hL q.out))
  refine ⟨_, (∑ q : DoubleCoset.Quotient (P : Set G) (L.toSubgroup : Set G),
    fixedDoubleCosetSection P (twist χ ((smoothContragredient σ).comp m)) L hL q.out
      ⟨lam q, hlam q⟩).2, fun f => ?_⟩
  rw [dual_apply_eq_sum_fixedDoubleCosetSection P _ L hL φ f, Submodule.coe_sum, map_sum,
    LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  have h2 := hlamφ q (pointEvaluation P _ L q.out f)
  rw [LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul, fixedSectionMap_apply,
    pointEvaluation_val] at h2
  rw [integralBilinearPairing_apply, fixedDoubleCosetSection_val,
    hcf q (lam q) (hlam q) f.1 f.2, h2, ← mul_assoc, mul_inv_cancel₀ (hc q), one_mul]

/-- An invariant integral pairing, for a measure on `K` positive on open
neighbourhoods of `1`, identifies the smooth dual of the induction of any smooth
`σ` with the induction of the smooth dual of `σ`, for a closed subgroup `P` with
compact quotient `P \ G` and a continuous section of `m`. The equivalence is
characterized by the integral formula. No admissibility is assumed. -/
theorem exists_integralDualEquiv_of_section (hm : Continuous m)
    (hχ : IsOpen (χ.ker : Set P)) (hδ : ∀ q : P, (χ q : ℂ) * χ q = ((δ q : ℝ) : ℂ))
    (hpos : ∀ U : Set K, IsOpen U → (1 : K) ∈ U → 0 < μ U)
    (hscalar : ∀ φ : G → ℂ, IsLocallyConstant φ →
      (∀ (q : P) (x : G), φ ((q : G) * x) = ((δ q : ℝ) : ℂ) * φ x) →
      ∀ g : G, Integrable (fun k : K => φ ((k : G) * g)) μ ∧
        (∫ k : K, φ ((k : G) * g) ∂μ) = ∫ k : K, φ (k : G) ∂μ)
    [CompactSpace (LeftQuotient P)] (hP : IsClosed (P : Set G)) (s : M →* P)
    (hs : Continuous s) (hms : ∀ n : M, m (s n) = n)
    (σ : Representation ℂ M V) (hσ : IsSmooth σ) :
    ∃ E : Representation.Equiv (smoothContragredient (smoothInduced P (twist χ (σ.comp m))))
        (smoothInduced P (twist χ ((smoothContragredient σ).comp m))),
      ∀ (ℓ : SmoothDual (smoothInduced P (twist χ (σ.comp m))))
        (f : SmoothFunctions P (twist χ (σ.comp m))),
        smoothDualPairing _ ℓ f =
          ∫ k : K, smoothDualPairing σ (eval P _ (E ℓ) k) (eval P _ f k) ∂μ := by
  have hcofG : ∀ U : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ U := by
    intro U
    obtain ⟨L, hL, hLU⟩ := compactOpenSubgroupBasis G U U.mem_nhds_one
    exact ⟨L, hL, fun x hx => hLU hx⟩
  have hpair : ∀ (h : SmoothFunctions P (twist χ ((smoothContragredient σ).comp m)))
      (f : SmoothFunctions P (twist χ (σ.comp m))) (g : G),
      Integrable (fun k : K =>
        smoothDualPairing σ (eval P _ h ((k : G) * g)) (eval P _ f ((k : G) * g))) μ ∧
      (∫ k : K, smoothDualPairing σ (eval P _ h ((k : G) * g))
        (eval P _ f ((k : G) * g)) ∂μ) =
        ∫ k : K, smoothDualPairing σ (eval P _ h k) (eval P _ f k) ∂μ := by
    intro h f
    refine hscalar (fun y => smoothDualPairing σ (eval P _ h y) (eval P _ f y))
      (bilinearPairing_isLocallyConstant P _ _ (smoothDualPairing σ) h f) ?_
    intro q x
    rw [dualPairing_covariant, hδ]
  have hint : ∀ (h : SmoothFunctions P (twist χ ((smoothContragredient σ).comp m)))
      (f : SmoothFunctions P (twist χ (σ.comp m))),
      Integrable (fun k : K => smoothDualPairing σ (eval P _ h k) (eval P _ f k)) μ := by
    intro h f
    simpa only [mul_one] using (hpair h f 1).1
  let b := integralBilinearPairing P _ _ (smoothDualPairing σ) K μ hint
  have hb : ∀ (g : G) (h : SmoothFunctions P (twist χ ((smoothContragredient σ).comp m)))
      (f : SmoothFunctions P (twist χ (σ.comp m))),
      b (smoothInduced P _ g h) (smoothInduced P _ g f) = b h f := by
    intro g h f
    exact (hpair h f g).2
  have hleft : ∀ h : SmoothFunctions P (twist χ ((smoothContragredient σ).comp m)),
      (∀ f : SmoothFunctions P (twist χ (σ.comp m)), b h f = 0) → h = 0 := by
    intro h hh
    by_contra hne
    obtain ⟨f, hf⟩ := integral_dualPairing_left_nondegenerate_of_pos P m χ δ K μ hm hχ hδ
      hpos hscalar σ hσ h hne
    exact hf (hh f)
  obtain ⟨E', hE'⟩ := exists_smoothDualEquiv_of_fixedSurjective hcofG _ _
    (smoothInduced_smooth P _) (smoothInduced_smooth P _) b hb hleft
    (fun L hL φ => integralBilinearPairing_fixed_surjective P m χ δ K μ hm hχ hδ hpos hscalar
      hP s hs hms σ hσ hint L hL φ)
  refine ⟨E'.symm, fun ℓ f => ?_⟩
  conv_lhs => rw [← E'.apply_symm_apply ℓ]
  exact hE' _ f

end Smooth

end Langlands.Induction
