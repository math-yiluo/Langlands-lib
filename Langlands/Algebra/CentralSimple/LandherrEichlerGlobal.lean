import Langlands.Algebra.CentralSimple.LandherrEichlerStep

/-! # Reduction of Landherr's theorem to relative reduced norm one -/

noncomputable section

namespace Langlands.CentralSimple.Landherr

open Langlands.GroupScheme.Quaternionic Langlands.GroupScheme.SU3Root
open NumberField IsDedekindDomain Filter Topology
open Langlands.Global.AdelicFunctoriality
open scoped TensorProduct NumberField.LiesOver

universe u

variable (F E : Type u) [Field F] [NumberField F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
  (B : Type u) [Ring B] [Algebra E B] [Algebra F B] [IsScalarTower F E B]
  [FiniteDimensional E B] [Algebra.IsCentral E B] [IsSimpleRing B]

omit [NumberField F] [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] in
/-- On original elements the relative reduced norm is the reduced norm over `E`. -/
theorem relNorm_one_tmul (z : B) :
    relNorm F E B F ((1 : F) ⊗ₜ[F] z) = reducedNorm E B E ((1 : E) ⊗ₜ[E] z) ⊗ₜ[F] (1 : F) := by
  unfold relNorm
  rw [UnitaryPoints.tensorEquiv_tmul]
  have h := reducedNorm_naturality E B
    (Algebra.TensorProduct.includeLeft : E →ₐ[E] E ⊗[F] F) ((1 : E) ⊗ₜ[E] z)
  rw [Algebra.TensorProduct.map_tmul] at h
  exact h

variable (τ : FirstKindInvolution F B)
  (hτ : ∀ e : E, τ (algebraMap E B e) = algebraMap E B (conjugation F E e))

include hτ in
/-- Let `τ` act on `E` by quadratic conjugation. If a `τ`-symmetric unit `y` factors as
`x τ(x)` with `x` a unit at every completion of `F`, then for some unit `b` the unit
`b⁻¹ y τ(b⁻¹)` has relative reduced norm one. -/
theorem exists_relNorm_eq_one (y : Bˣ) (hy : τ (y : B) = y)
    (hloc : ∀ v : Global.Place F, ∃ x : (Global.placeCompletion F v ⊗[F] B)ˣ,
      (1 : Global.placeCompletion F v) ⊗ₜ[F] (y : B) =
        (x : Global.placeCompletion F v ⊗[F] B) * τ.baseChange (Global.placeCompletion F v) x) :
    ∃ b : Bˣ, relNorm F E B F ((1 : F) ⊗ₜ[F] ((↑b⁻¹ : B) * y * τ (↑b⁻¹ : B))) = 1 := by
  classical
  have hFE : FiniteDimensional F E :=
    .of_finrank_pos (by rw [Algebra.IsQuadraticExtension.finrank_eq_two F E]; decide)
  let _ : NumberField E := NumberField.of_module_finite F E
  obtain ⟨a₀, ha⟩ := exists_relNorm_eq_qm F E B τ hτ (y : B) hy
  have ha₀ : a₀ ≠ 0 := by
    intro h0
    have h1 : relNorm F E B F ((1 : F) ⊗ₜ[F] (y : B)) * relNorm F E B F ((1 : F) ⊗ₜ[F] (↑y⁻¹ : B)) = 1 := by
      rw [← relNorm_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, Units.mul_inv,
        ← Algebra.TensorProduct.one_def, relNorm_one]
    rw [ha, h0, qm, TensorProduct.tmul_zero, TensorProduct.tmul_zero, add_zero, zero_mul] at h1
    exact zero_ne_one h1
  have hd : skewSq F E ≠ 0 := by
    intro h0
    have := algebraMap_skewSq F E
    rw [h0, map_zero] at this
    exact skewRoot_ne_zero F E (mul_self_eq_zero.mp this.symm)
  have hsol : ∀ (K : Type u) [Field K] [Algebra F K] (z : E ⊗[F] K),
      z * tensorConj F E K z = qm F E K (algebraMap F K a₀) 0 →
        ∃ X Y : K, X ^ 2 - algebraMap F K (skewSq F E) * Y ^ 2 = algebraMap F K a₀ := by
    intro K _ _ z hz
    obtain ⟨P, Q, rfl⟩ := exists_eq_qm F E K z
    rw [qm_mul_tensorConj] at hz
    refine ⟨P, Q, ?_⟩
    rw [← (qm_injective F E K hz).1]
    ring
  have hlocf : ∀ v : HeightOneSpectrum (𝓞 F), ∃ x : (v.adicCompletion F ⊗[F] B)ˣ,
      (1 : v.adicCompletion F) ⊗ₜ[F] (y : B) =
        (x : v.adicCompletion F ⊗[F] B) * τ.baseChange (v.adicCompletion F) x :=
    fun v => hloc (.inr v)
  have hloci : ∀ w : InfinitePlace F, ∃ x : (w.Completion ⊗[F] B)ˣ,
      (1 : w.Completion) ⊗ₜ[F] (y : B) = (x : w.Completion ⊗[F] B) * τ.baseChange w.Completion x :=
    fun w => hloc (.inl w)
  choose xf hxf using hlocf
  choose xi hxi using hloci
  have hδf := fun v => relNorm_mul_conj_of_eq F E B τ hτ _ (y : B) _ (hxf v) a₀ ha
  have hδi := fun w => relNorm_mul_conj_of_eq F E B τ hτ _ (y : B) _ (hxi w) a₀ ha
  obtain ⟨α, β, hαβ⟩ := QuadraticNormLocalGlobal.exists_eq_of_local
    ClassFieldTheory.Global.cyclicHasseNorm hd ha₀ (fun v => hsol _ _ (hδf v))
    (fun w => hsol _ _ (hδi w))
  set t₀ := algebraMap F E α + algebraMap F E β * skewRoot F E with ht₀_def
  have ht₀N : t₀ * conjugation F E t₀ = algebraMap F E a₀ := by
    rw [ht₀_def, conjugation_add_mul_skewRoot, ← hαβ]
    have := algebraMap_skewSq F E
    simp only [map_sub, map_mul, map_pow]
    rw [this]
    ring
  have ht₀ : t₀ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at ht₀N
    exact ha₀ ((algebraMap F E).injective (ht₀N.symm.trans (map_zero _).symm))
  have htK : ∀ (K : Type u) [CommRing K] [Algebra F K],
      (t₀ ⊗ₜ[F] (1 : K)) * tensorConj F E K (t₀ ⊗ₜ[F] (1 : K)) =
        qm F E K (algebraMap F K a₀) 0 := by
    intro K _ _
    rw [tmul_one_mul_tensorConj, ht₀N, ← one_tmul_eq_qm, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
  have hHf : ∀ v : HeightOneSpectrum (𝓞 F), ∃ P Q : v.adicCompletion F,
      IsUnit (qm F E _ P Q) ∧ relNorm F E B _ (xf v) * tensorConj F E _ (qm F E _ P Q) =
        (t₀ ⊗ₜ[F] (1 : v.adicCompletion F)) * qm F E _ P Q :=
    fun v => exists_hilbert90_point F E _ _ t₀ ht₀ ((hδf v).trans (htK _).symm)
  have hHi : ∀ w : InfinitePlace F, ∃ P Q : w.Completion,
      IsUnit (qm F E _ P Q) ∧ relNorm F E B _ (xi w) * tensorConj F E _ (qm F E _ P Q) =
        (t₀ ⊗ₜ[F] (1 : w.Completion)) * qm F E _ P Q :=
    fun w => exists_hilbert90_point F E _ _ t₀ ht₀ ((hδi w).trans (htK _).symm)
  choose Pf Qf hPQfu hPQf using hHf
  choose Pi Qi hPQiu hPQi using hHi
  have hfinU : ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)),
      w.asIdeal.LiesOver v.asIdeal → ∃ U ∈ 𝓝 (Pf v, Qf v), ∀ p q : F,
        (algebraMap F (v.adicCompletion F) p, algebraMap F (v.adicCompletion F) q) ∈ U →
        algebraMap F E p + algebraMap F E q * skewRoot F E ≠ 0 ∧
        ∃ z : (w.adicCompletion E ⊗[E] B)ˣ, reducedNorm E B _ (z : w.adicCompletion E ⊗[E] B) =
          algebraMap E (w.adicCompletion E) (t₀ * (algebraMap F E p + algebraMap F E q * skewRoot F E) /
            conjugation F E (algebraMap F E p + algebraMap F E q * skewRoot F E)) := by
    intro v w h
    have := h
    let _ : NontriviallyNormedField (w.adicCompletion E) :=
      Valued.toNontriviallyNormedField (w.adicCompletion E) (WithZero (Multiplicative ℤ))
    have : CharZero (w.adicCompletion E) :=
      charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
    exact exists_reducedNorm_near_hilbert90 F E B (FiniteExtension.completionMap v w)
      (FiniteExtension.continuous_completionMap v w)
      (fun x => FiniteExtension.completionMap_coe v w x) (xf v) t₀ (Pf v) (Qf v) (hPQfu v)
      (hPQf v)
  have hinfU : ∀ (v : InfinitePlace F) (w : InfinitePlace E), w.LiesOver v →
      ∃ U ∈ 𝓝 (Pi v, Qi v), ∀ p q : F,
        (algebraMap F v.Completion p, algebraMap F v.Completion q) ∈ U →
        algebraMap F E p + algebraMap F E q * skewRoot F E ≠ 0 ∧
        ∃ z : (w.Completion ⊗[E] B)ˣ, reducedNorm E B _ (z : w.Completion ⊗[E] B) =
          algebraMap E w.Completion (t₀ * (algebraMap F E p + algebraMap F E q * skewRoot F E) /
            conjugation F E (algebraMap F E p + algebraMap F E q * skewRoot F E)) := by
    intro v w h
    have := h
    let _ : NontriviallyNormedField w.Completion :=
      { (inferInstance : NormedField w.Completion) with
        non_trivial := by
          refine ⟨2, ?_⟩
          have h2 := (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
            (map_zero (InfinitePlace.Completion.extensionEmbedding w)) (2 : w.Completion)
          rw [← h2]
          norm_num only [map_ofNat, Complex.norm_ofNat] }
    have : CharZero w.Completion :=
      charZero_of_injective_algebraMap (algebraMap E w.Completion).injective
    refine exists_reducedNorm_near_hilbert90 F E B (NumberField.LiesOver.completionMap v w)
      (NumberField.LiesOver.continuous_completionMap v w) (fun x => ?_) (xi v) t₀ (Pi v) (Qi v)
      (hPQiu v) (hPQi v)
    rw [← RingHom.algebraMap_toAlgebra (NumberField.LiesOver.completionMap v w),
      ← IsScalarTower.algebraMap_apply]
    rfl
  choose Uf hUf hUfp using hfinU
  choose Ui hUi hUip using hinfU
  let A : CSA.{u, u} E := { toAlgCat := AlgCat.of E B }
  set NE := (Brauer.finite_nonsplitFinitePlaces A).toFinset with hNE
  set SF := NE.image (ClassFieldTheory.Global.placeBelow F) with hSF
  let Of : ∀ v : HeightOneSpectrum (𝓞 F), Set (v.adicCompletion F × v.adicCompletion F) :=
    fun v => ⋂ w ∈ NE, ⋂ h : w.asIdeal.LiesOver v.asIdeal, Uf v w h
  have hOf : ∀ v, Of v ∈ 𝓝 (Pf v, Qf v) := fun v =>
    (Filter.biInter_finset_mem NE).mpr fun w _ => Filter.iInter_mem.mpr fun h => hUf v w h
  let Oi : ∀ v : InfinitePlace F, Set (v.Completion × v.Completion) :=
    fun v => ⋂ w : InfinitePlace E, ⋂ h : w.LiesOver v, Ui v w h
  have hOi : ∀ v, Oi v ∈ 𝓝 (Pi v, Qi v) := fun v =>
    Filter.iInter_mem.mpr fun w => Filter.iInter_mem.mpr fun h => hUi v w h
  have hboxf := fun v => mem_nhds_prod_iff'.mp (hOf v)
  have hboxi := fun v => mem_nhds_prod_iff'.mp (hOi v)
  choose Af Bf hAfo hAf hBfo hBf hABf using hboxf
  choose Ai Bi hAio hAi hBio hBi hABi using hboxi
  obtain ⟨p, hpf, hpi⟩ := exists_algebraMap_mem_open SF (fun v => Af v.1) (fun v => hAfo v.1)
    (fun v => ⟨_, hAf v.1⟩) (fun w => Ai w) (fun w => hAio w) (fun w => ⟨_, hAi w⟩)
  obtain ⟨q, hqf, hqi⟩ := exists_algebraMap_mem_open SF (fun v => Bf v.1) (fun v => hBfo v.1)
    (fun v => ⟨_, hBf v.1⟩) (fun w => Bi w) (fun w => hBio w) (fun w => ⟨_, hBi w⟩)
  set ω := algebraMap F E p + algebraMap F E q * skewRoot F E with hω
  set t := t₀ * ω / conjugation F E ω with ht
  have hinf_cond : ∀ w : InfinitePlace E, ω ≠ 0 ∧ ∃ z : (w.Completion ⊗[E] B)ˣ,
      reducedNorm E B _ (z : w.Completion ⊗[E] B) = algebraMap E w.Completion t := by
    intro w
    let v := w.comap (algebraMap F E)
    have h : w.LiesOver v := ⟨rfl⟩
    refine hUip v w h p q ?_
    have hmem : (algebraMap F v.Completion p, algebraMap F v.Completion q) ∈ Oi v :=
      hABi v ⟨hpi v, hqi v⟩
    exact Set.mem_iInter.mp (Set.mem_iInter.mp hmem w) h
  have hfin_cond : ∀ w ∈ NE, ∃ z : (w.adicCompletion E ⊗[E] B)ˣ,
      reducedNorm E B _ (z : w.adicCompletion E ⊗[E] B) = algebraMap E (w.adicCompletion E) t := by
    intro w hw
    let v := ClassFieldTheory.Global.placeBelow F w
    have hv : v ∈ SF := Finset.mem_image_of_mem _ hw
    refine (hUfp v w (ClassFieldTheory.Global.liesOver_placeBelow F w) p q ?_).2
    have hmem : (algebraMap F (v.adicCompletion F) p, algebraMap F (v.adicCompletion F) q) ∈
        Of v := hABf v ⟨hpf ⟨v, hv⟩, hqf ⟨v, hv⟩⟩
    exact Set.mem_iInter.mp (Set.mem_iInter₂.mp hmem w hw) _
  have hω0 : ω ≠ 0 := (hinf_cond (Classical.arbitrary _)).1
  have hσω0 : conjugation F E ω ≠ 0 := fun h0 =>
    hω0 ((conjugation F E).injective (h0.trans (map_zero _).symm))
  have ht0 : t ≠ 0 := div_ne_zero (mul_ne_zero ht₀ hω0) hσω0
  have hl : ∀ w : Global.Place E,
      Units.map (algebraMap E (Global.placeCompletion E w)).toMonoidHom (Units.mk0 t ht0) ∈
        Set.range (reducedNormUnits E B (Global.placeCompletion E w)) := by
    intro w
    rcases w with w | w
    · obtain ⟨-, z, hz⟩ := hinf_cond w
      exact ⟨z, Units.ext hz⟩
    · by_cases hw : w ∈ NE
      · obtain ⟨z, hz⟩ := hfin_cond w hw
        exact ⟨z, Units.ext hz⟩
      · have hsplit : Brauer.IsSplit (Brauer.baseChange (w.adicCompletion E) A) := by
          by_contra hns
          apply hw
          rw [hNE, Set.Finite.mem_toFinset]
          exact hns
        exact reducedNormUnits_surjective_of_split A (w.adicCompletion E) hsplit _
  obtain ⟨b', hb'⟩ := numberFieldReducedNormLocality E B (Units.mk0 t ht0) hl
  let b : Bˣ := Units.map (Algebra.TensorProduct.lid E B).toMonoidHom b'
  have hb1 : (1 : E) ⊗ₜ[E] (b : B) = (b' : E ⊗[E] B) :=
    (Algebra.TensorProduct.lid E B).symm_apply_apply (b' : E ⊗[E] B)
  have hbn : reducedNorm E B E ((1 : E) ⊗ₜ[E] (b : B)) = t := by
    rw [hb1]
    exact congrArg Units.val hb'
  have hbinv : reducedNorm E B E ((1 : E) ⊗ₜ[E] (↑b⁻¹ : B)) = t⁻¹ := by
    have h1 : reducedNorm E B E ((1 : E) ⊗ₜ[E] (b : B)) *
        reducedNorm E B E ((1 : E) ⊗ₜ[E] (↑b⁻¹ : B)) = 1 := by
      rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, Units.mul_inv,
        ← Algebra.TensorProduct.one_def, map_one]
    rw [hbn] at h1
    exact (inv_eq_of_mul_eq_one_right h1).symm
  have htN : t * conjugation F E t = algebraMap F E a₀ := by
    rw [ht, map_div₀, map_mul, conjugation_involutive F E ω, ← ht₀N]
    field_simp
  refine ⟨b, ?_⟩
  have hsplit3 : (1 : F) ⊗ₜ[F] ((↑b⁻¹ : B) * (y : B) * τ (↑b⁻¹ : B)) =
      ((1 : F) ⊗ₜ[F] (↑b⁻¹ : B)) * ((1 : F) ⊗ₜ[F] (y : B)) * ((1 : F) ⊗ₜ[F] τ (↑b⁻¹ : B)) := by
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  have hτb : relNorm F E B F ((1 : F) ⊗ₜ[F] τ (↑b⁻¹ : B)) =
      tensorConj F E F (relNorm F E B F ((1 : F) ⊗ₜ[F] (↑b⁻¹ : B))) := by
    rw [← relNorm_baseChange F E B τ hτ F, FirstKindInvolution.baseChange_tmul]
  rw [hsplit3, relNorm_mul, relNorm_mul, hτb, ha, relNorm_one_tmul, hbinv, tensorConj_tmul,
    show qm F E F a₀ 0 = qm F E F (algebraMap F F a₀) 0 from rfl, ← htK F, tensorConj_tmul]
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  rw [Algebra.TensorProduct.one_def]
  congr 1
  rw [map_inv₀]
  have hσt0 : conjugation F E t ≠ 0 := fun h0 =>
    ht0 ((conjugation F E).injective (h0.trans (map_zero _).symm))
  calc t⁻¹ * (t₀ * conjugation F E t₀) * (conjugation F E t)⁻¹
      = (t * conjugation F E t)⁻¹ * (t₀ * conjugation F E t₀) := by
        rw [mul_inv]; ring
    _ = 1 := by rw [htN, ht₀N, inv_mul_cancel₀]; exact (map_ne_zero _).mpr ha₀

end Langlands.CentralSimple.Landherr
