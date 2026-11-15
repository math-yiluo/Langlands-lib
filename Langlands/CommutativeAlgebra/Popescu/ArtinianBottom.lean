import Langlands.CommutativeAlgebra.Popescu.LocalLifting
import Langlands.CommutativeAlgebra.Popescu.RegularSequenceFlatStatement
import Langlands.CommutativeAlgebra.Popescu.CharZeroFieldFactorizationStatement
import Langlands.CommutativeAlgebra.Popescu.NilpotentLiftingStatement
import Langlands.CommutativeAlgebra.Popescu.RegularParameterTools
import Mathlib

/-! # The Artinian bottom of the proof of Stacks Lemma 10.3 (07FE) -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

open MvPolynomial

open TensorProduct in
/-- Property PT transfers along compatible ring isomorphisms of bases and targets. -/
theorem hasSmoothFactorizations_of_ringEquiv' {R₁ Λ₁ R₂ Λ₂ : Type u} [CommRing R₁] [CommRing Λ₁]
    [CommRing R₂] [CommRing Λ₂] [Algebra R₁ Λ₁] [Algebra R₂ Λ₂] (e : R₂ ≃+* R₁)
    (eΛ : Λ₂ ≃+* Λ₁) (he : ∀ r, eΛ (algebraMap R₂ Λ₂ r) = algebraMap R₁ Λ₁ (e r))
    (h : HasSmoothFactorizations R₁ Λ₁) : HasSmoothFactorizations R₂ Λ₂ := by
  intro A _ _ _ f
  let _ : Algebra R₁ A := ((algebraMap R₂ A).comp e.symm.toRingHom).toAlgebra
  let _ : Algebra R₁ R₂ := e.symm.toRingHom.toAlgebra
  let _ : Algebra R₁ Λ₂ := ((algebraMap R₂ Λ₂).comp e.symm.toRingHom).toAlgebra
  have : IsScalarTower R₁ R₂ A := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R₁ R₂ Λ₂ := .of_algebraMap_eq fun _ => rfl
  have : Algebra.FinitePresentation R₁ R₂ :=
    .equiv (AlgEquiv.ofRingEquiv (f := e.symm) fun _ => rfl : R₁ ≃ₐ[R₁] R₂)
  have : Algebra.FinitePresentation R₁ A := .trans R₁ R₂ A
  let eΛ' : Λ₁ ≃ₐ[R₁] Λ₂ := AlgEquiv.ofRingEquiv (f := eΛ.symm) fun r => by
    show eΛ.symm (algebraMap R₁ Λ₁ r) = algebraMap R₂ Λ₂ (e.symm r)
    rw [RingEquiv.symm_apply_eq, he, e.apply_symm_apply]
  obtain ⟨B, _, _, hB, g, h, hgh⟩ := h A ((eΛ'.symm : Λ₂ →ₐ[R₁] Λ₁).comp (f.restrictScalars R₁))
  have hA : ∀ r : R₂, algebraMap R₂ A r = algebraMap R₁ A (e r) := fun r => by
    show _ = algebraMap R₂ A (e.symm (e r))
    rw [e.symm_apply_apply]
  let g₂ : A →ₐ[R₂] R₂ ⊗[R₁] B :=
    { toRingHom := (Algebra.TensorProduct.includeRight.comp g : A →ₐ[R₁] R₂ ⊗[R₁] B).toRingHom
      commutes' := fun r => by
        show (1 : R₂) ⊗ₜ[R₁] g (algebraMap R₂ A r) = algebraMap R₂ (R₂ ⊗[R₁] B) r
        rw [hA, g.commutes, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
          TensorProduct.smul_tmul', Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
          RingHom.id_apply, Algebra.smul_def, mul_one]
        show e.symm (e r) ⊗ₜ[R₁] (1 : B) = _
        rw [e.symm_apply_apply] }
  refine ⟨R₂ ⊗[R₁] B, inferInstance, inferInstance, inferInstance, g₂,
    Algebra.TensorProduct.lift (Algebra.ofId R₂ Λ₂) ((eΛ' : Λ₁ →ₐ[R₁] Λ₂).comp h)
      (fun _ _ => Commute.all _ _), ?_⟩
  ext a
  have := congrArg (fun φ => eΛ' (φ a)) hgh
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgHom.coe_restrictScalars',
    AlgEquiv.apply_symm_apply] at this
  show Algebra.TensorProduct.lift (Algebra.ofId R₂ Λ₂) ((eΛ' : Λ₁ →ₐ[R₁] Λ₂).comp h)
    (fun _ _ => Commute.all _ _) ((1 : R₂) ⊗ₜ[R₁] g a) = f a
  rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  exact this


section Monomial

variable {σ R : Type*} [CommSemiring R]

theorem mem_span_monomial_of_X_pow_mul {S : Set (σ →₀ ℕ)} {i : σ} (hS : ∀ m ∈ S, m i = 0)
    (a : ℕ) {p : MvPolynomial σ R}
    (h : X i ^ a * p ∈ Ideal.span ((fun m => monomial m (1 : R)) '' S)) :
    p ∈ Ideal.span ((fun m => monomial m (1 : R)) '' S) := by
  induction a with
  | zero => simpa using h
  | succ a ih =>
    apply ih
    apply RegularParameter.mem_span_monomial_of_X_mul hS
    rwa [← mul_assoc, ← pow_succ']

end Monomial

section Annihilator

variable {S : Type*} [CommRing S]

/-- If `Ann(π) = Ann(π²)` modulo `J`, then `Ann(π) = Ann(π^m)` modulo `J`. -/
theorem mul_mem_of_pow_mul_mem {J : Ideal S} {π : S} (h : ∀ x, π ^ 2 * x ∈ J → π * x ∈ J) :
    ∀ (m : ℕ) (x : S), π ^ (m + 1) * x ∈ J → π * x ∈ J := by
  intro m
  induction m with
  | zero => intro x hx; simpa using hx
  | succ m ih =>
    intro x hx
    apply h
    have := ih (π * x) (by rw [← mul_assoc, ← pow_succ]; exact hx)
    rwa [← mul_assoc, ← pow_two] at this

/-- If `Ann(π) = Ann(π²)` modulo `J`, then the same holds for `π^c`, `c > 0`. -/
theorem pow_annihilator {J : Ideal S} {π : S} (h : ∀ x, π ^ 2 * x ∈ J → π * x ∈ J) {c : ℕ}
    (hc : 0 < c) (x : S) (hx : (π ^ c) ^ 2 * x ∈ J) : π ^ c * x ∈ J := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt hc
  have h1 : π * x ∈ J := mul_mem_of_pow_mul_mem h (2 * c + 1) x (by
    rw [← pow_mul] at hx; convert hx using 2; ring)
  rw [zero_add, pow_succ, mul_comm (π ^ c) π, mul_assoc, mul_left_comm]
  exact J.mul_mem_left _ h1

end Annihilator

section Variables

variable (k : Type*) [CommRing k] {d : ℕ}

theorem image_X_pow_eq (c e : ℕ) (T : Set (Fin d)) :
    (fun j => ((X j : MvPolynomial (Fin d) k) ^ c) ^ e) '' T =
      (fun m => monomial m (1 : k)) '' ((fun j => Finsupp.single j (c * e)) '' T) := by
  rw [Set.image_image]
  congr 1
  funext j
  rw [← pow_mul, X_pow_eq_monomial]

/-- Powers of the variables satisfy the annihilator condition of Stacks Lemma 9.2. -/
theorem X_pow_annihilator (c e : ℕ) (i : Fin d) (y : MvPolynomial (Fin d) k)
    (hy : (X i ^ c) ^ 2 * y ∈ Ideal.span ((fun j => (X j ^ c) ^ e) '' {j | j < i})) :
    X i ^ c * y ∈ Ideal.span ((fun j => ((X j : MvPolynomial (Fin d) k) ^ c) ^ e) '' {j | j < i}) := by
  rw [image_X_pow_eq] at hy ⊢
  refine mem_span_monomial_of_X_pow_mul (i := i) ?_ c ?_
  · rintro _ ⟨j, hj, rfl⟩
    rw [Finsupp.single_apply, ite_eq_right_iff.mpr fun h => absurd h (ne_of_lt hj)]
  · rwa [← mul_assoc, ← pow_two]

end Variables

section Flatness

/-- The kernel of the constant coefficient is generated by the variables. -/
theorem ker_constantCoeff_eq {k : Type*} [CommRing k] {d : ℕ} :
    RingHom.ker (constantCoeff : MvPolynomial (Fin d) k →+* k) = Ideal.span (Set.range X) := by
  apply le_antisymm
  · intro p hp
    rw [← Set.image_univ, mem_ideal_span_X_image]
    intro m hm
    by_contra h
    push Not at h
    have hm0 : m = 0 := Finsupp.ext fun i => h i (Set.mem_univ _)
    subst hm0
    rw [mem_support_iff, ← constantCoeff_eq] at hm
    exact hm hp
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp

theorem sub_C_constantCoeff_mem {k : Type*} [CommRing k] {d : ℕ} (p : MvPolynomial (Fin d) k) :
    p - C (constantCoeff p) ∈ Ideal.span (Set.range (X : Fin d → MvPolynomial (Fin d) k)) := by
  rw [← ker_constantCoeff_eq, RingHom.mem_ker, map_sub, constantCoeff_C, sub_self]

variable {k Λ : Type u} [Field k] [CommRing Λ] [Algebra k Λ] {d : ℕ}
  [Algebra (MvPolynomial (Fin d) k) Λ] [IsScalarTower k (MvPolynomial (Fin d) k) Λ]

/-- If the images of the variables generate the maximal ideal of `Λ_q`, the preimage of `q` in
`k[x]` is the ideal of the origin. -/
theorem comap_eq_span_X (π : Fin d → Λ) (hX : ∀ i, algebraMap (MvPolynomial (Fin d) k) Λ (X i) = π i)
    (q : Ideal Λ) [q.IsPrime]
    (hspan : Ideal.span (Set.range fun i => algebraMap Λ (Localization.AtPrime q) (π i)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime q)) :
    q.comap (algebraMap (MvPolynomial (Fin d) k) Λ) = Ideal.span (Set.range X) := by
  have hπq : ∀ i, π i ∈ q := fun i => by
    have : algebraMap Λ (Localization.AtPrime q) (π i) ∈ IsLocalRing.maximalIdeal _ := by
      rw [← hspan]; exact Ideal.subset_span ⟨i, rfl⟩
    rwa [← Localization.AtPrime.under_maximalIdeal (I := q), Ideal.mem_comap]
  have hle : Ideal.span (Set.range X) ≤ q.comap (algebraMap (MvPolynomial (Fin d) k) Λ) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap, hX]
    exact hπq i
  refine le_antisymm (fun p hp => ?_) hle
  have h1 := hle (sub_C_constantCoeff_mem p)
  have h2 : algebraMap (MvPolynomial (Fin d) k) Λ (C (constantCoeff p)) ∈ q := by
    have := q.sub_mem hp h1
    rwa [← map_sub, sub_sub_cancel] at this
  rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply] at h2
  by_cases h0 : constantCoeff p = 0
  · have := sub_C_constantCoeff_mem p
    rwa [h0, map_zero, sub_zero] at this
  · exfalso
    apply (‹q.IsPrime›).ne_top
    rw [Ideal.eq_top_iff_one]
    have hu : IsUnit (algebraMap k Λ (constantCoeff p)) := (Ne.isUnit h0).map _
    obtain ⟨v, hv⟩ := hu.exists_left_inv
    rw [← hv]
    exact q.mul_mem_left _ h2

/-- Stacks Lemma 10.128.2 (07DY) applied to `k[x]_{(x)} → Λ_q`: if the images of the variables
form a regular system of parameters of `Λ_q` that is a regular sequence, then `Λ_q` is flat
over `k[x]`. -/
theorem flat_localization_of_regular (n3 : RegularSequenceFlatStatement.{u}) [IsNoetherianRing Λ]
    (π : Fin d → Λ) (hX : ∀ i, algebraMap (MvPolynomial (Fin d) k) Λ (X i) = π i)
    (q : Ideal Λ) [q.IsPrime]
    (hspan : Ideal.span (Set.range fun i => algebraMap Λ (Localization.AtPrime q) (π i)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime q))
    (hreg : RingTheory.Sequence.IsWeaklyRegular (Localization.AtPrime q)
      (List.ofFn fun i => algebraMap Λ (Localization.AtPrime q) (π i))) :
    Module.Flat (MvPolynomial (Fin d) k) (Localization.AtPrime q) := by
  set R := MvPolynomial (Fin d) k
  set P := q.comap (algebraMap R Λ) with hP
  have hPX : P = Ideal.span (Set.range X) := comap_eq_span_X π hX q hspan
  let φ : Localization.AtPrime P →+* Localization.AtPrime q :=
    Localization.localRingHom P q (algebraMap R Λ) rfl
  let _ : Algebra (Localization.AtPrime P) (Localization.AtPrime q) := φ.toAlgebra
  have hφ : ∀ x : R, φ (algebraMap R _ x) = algebraMap Λ _ (algebraMap R Λ x) := fun x =>
    Localization.localRingHom_to_map P q (algebraMap R Λ) rfl x
  have : IsScalarTower R (Localization.AtPrime P) (Localization.AtPrime q) :=
    .of_algebraMap_eq fun x => by
      rw [RingHom.algebraMap_toAlgebra, hφ, ← IsScalarTower.algebraMap_apply]
  have : IsLocalHom (algebraMap (Localization.AtPrime P) (Localization.AtPrime q)) :=
    Localization.isLocalHom_localRingHom P q (algebraMap R Λ) rfl
  have hflat := n3 (Localization.AtPrime P) (Localization.AtPrime q)
    (List.ofFn fun i => algebraMap R (Localization.AtPrime P) (X i)) ?_ ?_ ?_
  · exact Module.Flat.trans R (Localization.AtPrime P) (Localization.AtPrime q)
  · rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P,
      congrArg (Ideal.map (algebraMap R (Localization.AtPrime P))) hPX, Ideal.map_span, Ideal.ofList]
    congr 1
    ext x
    simp [List.mem_ofFn]
  · have := (RegularParameter.isWeaklyRegular_X k d).of_flat (S := Localization.AtPrime P)
    simpa [List.map_ofFn, Function.comp_def] using this
  · have : (List.ofFn fun i => algebraMap R (Localization.AtPrime P) (X i)).map
        (algebraMap (Localization.AtPrime P) (Localization.AtPrime q)) =
        List.ofFn fun i => algebraMap Λ (Localization.AtPrime q) (π i) := by
      rw [List.map_ofFn]
      congr 1
      funext i
      simp only [Function.comp_apply, RingHom.algebraMap_toAlgebra, hφ]
      exact congrArg _ (hX i)
    rw [this]
    exact hreg

end Flatness

section QuotientFactorization

variable {k Λ : Type u} [Field k] [CommRing Λ] [Algebra k Λ] {d : ℕ}
  [Algebra (MvPolynomial (Fin d) k) Λ] [IsScalarTower k (MvPolynomial (Fin d) k) Λ]

/-- Property PT for `k[x]/K → Λ_q/KΛ_q` when `K` is a monomial-type ideal between a power of the
ideal of the origin and that ideal: Stacks Proposition 5.3 (nilpotent lifting) applied to the
flat map, with the closed fibre `k → κ(q)` handled by the field case in characteristic zero. -/
theorem hasSmoothFactorizations_quot (n2 : CharZeroFieldFactorizationStatement.{u})
    (h5 : NilpotentLiftingStatement.{u}) [CharZero k]
    (π : Fin d → Λ) (hX : ∀ i, algebraMap (MvPolynomial (Fin d) k) Λ (X i) = π i)
    (q : Ideal Λ) [q.IsPrime]
    (hspan : Ideal.span (Set.range fun i => algebraMap Λ (Localization.AtPrime q) (π i)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime q))
    [hflat : Module.Flat (MvPolynomial (Fin d) k) (Localization.AtPrime q)]
    (K : Ideal (MvPolynomial (Fin d) k)) (hK1 : K ≤ Ideal.span (Set.range X))
    (hK2 : ∀ i, ∃ m, (X i : MvPolynomial (Fin d) k) ^ m ∈ K) :
    HasSmoothFactorizations (MvPolynomial (Fin d) k ⧸ K)
      (Localization.AtPrime q ⧸ K.map (algebraMap (MvPolynomial (Fin d) k)
        (Localization.AtPrime q))) := by
  classical
  set R := MvPolynomial (Fin d) k
  set L := Localization.AtPrime q
  set Rb := R ⧸ K
  set KL := K.map (algebraMap R L)
  set Lb := L ⧸ KL
  have hXL : ∀ i, algebraMap R L (X i) = algebraMap Λ L (π i) := fun i => by
    rw [IsScalarTower.algebraMap_apply R Λ L, hX]
  -- flatness
  have : Module.Flat Rb Lb :=
    Module.Flat.of_linearEquiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor L K).toLinearEquiv
  -- the nilpotent ideal
  set I : Ideal Rb := (Ideal.span (Set.range X)).map (Ideal.Quotient.mk K) with hIdef
  have hInil : IsNilpotent I := by
    have hfg : I.FG := by
      rw [hIdef, Ideal.map_span]
      exact Submodule.fg_span (Set.Finite.image _ (Set.finite_range _))
    rw [hfg.isNilpotent_iff_le_nilradical, hIdef, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    obtain ⟨m, hm⟩ := hK2 i
    exact ⟨m, by rw [← map_pow]; exact (Submodule.mem_bot _).mpr (Ideal.Quotient.eq_zero_iff_mem.mpr hm)⟩
  refine h5 Rb Lb I hInil this ?_
  -- the closed fibre
  set κ := IsLocalRing.ResidueField L
  have hn2 : HasSmoothFactorizations k κ := n2 k κ
  -- the base
  set ι : k →+* Rb ⧸ I := algebraMap k (Rb ⧸ I)
  have hι : ∀ p : R, Ideal.Quotient.mk I (Ideal.Quotient.mk K p) = ι (constantCoeff p) := by
    intro p
    rw [Ideal.Quotient.eq.mpr (show Ideal.Quotient.mk K p - Ideal.Quotient.mk K (C (constantCoeff p))
      ∈ I from by rw [← map_sub]; exact Ideal.mem_map_of_mem _ (sub_C_constantCoeff_mem p))]
    rfl
  have hIne : I ≠ ⊤ := by
    intro htop
    have : (1 : R) ∈ Ideal.span (Set.range X) := by
      have h1 : Ideal.comap (Ideal.Quotient.mk K) I = Ideal.span (Set.range X) := by
        rw [comap_mk_map_mk, sup_eq_left.mpr hK1]
      rw [← h1, htop, Ideal.comap_top]
      trivial
    rw [← ker_constantCoeff_eq, RingHom.mem_ker, map_one] at this
    exact one_ne_zero this
  have : Nontrivial (Rb ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIne
  have hιbij : Function.Bijective ι := by
    refine ⟨ι.injective, fun z => ?_⟩
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨constantCoeff p, (hι p).symm⟩
  let e : Rb ⧸ I ≃+* k := (RingEquiv.ofBijective ι hιbij).symm
  -- the fibre
  have hmax : Ideal.span (Set.range fun i => algebraMap R L (X i)) = IsLocalRing.maximalIdeal L := by
    simp_rw [hXL]; exact hspan
  have hKL : KL ≤ IsLocalRing.maximalIdeal L := by
    rw [← hmax]
    refine (Ideal.map_mono hK1).trans ?_
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  let Φ₀ : Lb →+* κ := Ideal.Quotient.lift KL (IsLocalRing.residue L) fun y hy =>
    (IsLocalRing.residue_eq_zero_iff y).mpr (hKL hy)
  have hIΦ : I.map (algebraMap Rb Lb) ≤ RingHom.ker Φ₀ := by
    rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    show IsLocalRing.residue L (algebraMap R L (X i)) = 0
    rw [IsLocalRing.residue_eq_zero_iff, ← hmax]
    exact Ideal.subset_span ⟨i, rfl⟩
  let Φ : Lb ⧸ I.map (algebraMap Rb Lb) →+* κ := Ideal.Quotient.lift _ Φ₀ hIΦ
  have hΦ : ∀ y : L, Φ (Ideal.Quotient.mk _ (Ideal.Quotient.mk KL y)) = IsLocalRing.residue L y :=
    fun y => rfl
  have hΦbij : Function.Bijective Φ := by
    refine ⟨?_, fun z => ?_⟩
    · rw [RingHom.injective_iff_ker_eq_bot, eq_bot_iff]
      intro z hz
      obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
      rw [RingHom.mem_ker, hΦ, IsLocalRing.residue_eq_zero_iff, ← hmax] at hz
      rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
      have : Ideal.span (Set.range fun i => algebraMap R L (X i)) ≤
          Ideal.comap (Ideal.Quotient.mk KL) (I.map (algebraMap Rb Lb)) := by
        rw [Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        rw [SetLike.mem_coe, Ideal.mem_comap]
        have h1 : Ideal.Quotient.mk K (X i) ∈ I :=
          Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i, rfl⟩)
        have h2 := Ideal.mem_map_of_mem (algebraMap Rb Lb) h1
        rwa [Ideal.Quotient.algebraMap_quotient_map_quotient] at h2
      exact this hz
    · obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective z
      exact ⟨_, hΦ y⟩
  let eΛ : Lb ⧸ I.map (algebraMap Rb Lb) ≃+* κ := RingEquiv.ofBijective Φ hΦbij
  refine hasSmoothFactorizations_of_ringEquiv' e eΛ ?_ hn2
  intro r
  obtain ⟨a, rfl⟩ := hιbij.2 r
  have hea : e (ι a) = a := (RingEquiv.ofBijective ι hιbij).symm_apply_apply a
  rw [hea, RingEquiv.ofBijective_apply]
  have hιa : ι a = Ideal.Quotient.mk I (Ideal.Quotient.mk K (C a)) := rfl
  rw [hιa, Ideal.Quotient.algebraMap_quotient_map_quotient,
    Ideal.Quotient.algebraMap_quotient_map_quotient, hΦ, ← MvPolynomial.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply]
  rfl

end QuotientFactorization

section Bottom

variable {k Λ : Type u} [Field k] [CommRing Λ] [Algebra k Λ] {d : ℕ}
  [Algebra (MvPolynomial (Fin d) k) Λ] [IsScalarTower k (MvPolynomial (Fin d) k) Λ]

omit [Algebra k Λ] [IsScalarTower k (MvPolynomial (Fin d) k) Λ] in
/-- A prime between `KΛ` and `q` is `q`, when the images of the variables generate `qΛ_q` and
some power of each variable lies in `K`. -/
theorem le_of_between (π : Fin d → Λ) (hX : ∀ i, algebraMap (MvPolynomial (Fin d) k) Λ (X i) = π i)
    (q : Ideal Λ) [q.IsPrime]
    (hspan : Ideal.span (Set.range fun i => algebraMap Λ (Localization.AtPrime q) (π i)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime q))
    (K : Ideal (MvPolynomial (Fin d) k))
    (hK2 : ∀ i, ∃ m, (X i : MvPolynomial (Fin d) k) ^ m ∈ K)
    (P : Ideal Λ) [P.IsPrime] (hKP : K.map (algebraMap _ Λ) ≤ P) (hPq : P ≤ q) : q ≤ P := by
  have hdisj : Disjoint (q.primeCompl : Set Λ) P := by
    rw [Set.disjoint_left]
    intro x hx hxP
    exact hx (hPq hxP)
  have hPL : (P.map (algebraMap Λ (Localization.AtPrime q))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ P ‹_› hdisj
  have hπP : ∀ i, π i ∈ P := fun i => by
    obtain ⟨m, hm⟩ := hK2 i
    have := hKP (Ideal.mem_map_of_mem (algebraMap _ Λ) hm)
    rw [map_pow, hX] at this
    exact ‹P.IsPrime›.mem_of_pow_mem m this
  have hmax : IsLocalRing.maximalIdeal (Localization.AtPrime q) ≤
      P.map (algebraMap Λ (Localization.AtPrime q)) := by
    rw [← hspan, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact Ideal.mem_map_of_mem _ (hπP i)
  have h1 := Ideal.comap_mono (f := algebraMap Λ (Localization.AtPrime q)) hmax
  have h2 : Ideal.comap (algebraMap Λ (Localization.AtPrime q))
      (IsLocalRing.maximalIdeal (Localization.AtPrime q)) = q :=
    Localization.AtPrime.under_maximalIdeal
  have h3 : Ideal.comap (algebraMap Λ (Localization.AtPrime q))
      (P.map (algebraMap Λ (Localization.AtPrime q))) = P :=
    IsLocalization.under_map_of_isPrime_disjoint q.primeCompl (Localization.AtPrime q) ‹_› hdisj
  rwa [h2, h3] at h1

/-- The bottom condition of Stacks Lemma 9.2 in the situation of Lemma 10.3. -/
theorem bottomCondition_of_flat (n2 : CharZeroFieldFactorizationStatement.{u})
    (h5 : NilpotentLiftingStatement.{u}) [CharZero k]
    (π : Fin d → Λ) (hX : ∀ i, algebraMap (MvPolynomial (Fin d) k) Λ (X i) = π i)
    (q : Ideal Λ) [q.IsPrime]
    (hspan : Ideal.span (Set.range fun i => algebraMap Λ (Localization.AtPrime q) (π i)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime q))
    [Module.Flat (MvPolynomial (Fin d) k) (Localization.AtPrime q)]
    (K : Ideal (MvPolynomial (Fin d) k)) (hK1 : K ≤ Ideal.span (Set.range X))
    (hK2 : ∀ i, ∃ m, (X i : MvPolynomial (Fin d) k) ^ m ∈ K) :
    BottomCondition (MvPolynomial (Fin d) k) Λ q K := by
  intro R₁ Λ₁ _ _ _ σ τ hσ hτ hkσ hkτ hστ Q _ hQ
  set R := MvPolynomial (Fin d) k
  set L := Localization.AtPrime q
  constructor
  · -- `Q` is a minimal prime
    refine ⟨⟨inferInstance, bot_le⟩, fun Q' hQ' hle => ?_⟩
    have := hQ'.1
    have hle' : q ≤ Q'.comap τ := by
      refine le_of_between π hX q hspan K hK2 (Q'.comap τ) ?_ ?_
      · rw [← hkτ, RingHom.ker_eq_comap_bot]
        exact Ideal.comap_mono bot_le
      · rw [← hQ]
        exact Ideal.comap_mono hle
    intro x hx
    obtain ⟨y, rfl⟩ := hτ x
    have : y ∈ q := by rw [← hQ]; exact hx
    exact hle' this
  · -- property PT
    have hPT := hasSmoothFactorizations_quot n2 h5 π hX q hspan K hK1 hK2
    let ψ : L →+* Localization.AtPrime Q := Localization.localRingHom q Q τ hQ.symm
    have hψ : Function.Surjective ψ :=
      (RingHom.surjectiveOnStalks_of_surjective hτ).localRingHom_surjective q Q hQ.symm
    have hψmap : ∀ y : Λ, ψ (algebraMap Λ L y) = algebraMap Λ₁ _ (τ y) := fun y =>
      Localization.localRingHom_to_map q Q τ hQ.symm y
    have hKΛL : (K.map (algebraMap R Λ)).map (algebraMap Λ L) = K.map (algebraMap R L) := by
      rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    have hker : RingHom.ker ψ = K.map (algebraMap R L) := by
      apply le_antisymm
      · intro z hz
        obtain ⟨a, s, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl z
        rw [RingHom.mem_ker, Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff] at hz
        obtain ⟨⟨t, ht⟩, htz⟩ := hz
        obtain ⟨t', rfl⟩ := hτ t
        rw [← hKΛL, IsLocalization.mk'_mem_map_algebraMap_iff]
        refine ⟨t', ?_, ?_⟩
        · show t' ∉ q
          rw [← hQ]
          exact ht
        · rw [← hkτ, RingHom.mem_ker, map_mul]
          exact htz
      · rw [← hKΛL, Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
        intro x hx
        rw [Ideal.mem_comap, Ideal.mem_comap, RingHom.mem_ker, hψmap]
        have : τ (algebraMap R Λ x) = 0 := by
          rw [← RingHom.mem_ker, hkτ]
          exact Ideal.mem_map_of_mem _ hx
        rw [this, map_zero]
    let e : R₁ ≃+* R ⧸ K :=
      ((Ideal.quotEquivOfEq hkσ.symm).trans (RingHom.quotientKerEquivOfSurjective hσ)).symm
    have he : ∀ x : R, e (σ x) = Ideal.Quotient.mk K x := fun x => by
      rw [RingEquiv.symm_apply_eq]
      rfl
    let eΛ : Localization.AtPrime Q ≃+* L ⧸ K.map (algebraMap R L) :=
      (RingHom.quotientKerEquivOfSurjective hψ).symm.trans (Ideal.quotEquivOfEq hker)
    have heΛ : ∀ y : L, eΛ (ψ y) = Ideal.Quotient.mk _ y := fun y => by
      show Ideal.quotEquivOfEq hker ((RingHom.quotientKerEquivOfSurjective hψ).symm (ψ y)) = _
      have : (RingHom.quotientKerEquivOfSurjective hψ).symm (ψ y) = Ideal.Quotient.mk _ y := by
        rw [RingEquiv.symm_apply_eq]
        rfl
      rw [this]
      rfl
    refine hasSmoothFactorizations_of_ringEquiv' e eΛ ?_ hPT
    intro r
    obtain ⟨x, rfl⟩ := hσ r
    rw [he, Ideal.Quotient.algebraMap_quotient_map_quotient,
      IsScalarTower.algebraMap_apply R₁ Λ₁ (Localization.AtPrime Q), ← hστ, ← hψmap, heΛ,
      ← IsScalarTower.algebraMap_apply]

end Bottom

end Langlands.CommutativeAlgebra.Popescu
