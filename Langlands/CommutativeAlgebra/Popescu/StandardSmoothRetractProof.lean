import Mathlib
import Langlands.CommutativeAlgebra.Popescu.StandardSmoothRetractStatement

/-! # Proof of Stacks 07CH: smooth algebras are retracts of standard smooth algebras -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu.StandardSmoothRetract

/-- A Nakayama-type lemma: if `φ : M → N` (with `M` finite and `N` finite projective) is
surjective modulo `J` and its kernel lies in `J • M`, then after inverting a suitable
`g ∈ 1 + J` the map `φ` becomes surjective and injective. -/
theorem exists_smul_range_and_smul_ker {C M N : Type*} [CommRing C] [AddCommGroup M]
    [Module C M] [Module.Finite C M] [AddCommGroup N] [Module C N] [Module.Finite C N]
    [Module.Projective C N] (J : Ideal C) (φ : M →ₗ[C] N)
    (h₁ : (⊤ : Submodule C N) ≤ LinearMap.range φ ⊔ J • ⊤)
    (h₂ : ∀ m, φ m = 0 → m ∈ J • (⊤ : Submodule C M)) :
    ∃ g : C, g - 1 ∈ J ∧ (∀ n, g • n ∈ LinearMap.range φ) ∧ ∀ m, φ m = 0 → g • m = 0 := by
  obtain ⟨r, hr, hrN⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
    (Module.Finite.fg_top (R := C) (M := N)) le_rfl h₁
  have hrN' : ∀ n : N, r • n ∈ LinearMap.range φ := fun n ↦
    hrN (Submodule.smul_mem_pointwise_smul n r ⊤ trivial)
  let rr : N →ₗ[C] LinearMap.range φ := (r • LinearMap.id).codRestrict _ hrN'
  obtain ⟨t, ht⟩ := Module.projective_lifting_property φ.rangeRestrict rr
    (LinearMap.surjective_rangeRestrict φ)
  have ht' : ∀ n, φ (t n) = r • n := fun n ↦ congrArg Subtype.val (LinearMap.congr_fun ht n)
  let e : M →ₗ[C] M := r • LinearMap.id - t ∘ₗ φ
  have he : ∀ m, φ (e m) = 0 := by intro m; simp [e, ht']
  have he' : ∀ m, φ m = 0 → e m = r • m := by intro m hm; simp [e, hm]
  let K' := LinearMap.range e
  have hK'fg : K'.FG := by
    change (LinearMap.range e).FG
    rw [LinearMap.range_eq_map]; exact (Module.Finite.fg_top).map e
  have hK' : K' ≤ J • K' := by
    rintro _ ⟨m, rfl⟩
    have hm : e m ∈ J • (⊤ : Submodule C M) := h₂ _ (he m)
    have hmap : (J • (⊤ : Submodule C M)).map e ≤ J • K' := by
      rw [Submodule.map_smul'', ← LinearMap.range_eq_map]
    have h1 : r • e m ∈ J • K' := he' _ (he m) ▸ hmap ⟨e m, hm, rfl⟩
    have h2 : (r - 1) • e m ∈ J • K' := Submodule.smul_mem_smul hr ⟨m, rfl⟩
    have : e m = r • e m - (r - 1) • e m := by simp [sub_smul]
    rw [this]; exact sub_mem h1 h2
  obtain ⟨r', hr', hr'K⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul J K' hK'fg hK'
  refine ⟨r * r', ?_, ?_, ?_⟩
  · have : r * r' - 1 = r * (r' - 1) + (r - 1) := by ring
    rw [this]; exact J.add_mem (J.mul_mem_left _ hr') hr
  · intro n
    rw [mul_comm, mul_smul]
    exact (LinearMap.range φ).smul_mem r' (hrN' n)
  · intro m hm
    rw [mul_comm, mul_smul, ← he' m hm]
    exact hr'K _ ⟨m, rfl⟩

section Setup

open MvPolynomial

variable {A : Type u} [CommRing A] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The linear form `v ↦ ∑ⱼ vⱼ Xⱼ`. -/
noncomputable def linForm : (ι → A) →ₗ[A] MvPolynomial ι A :=
  Fintype.linearCombination A X

@[simp] lemma linForm_single (i : ι) : linForm (Pi.single i (1 : A)) = X i := by
  simp [linForm]

omit [DecidableEq ι] in
lemma aeval_linForm {T : Type*} [CommRing T] [Algebra A T] (f : ι → T) (w : ι → A) :
    aeval f (linForm w) = ∑ j, w j • f j := by
  simp [linForm, Fintype.linearCombination_apply, map_sum]

variable (p : (ι → A) →ₗ[A] (ι → A))

/-- The ideal `(Xᵢ − L(p eᵢ))ᵢ` cutting out the vector bundle `Sym(im p)`. -/
noncomputable def relIdeal : Ideal (MvPolynomial ι A) :=
  Ideal.span (Set.range fun i ↦ X i - linForm (p (Pi.single i 1)))

lemma relIdeal_fg : (relIdeal p).FG :=
  Submodule.fg_span (Set.finite_range _)

lemma linForm_sub_mem (v : ι → A) : linForm v - linForm (p v) ∈ relIdeal p := by
  let f : (ι → A) →ₗ[A] MvPolynomial ι A := linForm - linForm ∘ₗ p
  have hv : v ∈ Submodule.span A (Set.range (Pi.basisFun A ι)) := by
    rw [(Pi.basisFun A ι).span_eq]; trivial
  change f v ∈ (relIdeal p).restrictScalars A
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    have : X i - linForm (p (Pi.single i 1)) ∈ relIdeal p := Ideal.subset_span ⟨i, rfl⟩
    simpa [f] using this
  | zero => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | smul a x _ hx => simpa using Submodule.smul_mem _ a hx

/-- The `A`-algebra `C = A[X] ⧸ (Xᵢ − L(p eᵢ))`. -/
abbrev Cr := MvPolynomial ι A ⧸ relIdeal p

variable {p}

lemma relIdeal_le_ker {T : Type*} [CommRing T] [Algebra A T] (f : ι → T)
    (hf : ∀ i, ∑ j, p (Pi.single i 1) j • f j = f i) :
    relIdeal p ≤ RingHom.ker (aeval f).toRingHom := by
  rw [relIdeal, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  simp [aeval_linForm, hf]

lemma eq_sum_single (w : ι → A) : ∑ j, w j • Pi.single j (1 : A) = w := by
  simpa using (Pi.basisFun A ι).sum_repr w

lemma sum_smul_map_single {M : Type*} [AddCommGroup M] [Module A M] (q : (ι → A) →ₗ[A] M)
    (w : ι → A) : ∑ j, w j • q (Pi.single j 1) = q w := by
  calc ∑ j, w j • q (Pi.single j 1) = q (∑ j, w j • Pi.single j 1) := by
        simp only [map_sum, map_smul]
    _ = q w := by rw [eq_sum_single]

/-- The augmentation `C → A`, `Xᵢ ↦ 0`. -/
noncomputable def eps : Cr p →ₐ[A] A :=
  Ideal.Quotient.liftₐ _ (aeval 0) fun a ha ↦
    (RingHom.mem_ker).mp (relIdeal_le_ker (p := p) (0 : ι → A) (by simp) ha)

@[simp] lemma eps_mk_X (i : ι) : eps (p := p) (Ideal.Quotient.mk _ (X i)) = 0 := by
  simp [eps]

/-- The `A`-algebra map `C → A ⊕ ε(ι → A)`, `Xᵢ ↦ ε · p eᵢ`, encoding the derivation
`C → im p`. -/
noncomputable def sig (hp : ∀ v, p (p v) = p v) : Cr p →ₐ[A] TrivSqZeroExt A (ι → A) :=
  Ideal.Quotient.liftₐ _ (aeval fun i ↦ TrivSqZeroExt.inr (p (Pi.single i 1))) fun a ha ↦ by
    have key : ∀ i, ∑ j, p (Pi.single i 1) j • TrivSqZeroExt.inr (p (Pi.single j 1)) =
        (TrivSqZeroExt.inr (p (Pi.single i 1)) : TrivSqZeroExt A (ι → A)) := by
      intro i
      have := sum_smul_map_single ((TrivSqZeroExt.inrHom A (ι → A)) ∘ₗ p) (p (Pi.single i 1))
      simpa [hp] using this
    exact (RingHom.mem_ker).mp (relIdeal_le_ker (p := p) _ key ha)

variable (hp : ∀ v, p (p v) = p v)

@[simp] lemma sig_mk_X (i : ι) :
    sig hp (Ideal.Quotient.mk _ (X i)) = TrivSqZeroExt.inr (p (Pi.single i 1)) := by
  rw [sig, Ideal.Quotient.liftₐ_apply]
  exact aeval_X _ _

lemma sig_fst (c : Cr p) : (sig hp c).fst = eps c := by
  have : (TrivSqZeroExt.fstHom A A (ι → A)).comp (sig hp) = eps := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    simp [eps]
  exact congr($this c)

/-- The section `C → A[X]`, `Xᵢ ↦ L(p eᵢ)`. -/
noncomputable def sec : Cr p →ₐ[A] MvPolynomial ι A :=
  Ideal.Quotient.liftₐ _ (aeval fun i ↦ linForm (p (Pi.single i 1))) fun a ha ↦ by
    have key : ∀ i, ∑ j, p (Pi.single i 1) j • linForm (p (Pi.single j 1)) =
        linForm (p (Pi.single i 1)) := by
      intro i
      have := sum_smul_map_single (linForm ∘ₗ p) (p (Pi.single i 1))
      simpa [hp] using this
    exact (RingHom.mem_ker).mp (relIdeal_le_ker (p := p) _ key ha)

lemma mk_sec (c : Cr p) : Ideal.Quotient.mk _ (sec hp c) = c := by
  have : (Ideal.Quotient.mkₐ A (relIdeal p)).comp (sec hp) = AlgHom.id A _ := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    simp only [sec, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.liftₐ_apply,
      AlgHom.id_apply]
    rw [Ideal.Quotient.eq]
    have h2 : X i - linForm (p (Pi.single i 1)) ∈ relIdeal p := Ideal.subset_span ⟨i, rfl⟩
    simpa using neg_mem h2
  exact congr($this c)

include hp in
lemma smooth_Cr : Algebra.Smooth A (Cr p) where
  formallySmooth := Algebra.FormallySmooth.of_split (Ideal.Quotient.mkₐ A (relIdeal p))
    ((Ideal.Quotient.mkₐ A _).comp (sec hp)) (AlgHom.ext fun c ↦ mk_sec hp c)
  finitePresentation := Algebra.FinitePresentation.quotient (relIdeal_fg p)

end Setup

section Main

open MvPolynomial KaehlerDifferential

variable (R : Type u) {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The map `ρ : A^ι → Ω[A⁄R]`, `eᵢ ↦ d aᵢ`. -/
noncomputable def rho (a : ι → A) : (ι → A) →ₗ[A] Ω[A⁄R] :=
  Fintype.linearCombination A fun i ↦ D R A (a i)

lemma rho_surjective {n : ℕ} (f : MvPolynomial (Fin n) R →ₐ[R] A)
    (hf : Function.Surjective f) : Function.Surjective (rho R fun k ↦ f (X k)) := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  refine (span_range_derivation R A).ge.trans (Submodule.span_le.mpr ?_)
  rintro _ ⟨y, rfl⟩
  obtain ⟨P, rfl⟩ := hf y
  induction P using MvPolynomial.induction_on with
  | C r => rw [MvPolynomial.algHom_C, Derivation.map_algebraMap]; exact zero_mem _
  | add P Q hP hQ => rw [map_add, map_add]; exact add_mem hP hQ
  | mul_X P k hP =>
    rw [map_mul, Derivation.leibniz]
    exact add_mem (Submodule.smul_mem _ _ ⟨Pi.single k 1, by simp [rho]⟩)
      (Submodule.smul_mem _ _ hP)

variable {R} (a : ι → A) (p : (ι → A) →ₗ[A] (ι → A))

/-- The images `xᵢ` of the variables in `C`. -/
noncomputable abbrev xx (i : ι) : Cr p := Ideal.Quotient.mk _ (X i)

/-- The elements `zᵢ = aᵢ − xᵢ` of `C`. -/
noncomputable abbrev zz (i : ι) : Cr p := algebraMap A (Cr p) (a i) - xx p i

variable (R) in
/-- The map `ψ : C^ι → Ω[C⁄R]`, `eᵢ ↦ d zᵢ`. -/
noncomputable def psi : (ι → Cr p) →ₗ[Cr p] Ω[Cr p⁄R] :=
  Fintype.linearCombination (Cr p) fun i ↦ D R (Cr p) (zz a p i)

lemma mk_linForm (b : ι → A) :
    Ideal.Quotient.mk (relIdeal p) (linForm b) = ∑ k, algebraMap A (Cr p) (b k) * xx p k := by
  have : Ideal.Quotient.mk (relIdeal p) (linForm b) =
      Ideal.Quotient.mkₐ A (relIdeal p) (linForm b) := rfl
  rw [this]
  simp [linForm, Fintype.linearCombination_apply, map_sum, Algebra.smul_def]
  rfl

lemma top_le_range_psi_sup (hb : ∀ ω : Ω[A⁄R], ∃ b, rho R a b = ω ∧ p b = 0) :
    (⊤ : Submodule (Cr p) Ω[Cr p⁄R]) ≤
      LinearMap.range (psi R a p) ⊔ RingHom.ker (eps (p := p)) • ⊤ := by
  set N := LinearMap.range (psi R a p) ⊔
    RingHom.ker (eps (p := p)) • (⊤ : Submodule (Cr p) Ω[Cr p⁄R]) with hN
  have hJ : ∀ (c : Cr p) (ω : Ω[Cr p⁄R]), eps c = 0 → c • ω ∈ N := fun c ω hc ↦
    Submodule.mem_sup_right (Submodule.smul_mem_smul (RingHom.mem_ker.mpr hc) trivial)
  have hψ : ∀ i, D R (Cr p) (zz a p i) ∈ N := fun i ↦
    Submodule.mem_sup_left ⟨Pi.single i 1, by simp [psi]⟩
  have hA : ∀ y : A, D R (Cr p) (algebraMap A (Cr p) y) ∈ N := by
    intro y
    obtain ⟨b, hb1, hb2⟩ := hb (D R A y)
    have e1 : D R (Cr p) (algebraMap A (Cr p) y) =
        ∑ k, algebraMap A (Cr p) (b k) • D R (Cr p) (algebraMap A (Cr p) (a k)) := by
      have := congrArg (KaehlerDifferential.map R R A (Cr p)) hb1
      simp only [rho, Fintype.linearCombination_apply, map_sum, map_smul, map_D] at this
      rw [← this]
      exact Finset.sum_congr rfl fun k _ ↦
        (algebraMap_smul (Cr p) (b k) (D R (Cr p) (algebraMap A (Cr p) (a k)))).symm
    have e2 : ∑ k, algebraMap A (Cr p) (b k) * xx p k = 0 := by
      rw [← mk_linForm, Ideal.Quotient.eq_zero_iff_mem]
      simpa [hb2] using linForm_sub_mem p b
    have e3 : ∑ k, algebraMap A (Cr p) (b k) • D R (Cr p) (xx p k) =
        -∑ k, xx p k • D R (Cr p) (algebraMap A (Cr p) (b k)) := by
      rw [eq_neg_iff_add_eq_zero, ← Finset.sum_add_distrib]
      have : ∀ k, algebraMap A (Cr p) (b k) • D R (Cr p) (xx p k) +
          xx p k • D R (Cr p) (algebraMap A (Cr p) (b k)) =
          D R (Cr p) (algebraMap A (Cr p) (b k) * xx p k) := fun k ↦
        (Derivation.leibniz _ _ _).symm
      rw [Finset.sum_congr rfl fun k _ ↦ this k, ← map_sum, e2, map_zero]
    have e4 : D R (Cr p) (algebraMap A (Cr p) y) =
        psi R a p (fun k ↦ algebraMap A (Cr p) (b k)) +
          ∑ k, algebraMap A (Cr p) (b k) • D R (Cr p) (xx p k) := by
      rw [e1, psi, Fintype.linearCombination_apply, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      have hz : algebraMap A (Cr p) (a k) = zz a p k + xx p k := by simp [zz]
      rw [hz, map_add]
      exact smul_add (algebraMap A (Cr p) (b k)) (D R (Cr p) (zz a p k)) (D R (Cr p) (xx p k))
    rw [e4, e3, ← sub_eq_add_neg]
    exact sub_mem (Submodule.mem_sup_left ⟨_, rfl⟩)
      (Submodule.sum_mem _ fun k _ ↦ hJ _ _ (eps_mk_X k))
  have hx : ∀ i, D R (Cr p) (xx p i) ∈ N := by
    intro i
    have : xx p i = algebraMap A (Cr p) (a i) - zz a p i := by simp [zz]
    rw [this, map_sub]
    exact sub_mem (hA _) (hψ i)
  have hall : ∀ c, D R (Cr p) c ∈ N := by
    intro c
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective c
    induction P using MvPolynomial.induction_on with
    | C y => exact hA y
    | add P Q hP hQ => rw [map_add, map_add]; exact add_mem hP hQ
    | mul_X P i hP =>
      rw [map_mul, Derivation.leibniz]
      exact add_mem (Submodule.smul_mem _ _ (hx i)) (Submodule.smul_mem _ _ hP)
  exact (span_range_derivation R (Cr p)).ge.trans
    (Submodule.span_le.mpr (by rintro _ ⟨c, rfl⟩; exact hall c))

lemma mem_smul_top_of_psi_eq_zero (hp : ∀ v, p (p v) = p v)
    (hw : ∀ w, rho R a w = 0 → p w = 0 → w = 0) (v : ι → Cr p) (hv : psi R a p v = 0) :
    v ∈ RingHom.ker (eps (p := p)) • (⊤ : Submodule (Cr p) (ι → Cr p)) := by
  have hepsz : ∀ i, eps (p := p) (zz a p i) = a i := by intro i; simp [zz]
  have key : (fun i ↦ eps (p := p) (v i)) = 0 := by
    let _ : Algebra (Cr p) A := (eps (p := p)).toRingHom.toAlgebra
    have : IsScalarTower R (Cr p) A := IsScalarTower.of_algebraMap_eq fun r ↦ by
      change _ = eps (p := p) (algebraMap R (Cr p) r)
      rw [IsScalarTower.algebraMap_apply R A (Cr p), AlgHom.commutes]
      rfl
    have ha : ∀ c, algebraMap (Cr p) A c = eps c := fun _ ↦ rfl
    have h1 : rho R a (fun i ↦ eps (p := p) (v i)) = 0 := by
      have := congrArg (KaehlerDifferential.map R R (Cr p) A) hv
      have hs : ∀ (c : Cr p) (ω : Ω[A⁄R]), c • ω = eps c • ω := fun c ω ↦
        (algebraMap_smul A c ω).symm
      simp only [psi, Fintype.linearCombination_apply, map_sum, map_smul, map_D, hs, ha,
        hepsz, map_zero] at this
      simpa [rho, Fintype.linearCombination_apply] using this
    have h2 : p (fun i ↦ eps (p := p) (v i)) = 0 := by
      let δ : Derivation R (Cr p) (ι → A) :=
        { toFun := fun c ↦ (sig hp c).snd
          map_add' := fun c d ↦ by simp
          map_smul' := fun r c ↦ by
            rw [← algebraMap_smul A r c, map_smul, TrivSqZeroExt.snd_smul, algebraMap_smul]
            rfl
          map_one_eq_zero' := by simp
          leibniz' := fun c d ↦ by
            change (sig hp (c * d)).snd = eps c • (sig hp d).snd + eps d • (sig hp c).snd
            rw [map_mul, TrivSqZeroExt.snd_mul, sig_fst, sig_fst, op_smul_eq_smul] }
      have hδ : ∀ c, δ c = (sig hp c).snd := fun _ ↦ rfl
      have hδz : ∀ i, δ (zz a p i) = -p (Pi.single i 1) := by
        intro i
        simp [hδ, zz, sig_mk_X, TrivSqZeroExt.algebraMap_eq_inl]
      have := congrArg δ.liftKaehlerDifferential hv
      have hs : ∀ (c : Cr p) (w : ι → A), c • w = eps c • w := fun _ _ ↦ rfl
      simp only [psi, Fintype.linearCombination_apply, map_sum, map_smul,
        Derivation.liftKaehlerDifferential_comp_D, hδz, hs, map_zero, smul_neg,
        Finset.sum_neg_distrib, neg_eq_zero] at this
      rwa [sum_smul_map_single p] at this
    exact hw _ h1 h2
  rw [← eq_sum_single v]
  exact Submodule.sum_mem _ fun i _ ↦
    Submodule.smul_mem_smul (RingHom.mem_ker.mpr (congr_fun key i)) trivial

end Main

/-- Bijectivity after localization: if `g` multiplies `N` into the range of `φ` and kills its
kernel, then the localized map `φ'` is bijective. -/
lemma bijective_of_isLocalizedModule {ι : Type} [Fintype ι] {C B N N' : Type*} [CommRing C]
    [CommRing B] [Algebra C B] (g : C) [IsLocalization.Away g B] [AddCommGroup N] [Module C N]
    [AddCommGroup N'] [Module C N'] [Module B N'] [IsScalarTower C B N']
    (l : N →ₗ[C] N') [IsLocalizedModule (Submonoid.powers g) l]
    (φ : (ι → C) →ₗ[C] N) (φ' : (ι → B) →ₗ[B] N')
    (hφ : ∀ u, φ' (fun i ↦ algebraMap C B (u i)) = l (φ u))
    (hr : ∀ x, g • x ∈ LinearMap.range φ) (hk : ∀ u, φ u = 0 → g • u = 0) :
    Function.Bijective φ' := by
  have hunit : ∀ k : ℕ, IsUnit (algebraMap C B (g ^ k)) := fun k ↦
    IsLocalization.map_units B (⟨g ^ k, k, rfl⟩ : Submonoid.powers g)
  refine ⟨(injective_iff_map_eq_zero φ').mpr fun w hw ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨⟨_, k, rfl⟩, hb⟩ :=
      IsLocalization.exist_integer_multiples (Submonoid.powers g) Finset.univ w
    have hb' : ∀ i, ∃ y, algebraMap C B y = (g ^ k : C) • w i := fun i ↦
      hb i (Finset.mem_univ i)
    choose u hu using hb'
    have h1 : l (φ u) = l 0 := by
      rw [← hφ, map_zero]
      have : (fun i ↦ algebraMap C B (u i)) = algebraMap C B (g ^ k) • w := by
        funext i; rw [hu, Pi.smul_apply, algebraMap_smul]
      rw [this, map_smul, hw, smul_zero]
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers g) h1
    have hm' : φ (g ^ m • u) = 0 := by
      rw [map_smul]
      have : g ^ m • φ u = g ^ m • (0 : N) := hm
      simpa using this
    have h2 := hk _ hm'
    funext i
    have h3 := congr_fun h2 i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h3
    have h4 : algebraMap C B (g ^ (1 + m + k)) * w i = 0 := by
      have : algebraMap C B (g * (g ^ m * u i)) = 0 := by rw [h3, map_zero]
      rw [map_mul, map_mul, hu, Algebra.smul_def] at this
      simp only [map_pow] at this ⊢
      linear_combination this
    exact (hunit _).mul_right_eq_zero.mp h4
  · obtain ⟨⟨x, _, k, rfl⟩, hx⟩ := IsLocalizedModule.surj (Submonoid.powers g) l y
    have hx' : g ^ k • y = l x := hx
    obtain ⟨u, hu⟩ := hr x
    obtain ⟨c, hc⟩ := hunit (k + 1)
    refine ⟨(↑c⁻¹ : B) • fun i ↦ algebraMap C B (u i), ?_⟩
    have : l (φ u) = algebraMap C B (g ^ (k + 1)) • y := by
      rw [hu, map_smul, ← hx', smul_smul, ← pow_succ', algebraMap_smul]
    rw [map_smul, hφ, this, ← hc, smul_smul, Units.inv_mul, one_smul]

open MvPolynomial KaehlerDifferential in
theorem standardSmoothRetract : StandardSmoothRetractStatement.{u} := by
  intro R A _ _ _ _
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R A)
  let a : Fin n → A := fun k ↦ f (X k)
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (rho R a) LinearMap.id
    (rho_surjective R f hf)
  have hs' : ∀ ω, rho R a (s ω) = ω := fun ω ↦ LinearMap.congr_fun hs ω
  let p : (Fin n → A) →ₗ[A] (Fin n → A) := LinearMap.id - s ∘ₗ rho R a
  have hpw : ∀ w, p w = w - s (rho R a w) := fun _ ↦ rfl
  have hρp : ∀ v, rho R a (p v) = 0 := by intro v; rw [hpw, map_sub, hs', sub_self]
  have hp : ∀ v, p (p v) = p v := by intro v; rw [hpw (p v), hρp, map_zero, sub_zero]
  have hb : ∀ ω, ∃ b, rho R a b = ω ∧ p b = 0 := fun ω ↦
    ⟨s ω, hs' ω, by rw [hpw, hs', sub_self]⟩
  have hw : ∀ w, rho R a w = 0 → p w = 0 → w = 0 := by
    intro w h1 h2; rwa [hpw, h1, map_zero, sub_zero] at h2
  have : Algebra.Smooth A (Cr p) := smooth_Cr hp
  have : Algebra.Smooth R (Cr p) := Algebra.Smooth.comp R A (Cr p)
  obtain ⟨g, hg1, hgr, hgk⟩ := exists_smul_range_and_smul_ker (RingHom.ker (eps (p := p)))
    (psi R a p) (top_le_range_psi_sup a p hb) (mem_smul_top_of_psi_eq_zero a p hp hw)
  let B := Localization.Away g
  have : Algebra.Smooth (Cr p) B := Algebra.Smooth.of_isLocalization_Away g
  have : Algebra.Smooth A B := Algebra.Smooth.comp A (Cr p) B
  have : Algebra.Smooth R B := Algebra.Smooth.comp R (Cr p) B
  have hepsg : eps (p := p) g = 1 := by
    have := RingHom.mem_ker.mp hg1
    rwa [map_sub, map_one, sub_eq_zero] at this
  refine ⟨B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_,
    ⟨IsLocalization.liftAlgHom (M := Submonoid.powers g) (f := eps) ?_⟩⟩
  · let ψB : (Fin n → B) →ₗ[B] Ω[B⁄R] :=
      Fintype.linearCombination B fun i ↦ D R B (algebraMap (Cr p) B (zz a p i))
    have hbij : Function.Bijective ψB := by
      refine bijective_of_isLocalizedModule g (KaehlerDifferential.map R R (Cr p) B)
        (psi R a p) ψB (fun u ↦ ?_) hgr hgk
      simp [ψB, psi, Fintype.linearCombination_apply, map_sum, algebraMap_smul]
    refine Algebra.IsStandardSmooth.of_basis_kaehlerDifferential
      ((Pi.basisFun B (Fin n)).map (LinearEquiv.ofBijective ψB hbij)) ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨algebraMap (Cr p) B (zz a p i), by simp [ψB]⟩
  · rintro ⟨_, k, rfl⟩
    simp [hepsg]

end Langlands.CommutativeAlgebra.Popescu.StandardSmoothRetract
