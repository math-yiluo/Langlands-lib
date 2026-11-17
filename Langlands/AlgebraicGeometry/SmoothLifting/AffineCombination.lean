import Mathlib

/-! # Affine combinations of ring maps into square-zero extensions

Let `J` be an ideal of a commutative ring `R` with `J * J = 0`. Ring maps `B →+* R` that agree
modulo `J` can be combined affinely: `φ₀ + ∑ cₖ (φₖ - φ₀)` is again a ring map. This file proves
that fact together with two localization lemmas for algebra maps out of finitely generated and
finitely presented algebras, used for the infinitesimal lifting property of smooth morphisms.
-/

noncomputable section

open scoped BigOperators

namespace Langlands.AlgebraicGeometry.SmoothLifting

section AffComb

variable {B R : Type*} [CommRing B] [CommRing R]

/-- An ideal with vanishing products of any two of its elements. -/
def SqZero (J : Ideal R) : Prop := ∀ a ∈ J, ∀ b ∈ J, a * b = 0

theorem SqZero.map {R' : Type*} [CommRing R'] {J : Ideal R} (hJ : SqZero J) (ρ : R →+* R') :
    SqZero (J.map ρ) := by
  have h : J * J = ⊥ := by
    refine le_bot_iff.mp (Submodule.mul_le.mpr fun a ha b hb => ?_)
    rw [hJ a ha b hb]; exact Submodule.zero_mem _
  intro a ha b hb
  have hab : a * b ∈ J.map ρ * J.map ρ := Ideal.mul_mem_mul ha hb
  rw [← Ideal.map_mul, h, Ideal.map_bot] at hab
  exact (Submodule.mem_bot _).mp hab

/-- The affine combination `φ₀ + ∑ cₖ (φₖ - φ₀)` of ring maps agreeing modulo a square-zero
ideal, as a ring map. -/
def affComb {ι : Type*} [Fintype ι] (J : Ideal R) (hJ : SqZero J) (φ₀ : B →+* R)
    (φ : ι → B →+* R) (hφ : ∀ k b, φ k b - φ₀ b ∈ J) (c : ι → R) : B →+* R where
  toFun b := φ₀ b + ∑ k, c k * (φ k b - φ₀ b)
  map_one' := by simp
  map_zero' := by simp
  map_add' a b := by
    simp only [map_add]
    rw [show (∑ k, c k * (φ k a + φ k b - (φ₀ a + φ₀ b))) =
        ∑ k, c k * (φ k a - φ₀ a) + ∑ k, c k * (φ k b - φ₀ b) by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun k _ => by ring]
    ring
  map_mul' a b := by
    have h1 : ∀ k, φ k (a * b) - φ₀ (a * b) =
        φ₀ a * (φ k b - φ₀ b) + φ₀ b * (φ k a - φ₀ a) := fun k => by
      have := hJ _ (hφ k a) _ (hφ k b)
      simp only [map_mul]
      linear_combination this
    have hA : ∑ k, c k * (φ k a - φ₀ a) ∈ J := J.sum_mem fun k _ => J.mul_mem_left _ (hφ k a)
    have hB : ∑ k, c k * (φ k b - φ₀ b) ∈ J := J.sum_mem fun k _ => J.mul_mem_left _ (hφ k b)
    have h0 := hJ _ hA _ hB
    have h2 : ∑ k, c k * (φ k (a * b) - φ₀ (a * b)) =
        φ₀ a * ∑ k, c k * (φ k b - φ₀ b) + φ₀ b * ∑ k, c k * (φ k a - φ₀ a) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by rw [h1 k]; ring
    show φ₀ (a * b) + ∑ k, c k * (φ k (a * b) - φ₀ (a * b)) =
      (φ₀ a + ∑ k, c k * (φ k a - φ₀ a)) * (φ₀ b + ∑ k, c k * (φ k b - φ₀ b))
    rw [h2, map_mul]
    linear_combination (-1 : R) * h0

theorem affComb_apply {ι : Type*} [Fintype ι] (J : Ideal R) (hJ : SqZero J) (φ₀ : B →+* R)
    (φ : ι → B →+* R) (hφ : ∀ k b, φ k b - φ₀ b ∈ J) (c : ι → R) (b : B) :
    affComb J hJ φ₀ φ hφ c b = φ₀ b + ∑ k, c k * (φ k b - φ₀ b) := rfl

theorem affComb_sub_mem {ι : Type*} [Fintype ι] (J : Ideal R) (hJ : SqZero J) (φ₀ : B →+* R)
    (φ : ι → B →+* R) (hφ : ∀ k b, φ k b - φ₀ b ∈ J) (c : ι → R) (b : B) :
    affComb J hJ φ₀ φ hφ c b - φ₀ b ∈ J := by
  rw [affComb_apply, add_sub_cancel_left]
  exact J.sum_mem fun k _ => J.mul_mem_left _ (hφ k b)

/-- The algebra-map version of `affComb`. -/
def affCombₐ {A : Type*} [CommRing A] [Algebra A B] [Algebra A R] {ι : Type*} [Fintype ι]
    (J : Ideal R) (hJ : SqZero J) (φ₀ : B →ₐ[A] R) (φ : ι → B →ₐ[A] R)
    (hφ : ∀ k b, φ k b - φ₀ b ∈ J) (c : ι → R) : B →ₐ[A] R :=
  { affComb J hJ φ₀.toRingHom (fun k => (φ k).toRingHom) hφ c with
    commutes' a := by
      change φ₀ (algebraMap A B a) + ∑ k, c k * (φ k (algebraMap A B a) - φ₀ (algebraMap A B a))
        = algebraMap A R a
      simp }

theorem affCombₐ_apply {A : Type*} [CommRing A] [Algebra A B] [Algebra A R] {ι : Type*}
    [Fintype ι] (J : Ideal R) (hJ : SqZero J) (φ₀ : B →ₐ[A] R) (φ : ι → B →ₐ[A] R)
    (hφ : ∀ k b, φ k b - φ₀ b ∈ J) (c : ι → R) (b : B) :
    affCombₐ J hJ φ₀ φ hφ c b = φ₀ b + ∑ k, c k * (φ k b - φ₀ b) := rfl

/-- The binary affine combination `φ₀ + c (φ₁ - φ₀)`. -/
def affComb₂ₐ {A : Type*} [CommRing A] [Algebra A B] [Algebra A R]
    (J : Ideal R) (hJ : SqZero J) (φ₀ φ₁ : B →ₐ[A] R) (hφ : ∀ b, φ₁ b - φ₀ b ∈ J) (c : R) :
    B →ₐ[A] R :=
  affCombₐ J hJ φ₀ (fun _ : Unit => φ₁) (fun _ => hφ) (fun _ => c)

theorem affComb₂ₐ_apply {A : Type*} [CommRing A] [Algebra A B] [Algebra A R]
    (J : Ideal R) (hJ : SqZero J) (φ₀ φ₁ : B →ₐ[A] R) (hφ : ∀ b, φ₁ b - φ₀ b ∈ J) (c : R)
    (b : B) : affComb₂ₐ J hJ φ₀ φ₁ hφ c b = φ₀ b + c * (φ₁ b - φ₀ b) := by
  simp [affComb₂ₐ, affCombₐ_apply]

end AffComb

section Torsion

/-- Two algebra maps out of a finitely generated algebra which agree after a ring map whose
kernel is `g`-power torsion differ by `g`-power torsion, uniformly. -/
theorem exists_pow_mul_sub_eq_zero {A B R R' : Type*} [CommRing A] [CommRing B] [CommRing R]
    [CommRing R'] [Algebra A B] [Algebra A R] [Algebra.FiniteType A B]
    (L L' : B →ₐ[A] R) (ρ : R →+* R') (g : R) (hρ : ∀ r, ρ r = 0 → ∃ m : ℕ, g ^ m * r = 0)
    (h : ∀ b, ρ (L b) = ρ (L' b)) : ∃ M : ℕ, ∀ b, g ^ M * (L b - L' b) = 0 := by
  classical
  obtain ⟨t, ht⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra A B).FG)
  have hm : ∀ b, ∃ m : ℕ, g ^ m * (L b - L' b) = 0 := fun b =>
    hρ _ (by rw [map_sub, h, sub_self])
  choose m hm using hm
  refine ⟨t.sup m, fun b => ?_⟩
  let T : Subalgebra A B :=
    { carrier := {b | g ^ t.sup m * (L b - L' b) = 0}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq, map_mul] at ha hb ⊢
        linear_combination L a * hb + L' b * ha
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq, map_add] at ha hb ⊢
        linear_combination ha + hb
      algebraMap_mem' := by
        intro a
        simp only [Set.mem_ofPred_eq, AlgHom.commutes, sub_self, mul_zero] }
  have hT : Algebra.adjoin A (t : Set B) ≤ T := by
    refine Algebra.adjoin_le fun b hb => ?_
    change g ^ t.sup m * (L b - L' b) = 0
    rw [← Nat.sub_add_cancel (Finset.le_sup (f := m) hb), pow_add, mul_assoc, hm b, mul_zero]
  have hb : b ∈ T := hT (ht.symm ▸ Algebra.mem_top)
  exact hb

end Torsion

section Extension

variable {A B R R' : Type*} [CommRing A] [CommRing B] [CommRing R] [CommRing R']
  [Algebra A B] [Algebra A R] [Algebra A R']

/-- **Extension of a localized first-order deformation.** Let `B` be a finitely presented
`A`-algebra, `J` a square-zero ideal of `R`, and `ρ : R → R'` an `A`-algebra map behaving like a
localization at `g` (its kernel is `g`-power torsion, and every element of `J R'` becomes the image
of an element of `J` after multiplication by a power of `ρ g`). If `β : B → R` and `β' : B → R'`
agree modulo `J R'` after `ρ`, then for all large `N` there is `γ : B → R`, congruent to `β`
modulo `J`, with `ρ ∘ γ = ρ ∘ β + (ρ g)^N (β' - ρ ∘ β)`. -/
theorem exists_extension [Algebra.FinitePresentation A B] (J : Ideal R) (hJ : SqZero J)
    (ρ : R →ₐ[A] R') (g : R)
    (h1 : ∀ r, ρ r = 0 → ∃ m : ℕ, g ^ m * r = 0)
    (h2 : ∀ r' ∈ J.map ρ, ∃ (n : ℕ) (e : R), e ∈ J ∧ ρ g ^ n * r' = ρ e)
    (β : B →ₐ[A] R) (β' : B →ₐ[A] R') (hβ : ∀ b, β' b - ρ (β b) ∈ J.map ρ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∃ γ : B →ₐ[A] R, (∀ b, γ b - β b ∈ J) ∧
      ∀ b, ρ (γ b) = ρ (β b) + ρ g ^ N * (β' b - ρ (β b)) := by
  classical
  obtain ⟨r, π, hπ, T, hT⟩ := (Algebra.FinitePresentation.out : ∃ (n : ℕ)
    (f : MvPolynomial (Fin n) A →ₐ[A] B), Function.Surjective f ∧ (RingHom.ker f.toRingHom).FG)
  have hJ' : SqZero (J.map ρ) := hJ.map ρ.toRingHom
  let b : Fin r → R := fun l => β (π (MvPolynomial.X l))
  let δ : Fin r → R' := fun l => β' (π (MvPolynomial.X l)) - ρ (b l)
  have hδ : ∀ l, ∃ (n : ℕ) (e : R), e ∈ J ∧ ρ g ^ n * δ l = ρ e := fun l => h2 _ (hβ _)
  choose n e he hne using hδ
  let n₀ := Finset.univ.sup n
  let e' : Fin r → R := fun l => g ^ (n₀ - n l) * e l
  have he' : ∀ l, e' l ∈ J := fun l => J.mul_mem_left _ (he l)
  have hne' : ∀ l, ρ (e' l) = ρ g ^ n₀ * δ l := fun l => by
    have hl : n₀ - n l + n l = n₀ := Nat.sub_add_cancel (Finset.le_sup (Finset.mem_univ l))
    simp only [e', map_mul, map_pow, ← hne l]
    rw [← mul_assoc, ← pow_add, hl]
  let γt : ℕ → MvPolynomial (Fin r) A →ₐ[A] R := fun j =>
    MvPolynomial.aeval fun l => b l + g ^ j * e' l
  let βπ : MvPolynomial (Fin r) A →ₐ[A] R := β.comp π
  let β'π : MvPolynomial (Fin r) A →ₐ[A] R' := β'.comp π
  -- `γt j` is congruent to `β ∘ π` modulo `J`
  have hmodJ : ∀ j p, γt j p - βπ p ∈ J := by
    intro j p
    rw [← Ideal.Quotient.eq]
    have : (Ideal.Quotient.mkₐ A J).comp (γt j) = (Ideal.Quotient.mkₐ A J).comp βπ := by
      refine MvPolynomial.algHom_ext fun l => ?_
      simp only [AlgHom.comp_apply, γt, βπ, MvPolynomial.aeval_X, Ideal.Quotient.mkₐ_eq_mk,
        map_add, map_mul]
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (he' l), mul_zero, add_zero]
    exact congrArg (fun F : MvPolynomial (Fin r) A →ₐ[A] R ⧸ J => F p) this
  have hmodJ' : ∀ p, β'π p - (ρ.comp βπ) p ∈ J.map ρ := fun p => hβ _
  -- identity 1: `ρ ∘ γt j = ρ ∘ βπ + (ρ g)^(n₀+j) (β'π - ρ ∘ βπ)`
  have hid1 : ∀ j p, ρ (γt j p) = ρ (βπ p) + ρ g ^ (n₀ + j) * (β'π p - ρ (βπ p)) := by
    intro j p
    have : ρ.comp (γt j) = affComb₂ₐ (J.map ρ) hJ' (ρ.comp βπ) β'π hmodJ' (ρ g ^ (n₀ + j)) := by
      refine MvPolynomial.algHom_ext fun l => ?_
      rw [affComb₂ₐ_apply]
      simp only [AlgHom.comp_apply, γt, MvPolynomial.aeval_X, map_add, map_mul, map_pow, hne']
      simp only [βπ, β'π, AlgHom.comp_apply, δ, b]
      ring
    have h := congrArg (fun F : MvPolynomial (Fin r) A →ₐ[A] R' => F p) this
    rw [affComb₂ₐ_apply] at h
    simpa only [AlgHom.comp_apply] using h
  -- identity 2: `γt j = βπ + g^j (γt 0 - βπ)`
  have hid2 : ∀ j p, γt j p = βπ p + g ^ j * (γt 0 p - βπ p) := by
    intro j p
    have : γt j = affComb₂ₐ J hJ βπ (γt 0) (hmodJ 0) (g ^ j) := by
      refine MvPolynomial.algHom_ext fun l => ?_
      rw [affComb₂ₐ_apply]
      simp only [γt, βπ, MvPolynomial.aeval_X, AlgHom.comp_apply, b, pow_zero, one_mul]
      ring
    have h := congrArg (fun F : MvPolynomial (Fin r) A →ₐ[A] R => F p) this
    simp only [affComb₂ₐ_apply] at h
    exact h
  -- the relations are killed by `γt 0` up to a power of `g`
  have hker : ∀ p ∈ RingHom.ker π.toRingHom, ∃ m : ℕ, g ^ m * γt 0 p = 0 := by
    intro p hp
    have hp' : π p = 0 := hp
    refine h1 _ ?_
    rw [hid1, show βπ p = 0 by simp [βπ, hp'], show β'π p = 0 by simp [β'π, hp']]
    simp
  choose! m hm using hker
  have hTsub : ∀ p ∈ T, p ∈ RingHom.ker π.toRingHom := fun p hp => hT ▸ Ideal.subset_span hp
  refine ⟨n₀ + T.sup m, fun N hN => ?_⟩
  set j := N - n₀ with hj
  have hjN : n₀ + j = N := by omega
  have hjm : T.sup m ≤ j := by omega
  have hkill : RingHom.ker π.toRingHom ≤ RingHom.ker (γt j).toRingHom := by
    rw [← hT, Ideal.span_le]
    intro p hp
    have hp0 : βπ p = 0 := by
      have : π p = 0 := hTsub p hp
      simp [βπ, this]
    change γt j p = 0
    rw [hid2, hp0, sub_zero, zero_add,
      ← Nat.sub_add_cancel ((Finset.le_sup (f := m) hp).trans hjm), pow_add, mul_assoc,
      hm p (hTsub p hp), mul_zero]
  refine ⟨AlgHom.liftOfSurjective π hπ (γt j) hkill, fun x => ?_, fun x => ?_⟩
  · obtain ⟨p, rfl⟩ := hπ x
    rw [AlgHom.liftOfSurjective_apply]
    exact hmodJ j p
  · obtain ⟨p, rfl⟩ := hπ x
    rw [AlgHom.liftOfSurjective_apply, hid1, hjN]
    rfl

end Extension

section FibreRing

variable {R : Type*} [CommRing R]

/-- The ring of tuples `(a₀, (aₖ)ₖ)` with every `aₖ - a₀` in `J`. -/
def fibreRing (ι : Type*) (J : Ideal R) : Subring (R × (ι → R)) where
  carrier := {a | ∀ k, a.2 k - a.1 ∈ J}
  mul_mem' {a b} ha hb k := by
    have : (a * b).2 k - (a * b).1 = a.2 k * (b.2 k - b.1) + (a.2 k - a.1) * b.1 := by
      simp only [Prod.snd_mul, Prod.fst_mul, Pi.mul_apply]; ring
    rw [this]; exact J.add_mem (J.mul_mem_left _ (hb k)) (J.mul_mem_right _ (ha k))
  one_mem' k := by simp
  add_mem' {a b} ha hb k := by
    have : (a + b).2 k - (a + b).1 = (a.2 k - a.1) + (b.2 k - b.1) := by
      simp only [Prod.snd_add, Prod.fst_add, Pi.add_apply]; ring
    rw [this]; exact J.add_mem (ha k) (hb k)
  zero_mem' k := by simp
  neg_mem' {a} ha k := by
    have : (-a).2 k - (-a).1 = -(a.2 k - a.1) := by
      simp only [Prod.snd_neg, Prod.fst_neg, Pi.neg_apply]; ring
    rw [this]; exact J.neg_mem (ha k)

variable {ι : Type*} (J : Ideal R)

/-- The base coordinate of the fibre ring. -/
def fibreFst : fibreRing ι J →+* R := (RingHom.fst R (ι → R)).comp (fibreRing ι J).subtype

/-- The `k`-th coordinate of the fibre ring. -/
def fibreEval (k : ι) : fibreRing ι J →+* R :=
  (Pi.evalRingHom (fun _ => R) k).comp ((RingHom.snd R (ι → R)).comp (fibreRing ι J).subtype)

@[simp] theorem fibreFst_apply (a : fibreRing ι J) : fibreFst J a = (a : R × (ι → R)).1 := rfl
@[simp] theorem fibreEval_apply (k : ι) (a : fibreRing ι J) :
    fibreEval J k a = (a : R × (ι → R)).2 k := rfl

theorem fibreEval_sub_mem (k : ι) (a : fibreRing ι J) : fibreEval J k a - fibreFst J a ∈ J :=
  a.2 k

/-- Ring maps into the fibre ring are determined by their coordinates. -/
theorem fibreRing_hom_ext {B : Type*} [CommRing B] {Φ Ψ : B →+* fibreRing ι J}
    (h₀ : (fibreFst J).comp Φ = (fibreFst J).comp Ψ)
    (h : ∀ k, (fibreEval J k).comp Φ = (fibreEval J k).comp Ψ) : Φ = Ψ := by
  ext b
  · exact congrArg (fun F : B →+* R => F b) h₀
  · exact congrArg (fun F : B →+* R => F b) (h _)

/-- The tuple map into the fibre ring. -/
def fibreLift {B : Type*} [CommRing B] (φ₀ : B →+* R) (φ : ι → B →+* R)
    (hφ : ∀ k b, φ k b - φ₀ b ∈ J) : B →+* fibreRing ι J :=
  ((RingHom.prod φ₀ (RingHom.pi φ))).codRestrict (fibreRing ι J) fun b k => hφ k b

@[simp] theorem fibreFst_comp_fibreLift {B : Type*} [CommRing B] (φ₀ : B →+* R)
    (φ : ι → B →+* R) (hφ : ∀ k b, φ k b - φ₀ b ∈ J) :
    (fibreFst J).comp (fibreLift J φ₀ φ hφ) = φ₀ := rfl

@[simp] theorem fibreEval_comp_fibreLift {B : Type*} [CommRing B] (φ₀ : B →+* R)
    (φ : ι → B →+* R) (hφ : ∀ k b, φ k b - φ₀ b ∈ J) (k : ι) :
    (fibreEval J k).comp (fibreLift J φ₀ φ hφ) = φ k := rfl

/-- The affine combination map on the fibre ring. -/
def fibreComb [Fintype ι] (hJ : SqZero J) (c : ι → R) : fibreRing ι J →+* R :=
  affComb J hJ (fibreFst J) (fun k => fibreEval J k) (fun k a => fibreEval_sub_mem J k a) c

theorem fibreComb_comp_fibreLift [Fintype ι] (hJ : SqZero J) (c : ι → R) {B : Type*}
    [CommRing B] (φ₀ : B →+* R) (φ : ι → B →+* R) (hφ : ∀ k b, φ k b - φ₀ b ∈ J) :
    (fibreComb J hJ c).comp (fibreLift J φ₀ φ hφ) = affComb J hJ φ₀ φ hφ c := rfl

end FibreRing

section Localization

variable {C Rc Rce : Type*} [CommRing C] [CommRing Rc] [CommRing Rce] [Algebra C Rc]
  [Algebra C Rce]

theorem isUnit_algebraMap_left_of_away (c e : C) [IsLocalization.Away (c * e) Rce] :
    IsUnit (algebraMap C Rce c) :=
  isUnit_of_mul_isUnit_left (by
    rw [← map_mul]; exact IsLocalization.Away.algebraMap_isUnit (c * e))

/-- The kernel of the restriction map `C[1/c] → C[1/(c e)]` is `e`-power torsion. -/
theorem away_ker_torsion (c e : C) [IsLocalization.Away c Rc] [IsLocalization.Away (c * e) Rce]
    (ρ : Rc →ₐ[C] Rce) (r : Rc) (hr : ρ r = 0) :
    ∃ m : ℕ, algebraMap C Rc e ^ m * r = 0 := by
  obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.surj (Submonoid.powers c) r
  have hx : algebraMap C Rce x = 0 := by
    have := congrArg ρ hxs
    rw [map_mul, hr, zero_mul, AlgHom.commutes] at this
    exact this.symm
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (c * e)) Rce x).mp hx
  refine ⟨k, ?_⟩
  have hs : IsUnit (algebraMap C Rc s) := IsLocalization.map_units Rc s
  have hc : IsUnit (algebraMap C Rc (c ^ k)) := by
    rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit c).pow k
  have h0 : algebraMap C Rc (e ^ k * x) = 0 := by
    refine (hc.mul_right_eq_zero).mp ?_
    rw [← map_mul, show c ^ k * (e ^ k * x) = (c * e) ^ k * x by ring]
    simp only at hk
    rw [hk, map_zero]
  refine (hs.mul_left_eq_zero).mp ?_
  rw [mul_assoc, hxs, ← map_pow, ← map_mul, h0]

/-- Elements of `I C[1/(c e)]` become images of elements of `I C[1/c]` after multiplication
by a power of `e`. -/
theorem away_map_surj (c e : C) [IsLocalization.Away c Rc] [IsLocalization.Away (c * e) Rce]
    (I : Ideal C) (ρ : Rc →ₐ[C] Rce) (r' : Rce)
    (hr' : r' ∈ (I.map (algebraMap C Rc)).map ρ) :
    ∃ (n : ℕ) (y : Rc), y ∈ I.map (algebraMap C Rc) ∧ ρ (algebraMap C Rc e) ^ n * r' = ρ y := by
  have hmap : (I.map (algebraMap C Rc)).map ρ = I.map (algebraMap C Rce) := by
    rw [show Ideal.map ρ (Ideal.map (algebraMap C Rc) I) =
      Ideal.map (ρ : Rc →+* Rce) (Ideal.map (algebraMap C Rc) I) from rfl, Ideal.map_map,
      ρ.comp_algebraMap]
  rw [hmap] at hr'
  obtain ⟨⟨⟨x, hx⟩, ⟨_, k, rfl⟩⟩, hxk⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers (c * e)) Rce).mp hr'
  simp only at hxk
  refine ⟨k, IsLocalization.mk' Rc x (⟨c ^ k, k, rfl⟩ : Submonoid.powers c), ?_, ?_⟩
  · rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hx)
  · have hc : IsUnit (algebraMap C Rce (c ^ k)) := by
      rw [map_pow]; exact (isUnit_algebraMap_left_of_away c e).pow k
    refine (hc.mul_left_inj).mp ?_
    rw [AlgHom.commutes, mul_assoc, mul_comm r', ← mul_assoc, ← map_pow, ← map_mul,
      mul_comm (e ^ k), ← mul_pow, mul_comm _ r', hxk]
    have := congrArg ρ (IsLocalization.mk'_spec Rc x (⟨c ^ k, k, rfl⟩ : Submonoid.powers c))
    rw [map_mul, AlgHom.commutes, AlgHom.commutes] at this
    exact this.symm

end Localization

end Langlands.AlgebraicGeometry.SmoothLifting
