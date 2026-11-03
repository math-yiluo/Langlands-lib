import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Commutative algebra for subgroups with the full Lie algebra -/

noncomputable section

open TensorProduct

namespace Langlands.GroupScheme.Lie.SubgroupEquality

section FormallySmooth

variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]

/-- If a surjection onto a formally smooth algebra has kernel inside `m ^ 2`, then the kernel
lies in every power of `m`. -/
theorem ker_le_pow_of_formallySmooth [Algebra.FormallySmooth k B] (π : A →ₐ[k] B)
    (hπ : Function.Surjective π) (m : Ideal A) (h2 : RingHom.ker π ≤ m ^ 2) (N : ℕ) :
    RingHom.ker π ≤ m ^ N := by
  let q : A →+* A ⧸ m ^ N := Ideal.Quotient.mk (m ^ N)
  let T : Ideal (A ⧸ m ^ N) := m.map q
  let J : Ideal (A ⧸ m ^ N) := (RingHom.ker π).map q
  have hTpow : ∀ n, T ^ n = (m ^ n).map q := fun n => (Ideal.map_pow q m n).symm
  have hTN : T ^ N = ⊥ := by rw [hTpow]; exact Ideal.map_quotient_self _
  have hJT : J ≤ T ^ 2 := by rw [hTpow]; exact Ideal.map_mono h2
  have hJT1 : J ≤ T := hJT.trans (Ideal.pow_le_self two_ne_zero)
  have hJ : IsNilpotent J := by
    refine ⟨N, ?_⟩
    have h : J ^ N ≤ T ^ N := Ideal.pow_right_mono hJT1 N
    rw [hTN] at h
    exact le_bot_iff.mp h
  let g : B →ₐ[k] (A ⧸ m ^ N) ⧸ J :=
    AlgHom.liftOfSurjective π hπ
      ((Ideal.Quotient.mkₐ k J).comp (Ideal.Quotient.mkₐ k (m ^ N))) (by
        intro x hx
        rw [RingHom.mem_ker]
        change Ideal.Quotient.mk J (q x) = 0
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem q hx))
  let φ : B →ₐ[k] A ⧸ m ^ N := Algebra.FormallySmooth.lift J hJ g
  have hφ : ∀ a, φ (π a) - q a ∈ J := by
    intro a
    rw [← Ideal.Quotient.eq]
    rw [Algebra.FormallySmooth.mk_lift]
    exact AlgHom.liftOfSurjective_apply π hπ _ _ a
  have hT : ∀ a ∈ m, q a ∈ T := fun a ha => Ideal.mem_map_of_mem q ha
  have hψT : ∀ a ∈ m, φ (π a) ∈ T := by
    intro a ha
    have h := T.add_mem (hJT1 (hφ a)) (hT a ha)
    rwa [sub_add_cancel] at h
  have key : ∀ i : ℕ, ∀ a ∈ m ^ i, φ (π a) - q a ∈ T ^ (i + 1) := by
    intro i
    induction i with
    | zero =>
      intro a _
      exact Ideal.pow_le_pow_right (by norm_num) (hJT (hφ a))
    | succ i ih =>
      intro a ha
      rw [pow_succ] at ha
      refine Submodule.mul_induction_on ha ?_ ?_
      · intro x hx y hy
        have e : φ (π (x * y)) - q (x * y) =
            (φ (π x) - q x) * φ (π y) + q x * (φ (π y) - q y) := by
          rw [map_mul, map_mul, map_mul]; ring
        rw [e]
        refine Ideal.add_mem _ ?_ ?_
        · rw [show i + 1 + 1 = (i + 1) + 1 from rfl, pow_succ]
          exact Ideal.mul_mem_mul (ih x hx) (hψT y hy)
        · rw [show i + 1 + 1 = i + 2 by ring, pow_add]
          refine Ideal.mul_mem_mul ?_ (hJT (hφ y))
          rw [hTpow]
          exact Ideal.mem_map_of_mem q hx
      · intro x y hx hy
        have e : φ (π (x + y)) - q (x + y) = (φ (π x) - q x) + (φ (π y) - q y) := by
          rw [map_add, map_add, map_add]; ring
        rw [e]
        exact Ideal.add_mem _ hx hy
  have step : ∀ n, n ≤ N → RingHom.ker π ≤ m ^ n := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn x hx
      have hxn : x ∈ m ^ n := ih (Nat.le_of_succ_le hn) hx
      have h := key n x hxn
      have hx0 : π x = 0 := hx
      rw [hx0, map_zero, zero_sub, Ideal.neg_mem_iff, hTpow] at h
      have h' := Ideal.mem_quotient_iff_mem_sup.mp h
      rwa [sup_eq_left.mpr (Ideal.pow_le_pow_right hn)] at h'
  exact step N le_rfl

end FormallySmooth

section Krull

variable {A : Type*} [CommRing A]

/-- **Krull's intersection theorem**, uniform version: an ideal inside every power of `m` in a
Noetherian ring is fixed by multiplication by one element of `m`. -/
theorem exists_mem_mul_eq_self_of_le_pow [IsNoetherianRing A] (m I : Ideal A)
    (h : ∀ N : ℕ, I ≤ m ^ N) : ∃ r ∈ m, ∀ x ∈ I, r * x = x := by
  let P : Submodule A A := ⨅ i : ℕ, m ^ i • ⊤
  have hP : ∀ i, (m.stableFiltration ⊤ ⊓ m.trivialFiltration P).N i = P :=
    fun i => inf_eq_right.mpr ((iInf_le _ i).trans <| le_of_eq <| by simp)
  obtain ⟨r, hr, hr'⟩ :=
    Submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul m P (IsNoetherian.noetherian P) (by
      obtain ⟨i, hi⟩ := (m.stableFiltration_stable ⊤).inter_right (m.trivialFiltration P)
      have := hi i (le_refl _)
      rw [hP, hP] at this
      exact le_of_eq this.symm)
  refine ⟨r, hr, fun x hx => hr' x ?_⟩
  rw [Submodule.mem_iInf]
  intro i
  have hx' := h i hx
  simpa [smul_eq_mul, Ideal.mul_top] using hx'

end Krull

section Connected

variable {A : Type*} [CommRing A]

/-- Over a ring with preconnected prime spectrum every idempotent is `0` or `1`. -/
theorem isIdempotentElem_eq_zero_or_one [PreconnectedSpace (PrimeSpectrum A)] {e : A}
    (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have nil : ∀ f : A, IsIdempotentElem f → PrimeSpectrum.basicOpen f = ⊥ → f = 0 := by
    intro f hf hb
    obtain ⟨n, hn⟩ := (PrimeSpectrum.basicOpen_eq_bot_iff f).mp hb
    rw [← hf.pow_succ_eq n, pow_succ, hn, zero_mul]
  have hc : IsClopen (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum A)) :=
    PrimeSpectrum.isClopen_iff.mpr ⟨e, he, rfl⟩
  rcases isClopen_iff.mp hc with h | h
  · exact Or.inl (nil e he (TopologicalSpace.Opens.coe_eq_empty.mp h))
  · right
    have htop : PrimeSpectrum.basicOpen e = ⊤ := TopologicalSpace.Opens.coe_eq_univ.mp h
    have h0 : PrimeSpectrum.basicOpen (1 - e) = ⊥ := by
      have hm : PrimeSpectrum.basicOpen ((1 - e) * e) = ⊥ := by
        rw [he.one_sub_mul_self, PrimeSpectrum.basicOpen_zero]
      rwa [PrimeSpectrum.basicOpen_mul, htop, inf_top_eq] at hm
    have := nil (1 - e) he.one_sub h0
    exact (sub_eq_zero.mp this).symm

/-- If `t` kills a proper ideal `I` and `1 - t ∈ I`, then `I = 0`, provided the prime spectrum
is preconnected. -/
theorem eq_bot_of_mul_eq_zero_of_one_sub_mem [PreconnectedSpace (PrimeSpectrum A)]
    (I : Ideal A) (hI : I ≠ ⊤) (t : A) (ht : ∀ x ∈ I, t * x = 0) (ht1 : 1 - t ∈ I) :
    I = ⊥ := by
  have he : IsIdempotentElem (1 - t) := by
    have h : t * (1 - t) = 0 := ht _ ht1
    unfold IsIdempotentElem
    linear_combination (-1 : A) * h
  rcases isIdempotentElem_eq_zero_or_one he with h | h
  · have t1 : t = 1 := (sub_eq_zero.mp h).symm
    rw [eq_bot_iff]
    intro x hx
    have := ht x hx
    rw [t1, one_mul] at this
    exact (Submodule.mem_bot A).mpr this
  · exact absurd (Ideal.eq_top_of_isUnit_mem I ht1 (by rw [h]; exact isUnit_one)) hI

end Connected

section Derivation

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]

/-- An element of the augmentation ideal outside its square is detected by a linear form
satisfying the Leibniz rule at the augmentation. -/
theorem exists_leibniz_ne_zero (ε : A →ₐ[k] k) {x : A} (hx : x ∈ RingHom.ker ε)
    (hx2 : x ∉ RingHom.ker ε ^ 2) :
    ∃ f : A →ₗ[k] k, f x ≠ 0 ∧ ∀ a b, f (a * b) = ε a * f b + ε b * f a := by
  let m : Ideal A := RingHom.ker ε
  let p : Submodule k A := (m ^ 2).restrictScalars k ⊔ k ∙ (1 : A)
  have hm2 : ∀ y ∈ m ^ 2, ε y = 0 := fun y hy => Ideal.pow_le_self two_ne_zero hy
  have hxp : x ∉ p := by
    intro hxp
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hxp
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
    have hc : c = 0 := by
      have h := congrArg ε hyz
      rw [map_add, hm2 y hy, map_smul, map_one, smul_eq_mul, mul_one, zero_add] at h
      rw [h]; exact hx
    rw [hc, zero_smul, add_zero] at hyz
    exact hx2 (hyz ▸ hy)
  obtain ⟨f, hfx, hfp⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hxp inferInstance
  have hf : ∀ y ∈ p, f y = 0 := fun y hy => by
    have : f y ∈ p.map f := Submodule.mem_map_of_mem hy
    rw [hfp] at this
    exact (Submodule.mem_bot k).mp this
  have hf1 : f 1 = 0 := hf 1 (Submodule.mem_sup_right (Submodule.mem_span_singleton_self 1))
  have hfm2 : ∀ y ∈ m ^ 2, f y = 0 := fun y hy => hf y (Submodule.mem_sup_left hy)
  refine ⟨f, hfx, fun a b => ?_⟩
  have ha : a - algebraMap k A (ε a) ∈ m := by
    change ε (a - algebraMap k A (ε a)) = 0
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  have hb : b - algebraMap k A (ε b) ∈ m := by
    change ε (b - algebraMap k A (ε b)) = 0
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  have hab : (a - algebraMap k A (ε a)) * (b - algebraMap k A (ε b)) ∈ m ^ 2 := by
    rw [pow_two]; exact Ideal.mul_mem_mul ha hb
  have e : a * b = (a - algebraMap k A (ε a)) * (b - algebraMap k A (ε b)) +
      ε a • b + ε b • a - (ε a * ε b) • (1 : A) := by
    simp only [Algebra.smul_def, map_mul]; ring
  rw [e, map_sub, map_add, map_add, hfm2 _ hab, map_smul, map_smul, map_smul, hf1,
    smul_eq_mul, smul_eq_mul, smul_eq_mul]
  ring

end Derivation

section Annihilator

variable {F A B : Type*} [Field F] [CommRing A] [CommRing B] [Algebra F A] [Algebra F B]

/-- Let `φ : A → B` be a surjection of `F`-algebras with `A` Noetherian and `B` formally smooth,
and `ε` an augmentation of `A` vanishing on `ker φ`. If every linear form satisfying the Leibniz
rule at `ε` vanishes on `ker φ`, then some `f` with `ε f = 1` annihilates `ker φ`. -/
theorem exists_annihilator_of_derivations [IsNoetherianRing A] [Algebra.FormallySmooth F B]
    (φ : A →ₐ[F] B) (hφ : Function.Surjective φ) (ε : A →ₐ[F] F)
    (hε : RingHom.ker φ ≤ RingHom.ker ε)
    (hder : ∀ δ : A →ₗ[F] F, (∀ a b, δ (a * b) = ε a * δ b + ε b * δ a) →
      ∀ x ∈ RingHom.ker φ, δ x = 0) :
    ∃ f : A, ε f = 1 ∧ ∀ x ∈ RingHom.ker φ, f * x = 0 := by
  have h2 : RingHom.ker φ ≤ RingHom.ker ε ^ 2 := by
    intro x hx
    by_contra hx2
    obtain ⟨δ, hδx, hδ⟩ := exists_leibniz_ne_zero ε (hε hx) hx2
    exact hδx (hder δ hδ x hx)
  obtain ⟨r, hr, hrx⟩ := exists_mem_mul_eq_self_of_le_pow (RingHom.ker ε) (RingHom.ker φ)
    (ker_le_pow_of_formallySmooth φ hφ _ h2)
  refine ⟨1 - r, ?_, fun x hx => ?_⟩
  · rw [map_sub, map_one, RingHom.mem_ker.mp hr, sub_zero]
  · rw [sub_mul, one_mul, hrx x hx, sub_self]

end Annihilator

section TensorProduct

variable {k A B C : Type*} [Field k] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]

/-- If left multiplication by `I ⊗ 1` kills `c ∈ A ⊗ B`, then every product map sends `c` into
the image of the annihilator of `I`. -/
theorem productMap_mem_map_annihilator (I : Ideal A) (c : A ⊗[k] B)
    (hc : ∀ x ∈ I, (x ⊗ₜ[k] (1 : B)) * c = 0) (φ : A →ₐ[k] C) (g : B →ₐ[k] C) :
    Algebra.TensorProduct.productMap φ g c ∈ (Submodule.annihilator I).map φ := by
  classical
  let b := Module.Basis.ofVectorSpace k B
  let E := TensorProduct.equivFinsuppOfBasisRight (M := A) b
  have hE : ∀ x : A, ∀ d : A ⊗[k] B, E ((x ⊗ₜ[k] (1 : B)) * d) = Finsupp.mapRange (x * ·)
      (mul_zero x) (E d) := by
    intro x d
    induction d using TensorProduct.inductionOn with
    | tmul a n =>
      ext i
      simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, E,
        TensorProduct.equivFinsuppOfBasisRight_apply_tmul, Finsupp.mapRange_apply]
      rw [mul_smul_comm]
    | add d d' hd hd' =>
      rw [mul_add, map_add, map_add, hd, hd']
      ext i
      simp [mul_add]
  have hann : ∀ i, E c i ∈ Submodule.annihilator I := by
    intro i
    rw [Submodule.mem_annihilator]
    intro x hx
    have h := congrArg (fun f => f i) (hE x c)
    simp only [hc x hx, map_zero, Finsupp.coe_zero, Pi.zero_apply,
      Finsupp.mapRange_apply] at h
    rw [smul_eq_mul, mul_comm]
    exact h.symm
  have hcsum : c = (E c).sum fun i a => a ⊗ₜ[k] b i := by
    rw [← TensorProduct.equivFinsuppOfBasisRight_symm_apply, LinearEquiv.symm_apply_apply]
  rw [hcsum, map_finsuppSum]
  refine Ideal.sum_mem _ fun i _ => ?_
  dsimp only
  rw [Algebra.TensorProduct.productMap_apply_tmul]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem φ (hann i))

end TensorProduct

end Langlands.GroupScheme.Lie.SubgroupEquality
