import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-! # Descent of a split finite étale affine-space algebra -/

open scoped TensorProduct

namespace Langlands.Algebra

universe u v w

/-- A multivariate polynomial over a finite product is a tuple of polynomials
over its factors. -/
private noncomputable def mvPolynomialPiRingEquiv (σ : Type w) {ι : Type u} [Finite ι]
    (B : ι → Type v) [∀ i, CommRing (B i)] :
    MvPolynomial σ (∀ i, B i) ≃+* ∀ i, MvPolynomial σ (B i) := by
  classical
  let f : MvPolynomial σ (∀ i, B i) →+* ∀ i, MvPolynomial σ (B i) :=
    RingHom.pi (fun i => MvPolynomial.map (Pi.evalRingHom B i))
  refine RingEquiv.ofBijective f ⟨?_, ?_⟩
  · intro p q h
    apply MvPolynomial.ext
    intro d
    funext i
    have hi := congrArg (fun x : ∀ i, MvPolynomial σ (B i) => (x i).coeff d) h
    change (MvPolynomial.map (Pi.evalRingHom B i) p).coeff d =
      (MvPolynomial.map (Pi.evalRingHom B i) q).coeff d at hi
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_map] at hi
    exact hi
  · intro p
    let := Fintype.ofFinite ι
    let s := Finset.univ.biUnion (fun i => (p i).support)
    have hs (d : σ →₀ ℕ) (hd : (fun i => (p i).coeff d) ≠ 0) : d ∈ s := by
      by_contra h
      apply hd
      funext i
      change (p i).coeff d = 0
      by_contra hi
      exact h (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, MvPolynomial.mem_support_iff.mpr hi⟩)
    let q : MvPolynomial σ (∀ i, B i) :=
      AddMonoidAlgebra.ofCoeff (Finsupp.onFinset s (fun d i => (p i).coeff d) hs)
    refine ⟨q, ?_⟩
    funext i
    apply MvPolynomial.ext
    intro d
    change (MvPolynomial.map (Pi.evalRingHom B i) q).coeff d = (p i).coeff d
    rw [MvPolynomial.coeff_map]
    rfl

private noncomputable def tensorGaloisMap {k E A : Type*} [Field k] [Field E]
    [Algebra k E] [CommRing A] [Algebra k A] (τ : E ≃ₐ[k] E) :
    E ⊗[k] A →ₐ[k] E ⊗[k] A :=
  Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id k A)

private theorem exists_one_tmul_eq_of_galois_fixed {k E A : Type*} [Field k] [Field E]
    [Algebra k E] [IsGalois k E] [CommRing A] [Algebra k A] (x : E ⊗[k] A)
    (hx : ∀ τ : E ≃ₐ[k] E, tensorGaloisMap τ x = x) :
    ∃ a : A, (1 : E) ⊗ₜ[k] a = x := by
  classical
  let b := Module.Free.chooseBasis k A
  let e := _root_.TensorProduct.equivFinsuppOfBasisRight (M := E) b
  have hcoord (τ : E ≃ₐ[k] E) (y : E ⊗[k] A) (i : Module.Free.ChooseBasisIndex k A) :
      e (tensorGaloisMap τ y) i = τ (e y i) := by
    induction y using _root_.TensorProduct.inductionOn with
    | tmul r a =>
      simp [e, tensorGaloisMap, Algebra.smul_def]
    | add z w hz hw => simp [hz, hw]
  have hr (i : Module.Free.ChooseBasisIndex k A) : ∃ c : k, algebraMap k E c = e x i :=
    (InfiniteGalois.mem_range_algebraMap_iff_fixed (e x i)).mpr fun τ ↦
      (hcoord τ x i).symm.trans (congrArg (fun y ↦ e y i) (hx τ))
  choose c hc using hr
  have hs i (hi : c i ≠ 0) : i ∈ (e x).support := by
    by_contra h
    exact hi ((map_eq_zero_iff _ (RingHom.injective (algebraMap k E))).mp
      ((hc i).trans (Finsupp.notMem_support_iff.mp h)))
  let d := Finsupp.onFinset (e x).support c hs
  refine ⟨b.repr.symm d, e.injective ?_⟩
  ext i
  change _root_.TensorProduct.equivFinsuppOfBasisRight b
    ((1 : E) ⊗ₜ[k] b.repr.symm d) i = e x i
  rw [_root_.TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
  simpa [Algebra.smul_def, d] using hc i

private theorem idempotent_is_constant {σ ι E : Type*} [Finite ι] [Field E]
    (p : MvPolynomial σ (ι → E)) (hp : IsIdempotentElem p) :
    MvPolynomial.C (MvPolynomial.constantCoeff p) = p := by
  apply (mvPolynomialPiRingEquiv σ (fun _ : ι ↦ E)).injective
  funext i
  let f := MvPolynomial.map (σ := σ) (Pi.evalRingHom (fun _ : ι ↦ E) i)
  change f (MvPolynomial.C (MvPolynomial.constantCoeff p)) = f p
  rw [show f (MvPolynomial.C (MvPolynomial.constantCoeff p)) =
      MvPolynomial.C (MvPolynomial.constantCoeff (f p)) by
    simp [f, MvPolynomial.constantCoeff_map]]
  have h := hp.map f
  have hz : f p * (f p - 1) = 0 := by rw [mul_sub, h.eq, mul_one, sub_self]
  rcases mul_eq_zero.mp hz with hzero | hone
  · simp [hzero]
  · simp [sub_eq_zero.mp hone]

private theorem map_constant_coefficients {σ ι E : Type*} [Fintype ι] [Field E]
    (f : MvPolynomial σ (ι → E) →+* MvPolynomial σ (ι → E))
    (hX : ∀ i, f (MvPolynomial.X i) = MvPolynomial.X i)
    (hscalar : ∀ c : E, ∃ a : ι → E, f (MvPolynomial.C (fun _ ↦ c)) = MvPolynomial.C a)
    (p : MvPolynomial σ (ι → E)) (d : σ →₀ ℕ) :
    f (MvPolynomial.C (p.coeff d)) = MvPolynomial.C ((f p).coeff d) := by
  classical
  let g := MvPolynomial.constantCoeff.comp (f.comp MvPolynomial.C)
  have hc : ∀ a : ι → E, f (MvPolynomial.C a) = MvPolynomial.C (g a) := by
    intro a
    have ha : ∃ b : ι → E, f (MvPolynomial.C a) = MvPolynomial.C b := by
      let e (i : ι) : ι → E := Pi.single i 1
      have hdistribute : a = ∑ i : ι, (fun _ ↦ a i) * e i := by
        funext j
        simp [e, Finset.sum_apply, Pi.single_apply]
      have he (i : ι) : IsIdempotentElem (e i) := by
        funext j
        by_cases hj : j = i <;> simp [e, hj]
      choose b hb using hscalar
      refine ⟨∑ i : ι, b (a i) *
        MvPolynomial.constantCoeff (f (MvPolynomial.C (e i))), ?_⟩
      calc
        f (MvPolynomial.C a) =
            ∑ i : ι, f (MvPolynomial.C ((fun _ ↦ a i) * e i)) := by
          exact (congrArg (f.comp MvPolynomial.C) hdistribute).trans (map_sum _ _ _)
        _ = _ := by
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [map_mul, map_mul, hb, map_mul,
            idempotent_is_constant _ (((he i).map MvPolynomial.C).map f)]
    obtain ⟨b, hb⟩ := ha
    simp [g, hb]
  have hf : f = MvPolynomial.map g := by
    apply MvPolynomial.ringHom_ext
    · intro a
      rw [MvPolynomial.map_C, hc]
    · intro i
      rw [MvPolynomial.map_X, hX]
  rw [hc, hf, MvPolynomial.coeff_map]

private noncomputable def mvPolynomialPiAlgEquiv (E σ ι : Type*) [Field E] [Finite ι] :
    MvPolynomial σ (ι → E) ≃ₐ[E] (ι → MvPolynomial σ E) := by
  refine AlgEquiv.ofRingEquiv (f := mvPolynomialPiRingEquiv σ (fun _ : ι ↦ E)) ?_
  intro c
  funext i
  change MvPolynomial.map (Pi.evalRingHom (fun _ : ι ↦ E) i)
    (MvPolynomial.C (fun _ ↦ c)) = MvPolynomial.C c
  simp

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- A module-finite affine-space algebra which splits into a finite power of
the base over a Galois extension is a polynomial ring over a finite reduced
coefficient algebra. -/
private theorem exists_mvPolynomial_ringEquiv_of_galois_split
    (k E : Type u) [Field k] [Field E] [Algebra k E] [IsGalois k E]
    (n : ℕ) (A : Type u) [CommRing A] [Algebra (MvPolynomial (Fin n) k) A]
    [Module.Finite (MvPolynomial (Fin n) k) A] (m : ℕ)
    (eSplit : (MvPolynomial (Fin n) E ⊗[MvPolynomial (Fin n) k] A) ≃ₐ[MvPolynomial (Fin n) E]
      (Fin m → MvPolynomial (Fin n) E)) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra k B) (_ : Module.Finite k B) (_ : IsReduced B),
      Nonempty (A ≃+* MvPolynomial (Fin n) B) := by
  classical
  let R := MvPolynomial (Fin n) k
  let S := MvPolynomial (Fin n) E
  let T := MvPolynomial (Fin n) (Fin m → E)
  let : Algebra k A := ((algebraMap R A).comp MvPolynomial.C).toAlgebra
  let : IsScalarTower k R A := IsScalarTower.of_algebraMap_eq' rfl
  let eBase := Algebra.IsPushout.cancelBaseChangeAlg k E R S A
  let ePi := mvPolynomialPiAlgEquiv E (Fin n) (Fin m)
  let e : E ⊗[k] A ≃ₐ[E] T :=
    eBase.symm.trans ((eSplit.restrictScalars E).trans ePi.symm)
  let j : A →ₐ[k] E ⊗[k] A := Algebra.TensorProduct.includeRight
  let g : A →ₐ[k] T := (e.restrictScalars k).toAlgHom.comp j
  have hg_apply (a : A) : g a = e (j a) := rfl
  have hg : Function.Injective g :=
    e.injective.comp (Algebra.TensorProduct.includeRight_injective (algebraMap k E).injective)
  have hX (i : Fin n) : g (algebraMap R A (MvPolynomial.X i)) = MvPolynomial.X i := by
    apply ePi.injective
    funext t
    change ePi (ePi.symm (eSplit (eBase.symm ((1 : E) ⊗ₜ[k]
      algebraMap R A (MvPolynomial.X i))))) t =
      MvPolynomial.map (Pi.evalRingHom (fun _ : Fin m ↦ E) t) (MvPolynomial.X i)
    rw [ePi.apply_symm_apply, Algebra.IsPushout.cancelBaseChangeAlg_symm_tmul, map_one,
      ← Algebra.TensorProduct.algebraMap_apply', IsScalarTower.algebraMap_apply R S (S ⊗[R] A),
      eSplit.commutes, MvPolynomial.map_X]
    change algebraMap R S (MvPolynomial.X i) = MvPolynomial.X i
    change MvPolynomial.map (algebraMap k E) (MvPolynomial.X i) = MvPolynomial.X i
    rw [MvPolynomial.map_X]
  let constants : (Fin m → E) →ₐ[k] T := IsScalarTower.toAlgHom k (Fin m → E) T
  let B := constants.range.comap g
  let h : B →+* (Fin m → E) :=
    MvPolynomial.constantCoeff.comp (g.toRingHom.comp B.val.toRingHom)
  have hB (b : B) : MvPolynomial.C (h b) = g (b : A) := by
    obtain ⟨c, hc⟩ := b.property
    change MvPolynomial.C c = g (b : A) at hc
    change MvPolynomial.C (MvPolynomial.constantCoeff (g (b : A))) = g (b : A)
    rw [← hc, MvPolynomial.constantCoeff_C]
  have hh : Function.Injective h := by
    intro b b' hb
    apply Subtype.ext
    apply hg
    rw [← hB, ← hB, hb]
  have hcoeff (a : A) (d : Fin n →₀ ℕ) : (g a).coeff d ∈ Set.range h := by
    have hfixed : ∀ τ : E ≃ₐ[k] E,
        tensorGaloisMap τ (e.symm (MvPolynomial.C ((g a).coeff d))) =
        e.symm (MvPolynomial.C ((g a).coeff d)) := by
      intro τ
      let f : T →+* T :=
        e.toRingHom.comp ((tensorGaloisMap τ).toRingHom.comp e.symm.toRingHom)
      have hf_apply (p : T) : f p = e (tensorGaloisMap τ (e.symm p)) := rfl
      have hf (a' : A) : f (g a') = g a' := by
        rw [hf_apply, hg_apply, e.symm_apply_apply]
        congr 1
        change Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id k A) ((1 : E) ⊗ₜ[k] a') =
          (1 : E) ⊗ₜ[k] a'
        rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
      have hfX (i : Fin n) : f (MvPolynomial.X i) = MvPolynomial.X i := by
        rw [← hX, hf]
      have hfScalar (c : E) :
          ∃ b : Fin m → E, f (MvPolynomial.C (fun _ ↦ c)) = MvPolynomial.C b := by
        refine ⟨fun _ ↦ τ c, ?_⟩
        have hScalar (c' : E) : algebraMap E T c' = MvPolynomial.C (fun _ ↦ c') := rfl
        rw [← hScalar c, ← hScalar (τ c), hf_apply, e.symm.commutes, ← e.commutes]
        congr 1
      apply e.injective
      change f (MvPolynomial.C ((g a).coeff d)) =
        e (e.symm (MvPolynomial.C ((g a).coeff d)))
      rw [e.apply_symm_apply, map_constant_coefficients f hfX hfScalar, hf]
    obtain ⟨b, hb⟩ := exists_one_tmul_eq_of_galois_fixed _ hfixed
    have hb' : g b = MvPolynomial.C ((g a).coeff d) := by
      change e ((1 : E) ⊗ₜ[k] b) = _
      rw [hb, e.apply_symm_apply]
    refine ⟨⟨b, ⟨(g a).coeff d, hb'.symm⟩⟩, ?_⟩
    change MvPolynomial.constantCoeff (g b) = _
    rw [hb', MvPolynomial.constantCoeff_C]
  let F : MvPolynomial (Fin n) B →ₐ[k] A :=
    MvPolynomial.aevalTower B.val (fun i ↦ algebraMap R A (MvPolynomial.X i))
  have hF : g.toRingHom.comp F.toRingHom = MvPolynomial.map h := by
    apply MvPolynomial.ringHom_ext
    · intro b
      change g (F (MvPolynomial.C b)) = (MvPolynomial.map h) (MvPolynomial.C b)
      rw [MvPolynomial.map_C]
      have hFC : F (MvPolynomial.C b) = (b : A) := MvPolynomial.aevalTower_C _ _ b
      rw [hFC, hB]
    · intro i
      change g (F (MvPolynomial.X i)) = (MvPolynomial.map h) (MvPolynomial.X i)
      have hFX : F (MvPolynomial.X i) = algebraMap R A (MvPolynomial.X i) :=
        MvPolynomial.aevalTower_X _ _ i
      rw [MvPolynomial.map_X, hFX, hX]
  have hF_apply (p : MvPolynomial (Fin n) B) : g (F p) = MvPolynomial.map h p :=
    RingHom.congr_fun hF p
  have hF_bijective : Function.Bijective F := by
    constructor
    · intro p q hpq
      exact (MvPolynomial.map_injective h hh) ((hF_apply p).symm.trans
        ((congrArg g hpq).trans (hF_apply q)))
    · intro a
      have hr : g a ∈ Set.range (MvPolynomial.map h) := by
        apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
        intro c hc
        obtain ⟨d, _, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc
        exact hcoeff a d
      obtain ⟨p, hp⟩ := hr
      exact ⟨p, hg ((hF_apply p).trans hp)⟩
  let eF := AlgEquiv.ofBijective F hF_bijective
  let q : A →+* B := MvPolynomial.constantCoeff.comp eF.symm.toRingHom
  let ε : R →+* k := MvPolynomial.constantCoeff
  have hq : q.comp (algebraMap R A) = (algebraMap k B).comp ε := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change MvPolynomial.constantCoeff (eF.symm (algebraMap k A c)) =
        algebraMap k B (MvPolynomial.constantCoeff (MvPolynomial.C c))
      rw [eF.symm.commutes, IsScalarTower.algebraMap_apply k B (MvPolynomial (Fin n) B),
        MvPolynomial.algebraMap_eq,
        MvPolynomial.constantCoeff_C, MvPolynomial.constantCoeff_C]
    · intro i
      have hFX : eF (MvPolynomial.X i) = algebraMap R A (MvPolynomial.X i) :=
        MvPolynomial.aevalTower_X _ _ i
      change MvPolynomial.constantCoeff (eF.symm (algebraMap R A (MvPolynomial.X i))) =
        algebraMap k B (MvPolynomial.constantCoeff (MvPolynomial.X i))
      rw [← hFX, eF.symm_apply_apply, MvPolynomial.constantCoeff_X,
        MvPolynomial.constantCoeff_X, map_zero]
  let qLinear : A →ₛₗ[ε] B :=
    { q.toAddMonoidHom with
      map_smul' := fun r a ↦ by
        change q (r • a) = ε r • q a
        rw [Algebra.smul_def, map_mul, Algebra.smul_def]
        exact congrArg (fun x : B ↦ x * q a) (RingHom.congr_fun hq r) }
  have hqSurj : Function.Surjective q :=
    (show Function.Surjective (MvPolynomial.constantCoeff : MvPolynomial (Fin n) B →+* B) from
      fun b ↦ ⟨MvPolynomial.C b, MvPolynomial.constantCoeff_C _ b⟩).comp eF.symm.surjective
  have hfin : Module.Finite k B := Module.Finite.of_surjective qLinear hqSurj
  have hred : IsReduced B := isReduced_of_injective h hh
  exact ⟨B, inferInstance, inferInstance, hfin, hred, ⟨eF.symm.toRingEquiv⟩⟩

/-- A module-finite affine-space algebra which splits over a Galois extension
is a finite product of polynomial rings over fields. -/
theorem mvPolynomial_product_of_galois_split
    (k E : Type u) [Field k] [Field E] [Algebra k E] [IsGalois k E]
    (n : ℕ) (A : Type u) [CommRing A] [Algebra (MvPolynomial (Fin n) k) A]
    [Module.Finite (MvPolynomial (Fin n) k) A] (m : ℕ)
    (eSplit : (MvPolynomial (Fin n) E ⊗[MvPolynomial (Fin n) k] A) ≃ₐ[MvPolynomial (Fin n) E]
      (Fin m → MvPolynomial (Fin n) E)) :
    ∃ (ι : Type u) (_ : Finite ι) (K : ι → Type u) (_ : ∀ i, Field (K i)),
      Nonempty (A ≃+* ∀ i, MvPolynomial (Fin n) (K i)) := by
  obtain ⟨B, hRing, hAlg, hFinite, hReduced, ⟨e⟩⟩ :=
    exists_mvPolynomial_ringEquiv_of_galois_split k E n A m eSplit
  let := hRing
  let := hAlg
  let := hFinite
  let := hReduced
  let : IsArtinianRing B := IsArtinianRing.of_finite k B
  let K (i : MaximalSpectrum B) := B ⧸ i.asIdeal
  let : ∀ i, Field (K i) := fun i ↦ Ideal.Quotient.field i.asIdeal
  let ePoly := MvPolynomial.mapEquiv (Fin n) (IsArtinianRing.equivPi B).toRingEquiv
  exact ⟨MaximalSpectrum B, inferInstance, K, inferInstance,
    ⟨e.trans (ePoly.trans (mvPolynomialPiRingEquiv (Fin n) K))⟩⟩

end Langlands.Algebra
