import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.FiniteType
import Mathlib.LinearAlgebra.Projection

universe u v

/-! # Jets along a section of a smooth algebra are finite projective

For a formally smooth algebra `A` of finite type over `R` with an augmentation
`ε : A →ₐ[R] R` and `I = ker ε`, every quotient `A ⧸ I ^ (n + 1)` is a finite projective
`R`-module. See the paired Markdown.
-/

open MvPolynomial

set_option autoImplicit false

namespace MvPolynomial

variable (σ : Type*) (R : Type u) [CommRing R]

/-- Polynomials supported in degrees `≥ n + 1` and in degrees `≤ n` are complementary. -/
theorem isCompl_restrictSupport_degree (n : ℕ) :
    IsCompl (restrictSupport R (Finsupp.degree ⁻¹' Set.Ici (n + 1) : Set (σ →₀ ℕ)))
      (restrictSupport R {x : σ →₀ ℕ | Finsupp.degree x ≤ n}) := by
  refine ⟨Submodule.disjoint_def.mpr fun p hs ht => ?_, codisjoint_iff.mpr ?_⟩
  · rw [mem_restrictSupport_iff] at hs ht
    rw [← MvPolynomial.support_eq_empty, Finset.eq_empty_iff_forall_notMem]
    intro x hx
    have h1 : n + 1 ≤ Finsupp.degree x := hs hx
    have h2 : Finsupp.degree x ≤ n := ht hx
    omega
  · rw [restrictSupport_eq_span, restrictSupport_eq_span, ← Submodule.span_union,
      ← Set.image_union]
    have : (Finsupp.degree ⁻¹' Set.Ici (n + 1) ∪ {x : σ →₀ ℕ | Finsupp.degree x ≤ n}) =
        Set.univ := by
      ext x
      simp only [Set.mem_union, Set.mem_preimage, Set.mem_Ici, Set.mem_ofPred_eq, Set.mem_univ,
        iff_true]
      omega
    rw [this, ← restrictSupport_eq_span, restrictSupport_univ]

/-- The truncated polynomial ring `R[σ] ⧸ (idealOfVars) ^ (n + 1)` is linearly equivalent to
the polynomials of degree at most `n`. -/
noncomputable def quotientIdealOfVarsPowEquiv (n : ℕ) :
    (MvPolynomial σ R ⧸ idealOfVars σ R ^ (n + 1)) ≃ₗ[R]
      restrictSupport R {x : σ →₀ ℕ | Finsupp.degree x ≤ n} :=
  (Submodule.Quotient.restrictScalarsEquiv R (idealOfVars σ R ^ (n + 1))).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (by rw [pow_idealOfVars]; rfl) ≪≫ₗ
    Submodule.quotientEquivOfIsCompl _ _ (isCompl_restrictSupport_degree σ R n)

theorem free_quotient_idealOfVars_pow (n : ℕ) :
    Module.Free R (MvPolynomial σ R ⧸ idealOfVars σ R ^ (n + 1)) :=
  have := Module.Free.of_basis (basisRestrictSupport R {x : σ →₀ ℕ | Finsupp.degree x ≤ n})
  Module.Free.of_equiv (quotientIdealOfVarsPowEquiv σ R n).symm

theorem finite_quotient_idealOfVars_pow [Finite σ] (n : ℕ) :
    Module.Finite R (MvPolynomial σ R ⧸ idealOfVars σ R ^ (n + 1)) :=
  have : Finite {x : σ →₀ ℕ | Finsupp.degree x ≤ n} := (Finsupp.finite_of_degree_le n).to_subtype
  have := Module.Finite.of_basis (basisRestrictSupport R {x : σ →₀ ℕ | Finsupp.degree x ≤ n})
  Module.Finite.equiv (quotientIdealOfVarsPowEquiv σ R n).symm

end MvPolynomial

namespace Algebra.FormallySmooth

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]

/-- For a formally smooth algebra of finite type with an augmentation `ε`, every quotient
`A ⧸ (ker ε) ^ (n + 1)` is an algebra retract of a truncated polynomial ring. -/
theorem exists_retract_quotient_ker_pow [FormallySmooth R A] [FiniteType R A]
    (ε : A →ₐ[R] R) (n : ℕ) :
    ∃ (m : ℕ) (q : MvPolynomial (Fin m) R ⧸ idealOfVars (Fin m) R ^ (n + 1) →ₐ[R]
        A ⧸ RingHom.ker ε ^ (n + 1))
      (s : A ⧸ RingHom.ker ε ^ (n + 1) →ₐ[R] MvPolynomial (Fin m) R ⧸ idealOfVars (Fin m) R ^ (n + 1)),
      q.comp s = AlgHom.id R _ := by
  classical
  set I := RingHom.ker ε
  obtain ⟨m, f₀, hf₀⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹_›
  -- Generators of `A` lying in `I`.
  let x : Fin m → A := fun i => f₀ (X i) - algebraMap R A (ε (f₀ (X i)))
  have hxI : ∀ i, x i ∈ I := fun i => by simp [I, x, RingHom.mem_ker]
  let g : MvPolynomial (Fin m) R →ₐ[R] A := aeval x
  have hg : Function.Surjective g := by
    have hle : f₀.range ≤ g.range := by
      conv_lhs => rw [aeval_unique f₀]
      rw [aeval_range]
      refine Algebra.adjoin_le ?_
      rintro _ ⟨i, rfl⟩
      have h : (f₀ ∘ X) i = g (X i) + algebraMap R A (ε (f₀ (X i))) := by simp [g, x]
      rw [SetLike.mem_coe, h]
      exact g.range.add_mem ⟨X i, rfl⟩ (g.range.algebraMap_mem _)
    intro a
    obtain ⟨b, hb⟩ := hf₀ a
    exact (AlgHom.mem_range g).mp (hle ((AlgHom.mem_range f₀).mpr ⟨b, hb⟩))
  -- `ε ∘ g` is the constant coefficient.
  have hεg : ∀ p, ε (g p) = constantCoeff p := by
    have h : ε.comp g = aeval (fun _ => (0 : R)) := by
      ext i
      simp [g, x]
    intro p
    simpa using AlgHom.congr_fun h p
  have hmem : ∀ p, ε (g p) = 0 → p ∈ idealOfVars (Fin m) R := by
    intro p hp
    rw [← pow_one (idealOfVars (Fin m) R), mem_pow_idealOfVars_iff']
    intro d hd
    have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (by omega)
    subst hd0
    rw [← constantCoeff_eq, ← hεg]
    exact hp
  set J := idealOfVars (Fin m) R ^ (n + 1)
  have hJ : J ≤ (I ^ (n + 1)).comap g := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    refine Ideal.pow_right_mono ?_ (n + 1)
    rw [Ideal.map_le_iff_le_comap, idealOfVars, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simpa [g] using hxI i
  let gq : MvPolynomial (Fin m) R ⧸ J →ₐ[R] A ⧸ I ^ (n + 1) := Ideal.quotientMapₐ (I ^ (n + 1)) g hJ
  have hgq : Function.Surjective gq := Ideal.quotientMap_surjective (H := hJ) hg
  have hgq_mk : ∀ p, gq (Ideal.Quotient.mk J p) = Ideal.Quotient.mk (I ^ (n + 1)) (g p) :=
    fun p => rfl
  -- The image of the ideal of variables, whose `(n + 1)`-st power vanishes.
  let N : Ideal (MvPolynomial (Fin m) R ⧸ J) := (idealOfVars (Fin m) R).map (Ideal.Quotient.mk J)
  have hN : N ^ (n + 1) = ⊥ := by
    rw [← Ideal.map_pow, Ideal.map_quotient_self]
  have hNmem : ∀ p, ε (g p) = 0 → Ideal.Quotient.mk J p ∈ N :=
    fun p hp => Ideal.mem_map_of_mem _ (hmem p hp)
  have hIpow : I ^ (n + 1) ≤ I := Ideal.pow_le_self (Nat.succ_ne_zero n)
  -- The kernel of `gq` is nilpotent.
  have hK : IsNilpotent (RingHom.ker gq) := by
    refine ⟨n + 1, ?_⟩
    have hKN : RingHom.ker gq ≤ N := by
      intro q hq
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
      rw [RingHom.mem_ker, hgq_mk, Ideal.Quotient.eq_zero_iff_mem] at hq
      exact hNmem p (hIpow hq)
    rw [Ideal.zero_eq_bot, eq_bot_iff, ← hN]
    exact Ideal.pow_right_mono hKN (n + 1)
  let e := Ideal.quotientKerAlgEquivOfSurjective hgq
  let t : A →ₐ[R] MvPolynomial (Fin m) R ⧸ J :=
    FormallySmooth.lift (RingHom.ker gq) hK
      ((e.symm : A ⧸ I ^ (n + 1) →ₐ[R] _).comp (Ideal.Quotient.mkₐ R (I ^ (n + 1))))
  have ht : ∀ a, gq (t a) = Ideal.Quotient.mk (I ^ (n + 1)) a := by
    intro a
    have h1 := FormallySmooth.mk_lift (RingHom.ker gq) hK
      ((e.symm : A ⧸ I ^ (n + 1) →ₐ[R] _).comp (Ideal.Quotient.mkₐ R (I ^ (n + 1)))) a
    have h2 : gq (t a) = e (Ideal.Quotient.mk (RingHom.ker gq) (t a)) := rfl
    rw [h2, h1]
    simp
  -- `t` kills `I ^ (n + 1)`.
  have htI : ∀ a ∈ I, t a ∈ N := by
    intro a ha
    obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (t a)
    rw [← hp]
    refine hNmem p ?_
    have h1 : Ideal.Quotient.mk (I ^ (n + 1)) (g p) = Ideal.Quotient.mk (I ^ (n + 1)) a := by
      rw [← hgq_mk, hp, ht]
    have h2 := hIpow (Ideal.Quotient.eq.mp h1)
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h2
    rw [h2]
    exact ha
  have htker : ∀ a ∈ I ^ (n + 1), t a = 0 := by
    intro a ha
    have hmap : Ideal.map t (I ^ (n + 1)) ≤ ⊥ := by
      rw [Ideal.map_pow, ← hN]
      exact Ideal.pow_right_mono (Ideal.map_le_of_le_comap (f := t) (K := N) fun b hb => Ideal.mem_comap.mpr (htI b hb)) (n + 1)
    exact Ideal.mem_bot.mp (hmap (Ideal.mem_map_of_mem t ha))
  let s : A ⧸ I ^ (n + 1) →ₐ[R] MvPolynomial (Fin m) R ⧸ J :=
    Ideal.Quotient.liftₐ (I ^ (n + 1)) t htker
  refine ⟨m, gq, s, Ideal.Quotient.algHom_ext R (AlgHom.ext fun a => ?_)⟩
  change gq (t a) = Ideal.Quotient.mk _ a
  exact ht a

/-- For a formally smooth algebra of finite type with an augmentation `ε`, every quotient
`A ⧸ (ker ε) ^ (n + 1)` is a finite projective module over the base. -/
theorem finite_projective_quotient_ker_pow [FormallySmooth R A] [FiniteType R A]
    (ε : A →ₐ[R] R) (n : ℕ) :
    Module.Finite R (A ⧸ RingHom.ker ε ^ (n + 1)) ∧
      Module.Projective R (A ⧸ RingHom.ker ε ^ (n + 1)) := by
  obtain ⟨m, q, s, hqs⟩ := exists_retract_quotient_ker_pow ε n
  have := MvPolynomial.free_quotient_idealOfVars_pow (Fin m) R n
  have := MvPolynomial.finite_quotient_idealOfVars_pow (Fin m) R n
  have hq : Function.Surjective q := fun y => ⟨s y, AlgHom.congr_fun hqs y⟩
  exact ⟨Module.Finite.of_surjective q.toLinearMap hq,
    Module.Projective.of_split s.toLinearMap q.toLinearMap
      (LinearMap.ext fun y => AlgHom.congr_fun hqs y)⟩

end Algebra.FormallySmooth

/-- For a smooth algebra with an augmentation `ε`, every quotient `A ⧸ (ker ε) ^ (n + 1)` is a
finite projective module over the base. -/
theorem Algebra.Smooth.finite_projective_quotient_ker_pow {R : Type u} [CommRing R] {A : Type v}
    [CommRing A] [Algebra R A] [Algebra.Smooth R A] (ε : A →ₐ[R] R) (n : ℕ) :
    Module.Finite R (A ⧸ RingHom.ker ε ^ (n + 1)) ∧
      Module.Projective R (A ⧸ RingHom.ker ε ^ (n + 1)) :=
  Algebra.FormallySmooth.finite_projective_quotient_ker_pow ε n
