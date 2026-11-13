import Mathlib

/-! # Invariant functions of a finite group of permutations

Let `R` be a finitely generated `ℂ`-algebra of complex functions on a set `X` that is a domain,
whose `ℂ`-points are evaluations and which separates the points of `X`, and let `W` be a finite
group of permutations of `X` preserving `R`. Then the `W`-invariant elements of `R` form a
finitely generated `ℂ`-algebra that is a domain, whose `ℂ`-points are evaluations, and which
separates the `W`-orbits. This is the algebra used for Renard VI.7.1 (the variety of cuspidal
data `X(M)/W`).
-/

noncomputable section

namespace Langlands.CuspidalSupport.InvariantFunctions

variable {X : Type*} (R : Subalgebra ℂ (X → ℂ)) (W : Subgroup (Equiv.Perm X))

/-- The elements of `R` invariant under every permutation in `W`, as a subalgebra of `R`. -/
def fixedSubalgebra : Subalgebra ℂ R where
  carrier := {f | ∀ w ∈ W, ∀ x, (f : X → ℂ) (w x) = (f : X → ℂ) x}
  mul_mem' {f g} hf hg w hw x := by
    simp only [Subalgebra.coe_mul, Pi.mul_apply, hf w hw x, hg w hw x]
  add_mem' {f g} hf hg w hw x := by
    simp only [Subalgebra.coe_add, Pi.add_apply, hf w hw x, hg w hw x]
  algebraMap_mem' c w hw x := rfl

variable {R W}

/-- `W` acts on `R` by `w • f = f ∘ w⁻¹`, when every element of `W` preserves `R`. -/
@[instance_reducible]
def action (hW : ∀ w ∈ W, ∀ f ∈ R, (fun x => f (w x)) ∈ R) : MulSemiringAction W R where
  smul w f := ⟨fun x => (f : X → ℂ) (((w⁻¹ : W) : Equiv.Perm X) x), hW _ (w⁻¹).2 f f.2⟩
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl
  smul_one _ := rfl
  smul_mul _ _ _ := rfl

theorem fixedSubalgebra_isInvariant (hW : ∀ w ∈ W, ∀ f ∈ R, (fun x => f (w x)) ∈ R) :
    letI := action hW
    Algebra.IsInvariant (fixedSubalgebra R W) R W := by
  let := action hW
  refine ⟨fun f hf => ⟨⟨f, fun w hw x => ?_⟩, rfl⟩⟩
  have := congrArg (fun g : R => (g : X → ℂ) x) (hf (⟨w, hw⟩⁻¹))
  exact this

theorem fixedSubalgebra_isIntegral (hW : ∀ w ∈ W, ∀ f ∈ R, (fun x => f (w x)) ∈ R)
    [Finite W] : Algebra.IsIntegral (fixedSubalgebra R W) R := by
  let := action hW
  have := fixedSubalgebra_isInvariant hW
  exact Algebra.IsInvariant.isIntegral (fixedSubalgebra R W) R W

theorem fixedSubalgebra_finiteType [Algebra.FiniteType ℂ R]
    (hW : ∀ w ∈ W, ∀ f ∈ R, (fun x => f (w x)) ∈ R) [Finite W] :
    Algebra.FiniteType ℂ (fixedSubalgebra R W) := by
  have := fixedSubalgebra_isIntegral hW
  have : Algebra.FiniteType (fixedSubalgebra R W) R :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℂ _ R
  have hfin := Algebra.IsIntegral.finite (R := fixedSubalgebra R W) (A := R)
  exact ⟨fg_of_fg_of_fg ℂ (fixedSubalgebra R W) R Algebra.FiniteType.out
    hfin.fg_top Subtype.val_injective⟩

set_option synthInstance.maxHeartbeats 200000 in
theorem fixedSubalgebra_exists_eval [Algebra.FiniteType ℂ R]
    (hev : ∀ ψ : R →ₐ[ℂ] ℂ, ∃ x : X, ∀ f : R, ψ f = (f : X → ℂ) x)
    (hW : ∀ w ∈ W, ∀ f ∈ R, (fun x => f (w x)) ∈ R) [Finite W]
    (φ : fixedSubalgebra R W →ₐ[ℂ] ℂ) :
    ∃ x : X, ∀ f : fixedSubalgebra R W, φ f = ((f : R) : X → ℂ) x := by
  have := fixedSubalgebra_isIntegral hW
  let S := fixedSubalgebra R W
  let φr : S →+* ℂ := φ.toRingHom
  have hsurj : Function.Surjective φr := fun c => ⟨algebraMap ℂ S c, by simp [φr]⟩
  let P : Ideal S := RingHom.ker φr
  have hPmax : P.IsMaximal := RingHom.ker_isMaximal_of_surjective φr hsurj
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (R := S) (S := R)
    P (by
      rw [(RingHom.injective_iff_ker_eq_bot _).mp (show Function.Injective (algebraMap S R) from
        Subtype.val_injective)]
      exact bot_le)
  let : Field (R ⧸ Q) := Ideal.Quotient.field Q
  have : Algebra.FiniteType ℂ (R ⧸ Q) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ Q)
      (Ideal.Quotient.mkₐ_surjective ℂ Q)
  have : Module.Finite ℂ (R ⧸ Q) := finite_of_finite_type_of_isJacobsonRing ℂ (R ⧸ Q)
  have hbij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ) (K := R ⧸ Q)
  let e : ℂ ≃ₐ[ℂ] R ⧸ Q := AlgEquiv.ofBijective (Algebra.ofId ℂ (R ⧸ Q)) hbij
  let ψ : R →ₐ[ℂ] ℂ := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ Q)
  obtain ⟨x, hx⟩ := hev ψ
  refine ⟨x, fun f => ?_⟩
  rw [← hx]
  have hmem : (f : R) - algebraMap ℂ R (φ f) ∈ Q := by
    have h1 : f - algebraMap ℂ S (φ f) ∈ P := by
      show φ (f - algebraMap ℂ S (φ f)) = 0
      have h0 := map_sub φ f (algebraMap ℂ S (φ f))
      rw [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self] at h0
      exact h0
    rw [← hQP] at h1
    simpa using h1
  have h2 : ψ ((f : R) - algebraMap ℂ R (φ f)) = 0 := by
    show e.symm (Ideal.Quotient.mk Q _) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hmem, map_zero]
  rw [map_sub, AlgHom.commutes, sub_eq_zero] at h2
  exact h2.symm

/-- **Invariant functions of a finite group of permutations.** For a finitely generated
`ℂ`-algebra `R` of functions on `X` that is a domain, whose `ℂ`-points are evaluations and which
separates points, and a finite group `W` of permutations preserving `R`, the `W`-invariant
elements of `R` form a finitely generated `ℂ`-subalgebra that is a domain, whose `ℂ`-points are
evaluations, and which separates exactly the `W`-orbits. -/
theorem exists_invariantSubalgebra [Algebra.FiniteType ℂ R] [IsDomain R]
    (hev : ∀ ψ : R →ₐ[ℂ] ℂ, ∃ x : X, ∀ f : R, ψ f = (f : X → ℂ) x)
    (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ R, f x ≠ f y)
    [Finite W] (hW : ∀ w ∈ W, ∀ f ∈ R, (fun x => f (w x)) ∈ R) :
    ∃ O : Subalgebra ℂ (X → ℂ),
      (O : Set (X → ℂ)) = {f | f ∈ R ∧ ∀ w ∈ W, ∀ x, f (w x) = f x} ∧
      Algebra.FiniteType ℂ O ∧ IsDomain O ∧
      (∀ φ : O →ₐ[ℂ] ℂ, ∃ x : X, ∀ f : O, φ f = (f : X → ℂ) x) ∧
      ∀ x y : X, (∃ w ∈ W, w y = x) ↔ ∀ f ∈ O, f x = f y := by
  classical
  set S := fixedSubalgebra R W
  let e : S ≃ₐ[ℂ] S.map R.val :=
    Subalgebra.equivMapOfInjective S R.val Subtype.val_injective
  refine ⟨S.map R.val, ?_, ?_, ?_, ?_, ?_⟩
  · ext f
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s.2, hs⟩
    · rintro ⟨hf, hinv⟩
      exact ⟨⟨f, hf⟩, hinv, rfl⟩
  · have := fixedSubalgebra_finiteType hW
    exact Algebra.FiniteType.equiv inferInstance e
  · exact e.toMulEquiv.symm.isDomain
  · intro φ
    obtain ⟨x, hx⟩ := fixedSubalgebra_exists_eval hev hW (φ.comp e.toAlgHom)
    refine ⟨x, fun f => ?_⟩
    have h2 : ((e.symm f : R) : X → ℂ) = (f : X → ℂ) := by
      conv_rhs => rw [← e.apply_symm_apply f]
      rfl
    have := hx (e.symm f)
    rw [h2] at this
    simpa using this
  · intro x y
    constructor
    · rintro ⟨w, hw, rfl⟩ f hf
      obtain ⟨s, hs, rfl⟩ := hf
      exact hs w hw y
    · intro hall
      by_contra hne
      push Not at hne
      have hne' : ∀ w : W, (w : Equiv.Perm X) x ≠ y := by
        intro w hwx
        refine hne _ (W.inv_mem w.2) ?_
        rw [← hwx]
        simp
      have hh : ∀ w : W, ∃ h ∈ R, h y = 0 ∧ h ((w : Equiv.Perm X) x) = 1 := by
        intro w
        obtain ⟨f, hf, hfne⟩ := hsep _ _ (hne' w)
        refine ⟨(f ((w : Equiv.Perm X) x) - f y)⁻¹ • (f - algebraMap ℂ (X → ℂ) (f y)),
          R.smul_mem (R.sub_mem hf (R.algebraMap_mem _)) _, ?_, ?_⟩
        · simp
        · simp [inv_mul_cancel₀ (sub_ne_zero.mpr hfne)]
      choose h hR h0 h1 using hh
      have := Fintype.ofFinite W
      let g : X → ℂ := 1 - ∏ w : W, (1 - h w)
      have hgR : g ∈ R :=
        R.sub_mem R.one_mem (Subalgebra.prod_mem R fun w _ => R.sub_mem R.one_mem (hR w))
      have hgy : g y = 0 := by simp [g, Finset.prod_apply, h0]
      have hgx : ∀ w : W, g ((w : Equiv.Perm X) x) = 1 := by
        intro w
        simp only [g, Pi.sub_apply, Pi.one_apply, Finset.prod_apply]
        rw [Finset.prod_eq_zero (Finset.mem_univ w) (by simp [h1])]
        simp
      let F : X → ℂ := fun z => ∏ w : W, g ((w : Equiv.Perm X) z)
      have hFR : F ∈ R := by
        have : F = ∏ w : W, (fun z => g ((w : Equiv.Perm X) z)) := by
          ext z
          simp [F, Finset.prod_apply]
        rw [this]
        exact Subalgebra.prod_mem R fun w _ => hW w w.2 g hgR
      have hFinv : ∀ w ∈ W, ∀ z, F (w z) = F z := by
        intro w hw z
        exact Fintype.prod_equiv (Equiv.mulRight ⟨w, hw⟩) _ _ (fun v => rfl)
      have hFx : F x = 1 := Finset.prod_eq_one fun w _ => hgx w
      have hFy : F y = 0 := Finset.prod_eq_zero (Finset.mem_univ 1) (by simpa using hgy)
      have := hall F ⟨⟨F, hFR⟩, hFinv, rfl⟩
      rw [hFx, hFy] at this
      exact one_ne_zero this

end Langlands.CuspidalSupport.InvariantFunctions
