import Langlands.CommutativeAlgebra.Popescu.LocalLifting
import Langlands.MathlibBase

/-! # The algebra `A[x, z]/(xᵢⁿ - Σⱼ zᵢⱼ aⱼ)` of the proof of Stacks Lemma 10.3 (07FE) -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

open MvPolynomial

namespace SmoothingAlgebra

variable {A : Type u} [CommRing A] (d : ℕ) {r : ℕ} (n : ℕ) (a : Fin r → A)

/-- The relations `xᵢⁿ - Σⱼ zᵢⱼ aⱼ`. -/
noncomputable def rel (i : Fin d) : MvPolynomial (Fin d ⊕ (Fin d × Fin r)) A :=
  X (Sum.inl i) ^ n - ∑ j, X (Sum.inr (i, j)) * C (a j)

/-- The algebra `A[x, z]/(xᵢⁿ - Σⱼ zᵢⱼ aⱼ)`. -/
def Alg : Type u :=
  MvPolynomial (Fin d ⊕ (Fin d × Fin r)) A ⧸ Ideal.span (Set.range (rel d n a))

noncomputable instance : CommRing (Alg d n a) :=
  inferInstanceAs (CommRing (MvPolynomial (Fin d ⊕ (Fin d × Fin r)) A ⧸ _))

noncomputable instance : Algebra A (Alg d n a) :=
  inferInstanceAs (Algebra A (MvPolynomial (Fin d ⊕ (Fin d × Fin r)) A ⧸ _))

/-- The quotient map onto `Alg`. -/
noncomputable def mk : MvPolynomial (Fin d ⊕ (Fin d × Fin r)) A →ₐ[A] Alg d n a :=
  Ideal.Quotient.mkₐ A _

theorem mk_surjective : Function.Surjective (mk d n a) := Ideal.Quotient.mkₐ_surjective A _

theorem mk_C (x : A) : mk d n a (C x) = algebraMap A (Alg d n a) x := (mk d n a).commutes x

theorem mk_rel (i : Fin d) : mk d n a (rel d n a i) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)

theorem rel_eq (i : Fin d) :
    mk d n a (X (Sum.inl i)) ^ n =
      ∑ j, mk d n a (X (Sum.inr (i, j))) * algebraMap A (Alg d n a) (a j) := by
  have h := mk_rel d n a i
  rw [rel, map_sub, map_pow, map_sum, sub_eq_zero] at h
  rw [h]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, mk_C]

variable (k : Type u) [Field k] [Algebra k A]

noncomputable instance : Algebra k (Alg d n a) :=
  inferInstanceAs (Algebra k (MvPolynomial (Fin d ⊕ (Fin d × Fin r)) A ⧸ _))

instance : IsScalarTower k A (Alg d n a) :=
  inferInstanceAs (IsScalarTower k A (MvPolynomial (Fin d ⊕ (Fin d × Fin r)) A ⧸ _))

/-- `Alg` as an algebra over `k[x₁, …, x_d]`, with `xᵢ ↦ xᵢ`. -/
noncomputable instance instAlgebraPoly : Algebra (MvPolynomial (Fin d) k) (Alg d n a) :=
  (aeval (R := k) fun i => mk d n a (X (Sum.inl i))).toRingHom.toAlgebra

instance : IsScalarTower k (MvPolynomial (Fin d) k) (Alg d n a) :=
  .of_algebraMap_eq fun c => (aeval_C _ c).symm

theorem algebraMap_X (i : Fin d) :
    algebraMap (MvPolynomial (Fin d) k) (Alg d n a) (X i) = mk d n a (X (Sum.inl i)) :=
  aeval_X _ _

instance [Algebra.FinitePresentation k A] : Algebra.FinitePresentation k (Alg d n a) :=
  show Algebra.FinitePresentation k
    (MvPolynomial (Fin d ⊕ (Fin d × Fin r)) A ⧸ Ideal.span (Set.range (rel d n a))) from
  Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range _))

instance [Algebra.FinitePresentation k A] :
    Algebra.FinitePresentation (MvPolynomial (Fin d) k) (Alg d n a) :=
  Algebra.FinitePresentation.of_restrict_scalars_finitePresentation k _ _

section Smooth

/-- `Alg_{aⱼ}` is formally smooth over `k[x]` when `A_{aⱼ}` is formally smooth over `k`: the relations
can be solved for `zᵢⱼ`. Proved by the lifting property. -/
theorem formallySmooth_away (j : Fin r) [Algebra.FormallySmooth k (Localization.Away (a j))] :
    Algebra.FormallySmooth (MvPolynomial (Fin d) k)
      (Localization.Away (algebraMap A (Alg d n a) (a j))) := by
  classical
  set R := MvPolynomial (Fin d) k
  set Bj := Localization.Away (algebraMap A (Alg d n a) (a j))
  apply Algebra.FormallySmooth.of_comp_surjective
  intro T _ _ J hJ φ
  let _ : Algebra k T := ((algebraMap R T).comp (algebraMap k R)).toAlgebra
  have : IsScalarTower k R T := .of_algebraMap_eq fun _ => rfl
  let ι₀ : Localization.Away (a j) →+* Bj := IsLocalization.Away.lift (a j)
    (g := (algebraMap (Alg d n a) Bj).comp (algebraMap A (Alg d n a)))
    (IsLocalization.Away.algebraMap_isUnit (algebraMap A (Alg d n a) (a j)))
  have hι₀ : ∀ x : A, ι₀ (algebraMap A _ x) = algebraMap (Alg d n a) Bj (algebraMap A _ x) :=
    fun x => IsLocalization.Away.lift_eq _ _ x
  let ι : Localization.Away (a j) →ₐ[k] Bj :=
    { ι₀ with
      commutes' := fun c => by
        show ι₀ (algebraMap k _ c) = _
        rw [IsScalarTower.algebraMap_apply k A (Localization.Away (a j)), hι₀,
          ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] }
  have hι : ∀ x : A, ι (algebraMap A _ x) = algebraMap (Alg d n a) Bj (algebraMap A _ x) := hι₀
  let α₀ : Localization.Away (a j) →ₐ[k] T ⧸ J := (φ.restrictScalars k).comp ι
  have hJn : IsNilpotent J := ⟨2, hJ⟩
  let α : Localization.Away (a j) →ₐ[k] T := Algebra.FormallySmooth.lift J hJn α₀
  have hα : ∀ y, Ideal.Quotient.mk J (α y) = α₀ y := Algebra.FormallySmooth.mk_lift J hJn α₀
  let αA : A →+* T := α.toRingHom.comp (algebraMap A (Localization.Away (a j)))
  have hu : IsUnit (αA (a j)) := (IsLocalization.Away.algebraMap_isUnit (a j)).map α
  let v : T := ↑hu.unit⁻¹
  have hv : v * αA (a j) = 1 := hu.val_inv_mul
  let zB : Fin d × Fin r → Bj := fun p => algebraMap (Alg d n a) Bj (mk d n a (X (Sum.inr p)))
  let xB : Fin d → Bj := fun i => algebraMap (Alg d n a) Bj (mk d n a (X (Sum.inl i)))
  choose t ht using fun p => Ideal.Quotient.mk_surjective (φ (zB p))
  let xT : Fin d → T := fun i => algebraMap R T (X i)
  let ε : Fin d → T := fun i => xT i ^ n - ∑ l, t (i, l) * αA (a l)
  let val : Fin d ⊕ (Fin d × Fin r) → T :=
    Sum.elim xT fun p => t p + if p.2 = j then v * ε p.1 else 0
  let ψ₀ : MvPolynomial (Fin d ⊕ (Fin d × Fin r)) A →+* T := eval₂Hom αA val
  have hrel : ∀ i, ψ₀ (rel d n a i) = 0 := by
    intro i
    simp only [rel, ψ₀, map_sub, map_pow, map_sum, map_mul, eval₂Hom_X', eval₂Hom_C, val,
      Sum.elim_inl, Sum.elim_inr, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    linear_combination (-(xT i ^ n - ∑ l, t (i, l) * αA (a l))) * hv
  have hle : Ideal.span (Set.range (rel d n a)) ≤ RingHom.ker ψ₀ := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hrel i
  let ψ₁ : Alg d n a →+* T := Ideal.Quotient.lift _ ψ₀ fun p hp => hle hp
  have hψ₁ : ∀ p, ψ₁ (mk d n a p) = ψ₀ p := fun p => rfl
  have hψ₁a : ∀ x, ψ₁ (algebraMap A (Alg d n a) x) = αA x := fun x => by
    rw [← mk_C, hψ₁, eval₂Hom_C]
  let ψ₂ : Bj →+* T := IsLocalization.Away.lift (algebraMap A (Alg d n a) (a j))
    (g := ψ₁) (by rw [hψ₁a]; exact hu)
  have hψ₂ : ∀ y, ψ₂ (algebraMap (Alg d n a) Bj y) = ψ₁ y := fun y =>
    IsLocalization.Away.lift_eq _ _ y
  have hRT : ψ₁.comp (algebraMap R (Alg d n a)) = algebraMap R T := by
    apply MvPolynomial.ringHom_ext
    · intro c
      show ψ₁ (algebraMap R (Alg d n a) (algebraMap k R c)) = algebraMap R T (algebraMap k R c)
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply k A (Alg d n a), hψ₁a]
      show α (algebraMap A _ (algebraMap k A c)) = _
      rw [← IsScalarTower.algebraMap_apply, α.commutes]
      rfl
    · intro i
      show ψ₁ (algebraMap R (Alg d n a) (X i)) = _
      rw [algebraMap_X, hψ₁, eval₂Hom_X']
      rfl
  let ψ : Bj →ₐ[R] T :=
    { ψ₂ with
      commutes' := fun p => by
        show ψ₂ (algebraMap R Bj p) = _
        rw [IsScalarTower.algebraMap_apply R (Alg d n a) Bj, hψ₂]
        exact RingHom.congr_fun hRT p }
  refine ⟨ψ, ?_⟩
  -- compatibility with `φ`
  have hC : ∀ x : A, Ideal.Quotient.mk J (αA x) =
      φ (algebraMap (Alg d n a) Bj (algebraMap A (Alg d n a) x)) := fun x => by
    show Ideal.Quotient.mk J (α (algebraMap A _ x)) = _
    rw [hα]
    show φ (ι (algebraMap A _ x)) = _
    rw [hι]
  have hXl : ∀ i, Ideal.Quotient.mk J (xT i) = φ (xB i) := fun i => by
    show Ideal.Quotient.mk J (algebraMap R T (X i)) = _
    rw [Ideal.Quotient.mk_algebraMap, ← φ.commutes,
      IsScalarTower.algebraMap_apply R (Alg d n a) Bj, algebraMap_X]
  have hε : ∀ i, Ideal.Quotient.mk J (ε i) = 0 := fun i => by
    have h0 : mk d n a (X (Sum.inl i)) ^ n - ∑ l, mk d n a (X (Sum.inr (i, l))) *
        algebraMap A (Alg d n a) (a l) = 0 := sub_eq_zero.mpr (rel_eq d n a i)
    have h1 := congrArg (fun y => φ (algebraMap (Alg d n a) Bj y)) h0
    simp only [map_sub, map_pow, map_sum, map_mul, map_zero] at h1
    simp only [ε, map_sub, map_pow, map_sum, map_mul, hXl, ht, hC]
    exact h1
  have key : (Ideal.Quotient.mk J).comp ψ₀ =
      ((φ : Bj →+* T ⧸ J).comp (algebraMap (Alg d n a) Bj)).comp (mk d n a : _ →+* _) := by
    apply MvPolynomial.ringHom_ext
    · intro x
      simp only [RingHom.coe_comp, Function.comp_apply, ψ₀, eval₂Hom_C, AlgHom.coe_toRingHom,
        mk_C]
      exact hC x
    · rintro (i | p)
      · simp only [RingHom.coe_comp, Function.comp_apply, ψ₀, eval₂Hom_X', val, Sum.elim_inl,
          AlgHom.coe_toRingHom]
        exact hXl i
      · simp only [RingHom.coe_comp, Function.comp_apply, ψ₀, eval₂Hom_X', val, Sum.elim_inr,
          AlgHom.coe_toRingHom, map_add, ht]
        split_ifs
        · rw [map_mul, hε, mul_zero, add_zero]
        · rw [map_zero, add_zero]
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (algebraMap A (Alg d n a) (a j)))
  ext y
  obtain ⟨p, rfl⟩ := mk_surjective d n a y
  have := RingHom.congr_fun key p
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom] at this ⊢
  show Ideal.Quotient.mk J (ψ₂ (algebraMap (Alg d n a) Bj (mk d n a p))) = _
  rw [hψ₂, hψ₁]
  exact this

/-- `Alg_{aⱼ}` is smooth over `k[x]` when `A_{aⱼ}` is smooth over `k`. -/
theorem smooth_away [Algebra.FinitePresentation k A] (j : Fin r)
    [Algebra.Smooth k (Localization.Away (a j))] :
    Algebra.Smooth (MvPolynomial (Fin d) k)
      (Localization.Away (algebraMap A (Alg d n a) (a j))) := by
  have : Algebra.FinitePresentation (Alg d n a)
      (Localization.Away (algebraMap A (Alg d n a) (a j))) :=
    IsLocalization.Away.finitePresentation (S := Localization.Away (algebraMap A (Alg d n a) (a j)))
      (algebraMap A (Alg d n a) (a j))
  exact ⟨formallySmooth_away d n a k j,
    Algebra.FinitePresentation.trans (MvPolynomial (Fin d) k) (Alg d n a) _⟩

end Smooth

section Lift

variable {Λ : Type u} [CommRing Λ] [Algebra k Λ] [Algebra (MvPolynomial (Fin d) k) Λ]
  [IsScalarTower k (MvPolynomial (Fin d) k) Λ]

/-- The map `Alg → Λ` with `xᵢ ↦ πᵢ` and `zᵢⱼ ↦ λᵢⱼ`, where `πᵢⁿ = Σⱼ λᵢⱼ f(aⱼ)`. -/
noncomputable def lift (f : A →ₐ[k] Λ) (π : Fin d → Λ) (lam : Fin d → Fin r → Λ)
    (hπ : ∀ i, π i ^ n = ∑ j, lam i j * f (a j))
    (hX : ∀ i, algebraMap (MvPolynomial (Fin d) k) Λ (X i) = π i) :
    Alg d n a →ₐ[MvPolynomial (Fin d) k] Λ :=
  let ρ₀ : MvPolynomial (Fin d ⊕ (Fin d × Fin r)) A →+* Λ :=
    eval₂Hom f.toRingHom (Sum.elim π fun p => lam p.1 p.2)
  have hle : Ideal.span (Set.range (rel d n a)) ≤ RingHom.ker ρ₀ := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp only [SetLike.mem_coe, RingHom.mem_ker, rel, ρ₀, map_sub, map_pow, map_sum, map_mul,
      eval₂Hom_X', eval₂Hom_C, Sum.elim_inl, Sum.elim_inr, hπ]
    exact sub_self _
  let ρ₁ : Alg d n a →+* Λ := Ideal.Quotient.lift _ ρ₀ fun p hp => hle hp
  { ρ₁ with
    commutes' := fun p => by
      have h : ρ₁.comp (algebraMap (MvPolynomial (Fin d) k) (Alg d n a)) =
          algebraMap (MvPolynomial (Fin d) k) Λ := by
        apply MvPolynomial.ringHom_ext
        · intro c
          show ρ₁ (algebraMap (MvPolynomial (Fin d) k) (Alg d n a) (algebraMap k _ c)) =
            algebraMap (MvPolynomial (Fin d) k) Λ (algebraMap k _ c)
          rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
            IsScalarTower.algebraMap_apply k A (Alg d n a), ← mk_C]
          show ρ₀ (C (algebraMap k A c)) = _
          rw [eval₂Hom_C]
          exact f.commutes c
        · intro i
          show ρ₁ (algebraMap (MvPolynomial (Fin d) k) (Alg d n a) (X i)) = _
          rw [algebraMap_X, hX]
          show ρ₀ (X (Sum.inl i)) = _
          rw [eval₂Hom_X']
          rfl
      exact RingHom.congr_fun h p }

theorem lift_algebraMap (f : A →ₐ[k] Λ) (π : Fin d → Λ) (lam : Fin d → Fin r → Λ)
    (hπ : ∀ i, π i ^ n = ∑ j, lam i j * f (a j))
    (hX : ∀ i, algebraMap (MvPolynomial (Fin d) k) Λ (X i) = π i) (x : A) :
    lift d n a k f π lam hπ hX (algebraMap A (Alg d n a) x) = f x := by
  rw [← mk_C]
  show eval₂Hom f.toRingHom _ (C x) = f x
  rw [eval₂Hom_C]
  rfl

end Lift

end SmoothingAlgebra

end Langlands.CommutativeAlgebra.Popescu
