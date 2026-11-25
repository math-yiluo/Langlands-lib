import Langlands.CommutativeAlgebra.Popescu.Basic
import Langlands.CommutativeAlgebra.Popescu.DimZeroResolutionProof
import Langlands.MathlibBase

/-! # The gluing algebra of Stacks Lemma 9.4 (07FA) -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

open MvPolynomial

namespace DimZeroGlue

variable {A : Type u} [CommRing A] {n m : ℕ} (r : ℕ) (F : Fin m → MvPolynomial (Fin n) A)

/-- The variables `xᵢ` (`i < n`), `yₖ` (`k < r`), `z` and `tₖⱼ`. -/
abbrev V (n m r : ℕ) := Fin n ⊕ (Fin r ⊕ (Unit ⊕ (Fin r × Fin m)))

/-- The variable `xᵢ`. -/
noncomputable def xv (i : Fin n) : MvPolynomial (V n m r) A := X (Sum.inl i)
/-- The variable `yₖ`. -/
noncomputable def yv (k : Fin r) : MvPolynomial (V n m r) A := X (Sum.inr (Sum.inl k))
/-- The variable `z`. -/
noncomputable def zv : MvPolynomial (V n m r) A := X (Sum.inr (Sum.inr (Sum.inl ())))
/-- The variable `tₖⱼ`. -/
noncomputable def tv (k : Fin r) (j : Fin m) : MvPolynomial (V n m r) A :=
  X (Sum.inr (Sum.inr (Sum.inr (k, j))))

/-- The relations `Fⱼ(x) − Σₖ yₖ tₖⱼ` and `z yₖ`. -/
noncomputable def rels : Fin m ⊕ Fin r → MvPolynomial (V n m r) A :=
  Sum.elim (fun j => rename Sum.inl (F j) - ∑ k, yv r k * tv r k j)
    (fun k => zv r * yv r k)

/-- The algebra `A[x, y, z, t]/(Fⱼ(x) − Σₖ yₖ tₖⱼ, z yₖ)`. -/
def Alg : Type u := MvPolynomial (V n m r) A ⧸ Ideal.span (Set.range (rels r F))

noncomputable instance : CommRing (Alg r F) :=
  inferInstanceAs (CommRing (MvPolynomial (V n m r) A ⧸ _))

noncomputable instance (R : Type*) [CommRing R] [Algebra R A] : Algebra R (Alg r F) :=
  inferInstanceAs (Algebra R (MvPolynomial (V n m r) A ⧸ Ideal.span (Set.range (rels r F))))

instance (R : Type*) [CommRing R] [Algebra R A] : IsScalarTower R A (Alg r F) :=
  inferInstanceAs (IsScalarTower R A (MvPolynomial (V n m r) A ⧸ Ideal.span (Set.range (rels r F))))

/-- The quotient map onto `Alg`. -/
noncomputable def mk : MvPolynomial (V n m r) A →ₐ[A] Alg r F := Ideal.Quotient.mkₐ A _

theorem mk_surjective : Function.Surjective (mk r F) := Ideal.Quotient.mkₐ_surjective A _

theorem mk_C (a : A) : mk r F (C a) = algebraMap A (Alg r F) a := (mk r F).commutes a

theorem mk_rels (i) : mk r F (rels r F i) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)

theorem rel1 (j : Fin m) :
    mk r F (rename Sum.inl (F j)) = ∑ k, mk r F (yv r k) * mk r F (tv r k j) := by
  have h := mk_rels r F (Sum.inl j)
  simp only [rels, Sum.elim_inl, map_sub, map_sum, map_mul] at h
  exact sub_eq_zero.mp h

theorem rel2 (k : Fin r) : mk r F (zv r) * mk r F (yv r k) = 0 := by
  have h := mk_rels r F (Sum.inr k)
  simpa [rels] using h

/-- A lift of a unit modulo a square-zero ideal is a unit. -/
theorem isUnit_of_isUnit_mk {T : Type*} [CommRing T] (J : Ideal T) (hJ : J ^ 2 = ⊥) {x : T}
    (h : IsUnit (Ideal.Quotient.mk J x)) : IsUnit x := by
  obtain ⟨w, hw⟩ := h.exists_right_inv
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective w
  have h3 : x * w - 1 ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hw, map_one, sub_self]
  have hz : (x * w - 1) * (x * w - 1) = 0 := by
    have : (x * w - 1) * (x * w - 1) ∈ J ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul h3 h3
    rw [hJ] at this
    exact (Submodule.mem_bot _).mp this
  refine IsUnit.of_mul_eq_one (w * (1 - (x * w - 1))) ?_
  linear_combination (-1 : T) * hz

section SmoothY

variable (R : Type u) [CommRing R] [Algebra R A]

/-- `Alg_{a yₗ}` is formally smooth over `R` when `A_a` is: the relations can be solved for
`tₗⱼ`, and `z = 0`. -/
theorem formallySmooth_away_y (a : A) (l : Fin r)
    [Algebra.FormallySmooth R (Localization.Away a)] :
    Algebra.FormallySmooth R
      (Localization.Away (algebraMap A (Alg r F) a * mk r F (yv r l))) := by
  classical
  set b := algebraMap A (Alg r F) a * mk r F (yv r l)
  set Bj := Localization.Away b
  have hbu : IsUnit (algebraMap (Alg r F) Bj b) := IsLocalization.Away.algebraMap_isUnit b
  have hau : IsUnit (algebraMap (Alg r F) Bj (algebraMap A (Alg r F) a)) :=
    isUnit_of_mul_isUnit_left (by rw [← map_mul]; exact hbu)
  have hyu : IsUnit (algebraMap (Alg r F) Bj (mk r F (yv r l))) :=
    isUnit_of_mul_isUnit_right (by rw [← map_mul]; exact hbu)
  apply Algebra.FormallySmooth.of_comp_surjective
  intro T _ _ J hJ φ
  let ι₀ : Localization.Away a →+* Bj := IsLocalization.Away.lift a
    (g := (algebraMap (Alg r F) Bj).comp (algebraMap A (Alg r F))) hau
  have hι₀ : ∀ x : A, ι₀ (algebraMap A _ x) = algebraMap (Alg r F) Bj (algebraMap A _ x) :=
    fun x => IsLocalization.Away.lift_eq _ _ x
  let ι : Localization.Away a →ₐ[R] Bj :=
    { ι₀ with
      commutes' := fun c => by
        show ι₀ (algebraMap R _ c) = _
        rw [IsScalarTower.algebraMap_apply R A (Localization.Away a), hι₀,
          ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] }
  let α₀ : Localization.Away a →ₐ[R] T ⧸ J := φ.comp ι
  have hJn : IsNilpotent J := ⟨2, hJ⟩
  let α : Localization.Away a →ₐ[R] T := Algebra.FormallySmooth.lift J hJn α₀
  have hα : ∀ y, Ideal.Quotient.mk J (α y) = α₀ y := Algebra.FormallySmooth.mk_lift J hJn α₀
  let αA : A →+* T := α.toRingHom.comp (algebraMap A (Localization.Away a))
  have hαu : IsUnit (αA a) := (IsLocalization.Away.algebraMap_isUnit a).map α
  let elt : V n m r → Bj := fun w => algebraMap (Alg r F) Bj (mk r F (X w))
  choose e he using fun w => Ideal.Quotient.mk_surjective (φ (elt w))
  have hC : ∀ x : A, Ideal.Quotient.mk J (αA x) =
      φ (algebraMap (Alg r F) Bj (algebraMap A (Alg r F) x)) := fun x => by
    show Ideal.Quotient.mk J (α (algebraMap A _ x)) = _
    rw [hα]
    show φ (ι (algebraMap A _ x)) = _
    exact congrArg φ (hι₀ x)
  have hyT : IsUnit (e (Sum.inr (Sum.inl l))) := isUnit_of_isUnit_mk J hJ (by
    rw [he]; exact hyu.map φ)
  let v : T := ↑hyT.unit⁻¹
  have hv : e (Sum.inr (Sum.inl l)) * v = 1 := hyT.mul_val_inv
  let xT : Fin n → T := fun i => e (Sum.inl i)
  let yT : Fin r → T := fun k => e (Sum.inr (Sum.inl k))
  let tT : Fin r → Fin m → T := fun k j => e (Sum.inr (Sum.inr (Sum.inr (k, j))))
  let ε : Fin m → T := fun j => eval₂ αA xT (F j) - ∑ k, yT k * tT k j
  let val : V n m r → T :=
    Sum.elim xT (Sum.elim yT (Sum.elim (fun _ => 0)
      (fun p => tT p.1 p.2 + if p.1 = l then v * ε p.2 else 0)))
  let ψ₀ : MvPolynomial (V n m r) A →+* T := eval₂Hom αA val
  have hψF : ∀ p : MvPolynomial (Fin n) A, ψ₀ (rename Sum.inl p) = eval₂ αA xT p := fun p => by
    show eval₂ αA val (rename Sum.inl p) = _
    rw [eval₂_rename]
    rfl
  have hrel : ∀ i, ψ₀ (rels r F i) = 0 := by
    rintro (j | k)
    · simp only [rels, Sum.elim_inl, map_sub, hψF, map_sum, map_mul, ψ₀, yv, tv, eval₂Hom_X',
        val, Sum.elim_inr, Sum.elim_inl, mul_add, Finset.sum_add_distrib, mul_ite,
        mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      have : yT l * (v * ε j) = ε j := by rw [← mul_assoc, show yT l * v = 1 from hv, one_mul]
      rw [this]
      simp only [ε]
      ring
    · simp [rels, ψ₀, zv, yv, val]
  have hle : Ideal.span (Set.range (rels r F)) ≤ RingHom.ker ψ₀ := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hrel i
  let ψ₁ : Alg r F →+* T := Ideal.Quotient.lift _ ψ₀ fun p hp => hle hp
  have hψ₁ : ∀ p, ψ₁ (mk r F p) = ψ₀ p := fun p => rfl
  have hψ₁a : ∀ x, ψ₁ (algebraMap A (Alg r F) x) = αA x := fun x => by
    rw [← mk_C, hψ₁, eval₂Hom_C]
  have hψ₁b : IsUnit (ψ₁ b) := by
    rw [map_mul, hψ₁a, hψ₁]
    exact hαu.mul (by simpa [ψ₀, yv, val] using hyT)
  let ψ₂ : Bj →+* T := IsLocalization.Away.lift b hψ₁b
  have hψ₂ : ∀ y, ψ₂ (algebraMap (Alg r F) Bj y) = ψ₁ y := fun y =>
    IsLocalization.Away.lift_eq _ _ y
  let ψ : Bj →ₐ[R] T :=
    { ψ₂ with
      commutes' := fun c => by
        show ψ₂ (algebraMap R Bj c) = _
        rw [IsScalarTower.algebraMap_apply R (Alg r F) Bj,
          IsScalarTower.algebraMap_apply R A (Alg r F), hψ₂, hψ₁a]
        show α (algebraMap A _ (algebraMap R A c)) = _
        rw [← IsScalarTower.algebraMap_apply, α.commutes] }
  refine ⟨ψ, ?_⟩
  -- compatibility with `φ`
  have hzB : φ (elt (Sum.inr (Sum.inr (Sum.inl ())))) = 0 := by
    have h2 := congrArg (algebraMap (Alg r F) Bj) (rel2 r F l)
    rw [map_mul, map_zero] at h2
    have : elt (Sum.inr (Sum.inr (Sum.inl ()))) = 0 := (hyu.mul_left_eq_zero).mp h2
    rw [this, map_zero]
  have hev : ∀ p : MvPolynomial (Fin n) A, Ideal.Quotient.mk J (eval₂ αA xT p) =
      φ (algebraMap (Alg r F) Bj (mk r F (rename Sum.inl p))) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C x => simp only [eval₂_C, hC, rename_C, mk_C]
    | add p q hp hq => simp only [eval₂_add, map_add, hp, hq]
    | mul_X p i hp =>
      simp only [eval₂_mul, eval₂_X, map_mul, hp, rename_X]
      congr 1
      exact he (Sum.inl i)
  have hε : ∀ j, Ideal.Quotient.mk J (ε j) = 0 := fun j => by
    have h0 := congrArg (fun y => φ (algebraMap (Alg r F) Bj y)) (sub_eq_zero.mpr (rel1 r F j))
    simp only [map_sub, map_sum, map_mul, map_zero] at h0
    simp only [ε, map_sub, map_sum, map_mul, hev, yT, tT, he]
    exact h0
  have key : (Ideal.Quotient.mk J).comp ψ₀ =
      ((φ : Bj →+* T ⧸ J).comp (algebraMap (Alg r F) Bj)).comp (mk r F : _ →+* _) := by
    apply MvPolynomial.ringHom_ext
    · intro x
      simp only [RingHom.coe_comp, Function.comp_apply, ψ₀, eval₂Hom_C, AlgHom.coe_toRingHom,
        mk_C]
      exact hC x
    · rintro (i | k | ⟨⟩ | p)
      · simp only [RingHom.coe_comp, Function.comp_apply, ψ₀, eval₂Hom_X', val, Sum.elim_inl,
          AlgHom.coe_toRingHom]
        exact he _
      · simp only [RingHom.coe_comp, Function.comp_apply, ψ₀, eval₂Hom_X', val, Sum.elim_inl,
          Sum.elim_inr, AlgHom.coe_toRingHom]
        exact he _
      · simp only [RingHom.coe_comp, Function.comp_apply, ψ₀, eval₂Hom_X', val, Sum.elim_inl,
          Sum.elim_inr, AlgHom.coe_toRingHom, map_zero]
        exact hzB.symm
      · simp only [RingHom.coe_comp, Function.comp_apply, ψ₀, eval₂Hom_X', val, Sum.elim_inr,
          AlgHom.coe_toRingHom, map_add, tT, he]
        split_ifs
        · rw [map_mul, hε, mul_zero, add_zero]
        · rw [map_zero, add_zero]
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers b)
  ext y
  obtain ⟨p, rfl⟩ := mk_surjective r F y
  have := RingHom.congr_fun key p
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom] at this ⊢
  show Ideal.Quotient.mk J (ψ₂ (algebraMap (Alg r F) Bj (mk r F p))) = _
  rw [hψ₂, hψ₁]
  exact this

end SmoothY

section SmoothZ

variable (R : Type u) [CommRing R] [Algebra R A] {C : Type u} [CommRing C] [Algebra A C]
  [Algebra R C] [IsScalarTower R A C] (φC : MvPolynomial (Fin n) A →ₐ[A] C)
  (hφC : Function.Surjective φC) (hker : RingHom.ker φC = Ideal.span (Set.range F))

include hφC hker in
/-- `Alg_{z c}` is formally smooth over `R` when `C_c` is, where `C = A[x]/(F)`: inverting `z`
kills the `yₖ`, so `Alg_z = C[z, z⁻¹, t]`. -/
theorem formallySmooth_away_z (c : MvPolynomial (Fin n) A)
    [Algebra.FormallySmooth R (Localization.Away (φC c))] :
    Algebra.FormallySmooth R
      (Localization.Away (mk r F (zv r) * mk r F (rename Sum.inl c))) := by
  classical
  set b := mk r F (zv r) * mk r F (rename Sum.inl c)
  set Bj := Localization.Away b
  set Cc := Localization.Away (φC c)
  have hbu : IsUnit (algebraMap (Alg r F) Bj b) := IsLocalization.Away.algebraMap_isUnit b
  have hzu : IsUnit (algebraMap (Alg r F) Bj (mk r F (zv r))) :=
    isUnit_of_mul_isUnit_left (by rw [← map_mul]; exact hbu)
  have hcu : IsUnit (algebraMap (Alg r F) Bj (mk r F (rename Sum.inl c))) :=
    isUnit_of_mul_isUnit_right (by rw [← map_mul]; exact hbu)
  have hy0 : ∀ k, algebraMap (Alg r F) Bj (mk r F (yv r k)) = 0 := fun k => by
    have h2 := congrArg (algebraMap (Alg r F) Bj) (rel2 r F k)
    rw [map_mul, map_zero] at h2
    exact (hzu.mul_right_eq_zero).mp h2
  -- the map `C → Bj`
  let θ : MvPolynomial (Fin n) A →ₐ[A] Bj :=
    (IsScalarTower.toAlgHom A (Alg r F) Bj).comp ((mk r F).comp (rename Sum.inl))
  have hθker : RingHom.ker φC.toRingHom ≤ RingHom.ker θ.toRingHom := by
    show RingHom.ker φC ≤ _
    rw [hker, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    show algebraMap (Alg r F) Bj (mk r F (rename Sum.inl (F j))) = 0
    rw [rel1, map_sum]
    exact Finset.sum_eq_zero fun k _ => by rw [map_mul, hy0, zero_mul]
  let κ : C →ₐ[A] Bj := AlgHom.liftOfSurjective φC hφC θ hθker
  have hκ : ∀ p, κ (φC p) = algebraMap (Alg r F) Bj (mk r F (rename Sum.inl p)) := fun p =>
    AlgHom.liftOfSurjective_apply φC hφC θ hθker p
  have hκc : IsUnit (κ (φC c)) := by rw [hκ]; exact hcu
  let κ₀ : Cc →+* Bj := IsLocalization.Away.lift (φC c) (g := κ.toRingHom) hκc
  have hκ₀ : ∀ y, κ₀ (algebraMap C Cc y) = κ y := fun y => IsLocalization.Away.lift_eq _ _ y
  let κ' : Cc →ₐ[R] Bj :=
    { κ₀ with
      commutes' := fun x => by
        show κ₀ (algebraMap R Cc x) = _
        rw [IsScalarTower.algebraMap_apply R C Cc, hκ₀, IsScalarTower.algebraMap_apply R A C,
          κ.commutes]
        exact (IsScalarTower.algebraMap_apply R A Bj x).symm }
  apply Algebra.FormallySmooth.of_comp_surjective
  intro T _ _ J hJ φ
  let α₀ : Cc →ₐ[R] T ⧸ J := φ.comp κ'
  have hJn : IsNilpotent J := ⟨2, hJ⟩
  let α : Cc →ₐ[R] T := Algebra.FormallySmooth.lift J hJn α₀
  have hα : ∀ y, Ideal.Quotient.mk J (α y) = α₀ y := Algebra.FormallySmooth.mk_lift J hJn α₀
  let αC : C →+* T := α.toRingHom.comp (algebraMap C Cc)
  let αA : A →+* T := αC.comp (algebraMap A C)
  let elt : V n m r → Bj := fun w => algebraMap (Alg r F) Bj (mk r F (X w))
  choose e he using fun w => Ideal.Quotient.mk_surjective (φ (elt w))
  have hzT : IsUnit (e (Sum.inr (Sum.inr (Sum.inl ())))) := isUnit_of_isUnit_mk J hJ (by
    rw [he]; exact hzu.map φ)
  let val : V n m r → T :=
    Sum.elim (fun i => αC (φC (X i))) (Sum.elim (fun _ => 0) (Sum.elim
      (fun _ => e (Sum.inr (Sum.inr (Sum.inl ())))) (fun p => e (Sum.inr (Sum.inr (Sum.inr p))))))
  let ψ₀ : MvPolynomial (V n m r) A →+* T := eval₂Hom αA val
  have hψF : ∀ p : MvPolynomial (Fin n) A, ψ₀ (rename Sum.inl p) = αC (φC p) := fun p => by
    show eval₂ αA val (rename Sum.inl p) = _
    rw [eval₂_rename]
    have h : (eval₂Hom αA (val ∘ Sum.inl) : MvPolynomial (Fin n) A →+* T) =
        αC.comp (φC : MvPolynomial (Fin n) A →+* C) := by
      apply MvPolynomial.ringHom_ext
      · intro x
        simp [αA, eval₂Hom_C]
      · intro i
        simp [val]
    exact RingHom.congr_fun h p
  have hrel : ∀ i, ψ₀ (rels r F i) = 0 := by
    rintro (j | k)
    · have hFj : φC (F j) = 0 := by
        have : F j ∈ RingHom.ker φC := by rw [hker]; exact Ideal.subset_span ⟨j, rfl⟩
        exact this
      simp only [rels, Sum.elim_inl, map_sub, hψF, hFj, map_zero, map_sum, map_mul, ψ₀, yv,
        eval₂Hom_X', val, Sum.elim_inr, Sum.elim_inl, zero_mul, Finset.sum_const_zero,
        sub_zero]
    · simp [rels, ψ₀, zv, yv, val]
  have hle : Ideal.span (Set.range (rels r F)) ≤ RingHom.ker ψ₀ := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hrel i
  let ψ₁ : Alg r F →+* T := Ideal.Quotient.lift _ ψ₀ fun p hp => hle hp
  have hψ₁ : ∀ p, ψ₁ (mk r F p) = ψ₀ p := fun p => rfl
  have hψ₁a : ∀ x, ψ₁ (algebraMap A (Alg r F) x) = αA x := fun x => by
    rw [← mk_C, hψ₁, eval₂Hom_C]
  have hψ₁b : IsUnit (ψ₁ b) := by
    rw [map_mul, hψ₁, hψ₁, hψF]
    refine IsUnit.mul (by simpa [ψ₀, zv, val] using hzT) ?_
    exact (IsLocalization.Away.algebraMap_isUnit (φC c)).map α
  let ψ₂ : Bj →+* T := IsLocalization.Away.lift b hψ₁b
  have hψ₂ : ∀ y, ψ₂ (algebraMap (Alg r F) Bj y) = ψ₁ y := fun y =>
    IsLocalization.Away.lift_eq _ _ y
  let ψ : Bj →ₐ[R] T :=
    { ψ₂ with
      commutes' := fun x => by
        show ψ₂ (algebraMap R Bj x) = _
        rw [IsScalarTower.algebraMap_apply R (Alg r F) Bj,
          IsScalarTower.algebraMap_apply R A (Alg r F), hψ₂, hψ₁a]
        show α (algebraMap C Cc (algebraMap A C (algebraMap R A x))) = _
        rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, α.commutes] }
  refine ⟨ψ, ?_⟩
  have hκ'C : ∀ p, κ' (algebraMap C Cc (φC p)) =
      algebraMap (Alg r F) Bj (mk r F (rename Sum.inl p)) := fun p => by
    show κ₀ _ = _
    rw [hκ₀, hκ]
  have hX : ∀ p : MvPolynomial (Fin n) A, Ideal.Quotient.mk J (αC (φC p)) =
      φ (algebraMap (Alg r F) Bj (mk r F (rename Sum.inl p))) := fun p => by
    show Ideal.Quotient.mk J (α _) = _
    rw [hα]
    show φ (κ' _) = _
    rw [hκ'C]
  have key : (Ideal.Quotient.mk J).comp ψ₀ =
      ((φ : Bj →+* T ⧸ J).comp (algebraMap (Alg r F) Bj)).comp (mk r F : _ →+* _) := by
    apply MvPolynomial.ringHom_ext
    · intro x
      have h := hX (MvPolynomial.C x)
      simp only [rename_C, mk_C] at h
      simp only [RingHom.coe_comp, Function.comp_apply, ψ₀, eval₂Hom_C, AlgHom.coe_toRingHom,
        mk_C, αA]
      rw [← h, ← MvPolynomial.algebraMap_eq, φC.commutes]
    · rintro (i | k | ⟨⟩ | p)
      · simp only [RingHom.coe_comp, Function.comp_apply, ψ₀, eval₂Hom_X', val, Sum.elim_inl,
          AlgHom.coe_toRingHom]
        have h := hX (X i)
        rwa [rename_X] at h
      · simp only [RingHom.coe_comp, Function.comp_apply, ψ₀, eval₂Hom_X', val, Sum.elim_inl,
          Sum.elim_inr, AlgHom.coe_toRingHom, map_zero]
        rw [show (X (Sum.inr (Sum.inl k)) : MvPolynomial (V n m r) A) = yv r k from rfl, hy0,
          map_zero]
      · simp only [RingHom.coe_comp, Function.comp_apply, ψ₀, eval₂Hom_X', val, Sum.elim_inl,
          Sum.elim_inr, AlgHom.coe_toRingHom]
        exact he _
      · simp only [RingHom.coe_comp, Function.comp_apply, ψ₀, eval₂Hom_X', val, Sum.elim_inr,
          AlgHom.coe_toRingHom]
        exact he _
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers b)
  ext y
  obtain ⟨p, rfl⟩ := mk_surjective r F y
  have := RingHom.congr_fun key p
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom] at this ⊢
  show Ideal.Quotient.mk J (ψ₂ (algebraMap (Alg r F) Bj (mk r F p))) = _
  rw [hψ₂, hψ₁]
  exact this

end SmoothZ

end DimZeroGlue

open DimZeroGlue in
/-- Stacks Lemma 9.4 (07FA), from a factorization `A → C → Λ` with `H_{C/R}Λ ⊄ q`. -/
theorem canBeResolved_of_dimZero {R A Λ : Type u} [CommRing R] [IsNoetherianRing R] [CommRing A]
    [CommRing Λ] [IsNoetherianRing Λ] [Algebra R A] [Algebra R Λ] [Algebra.FinitePresentation R A]
    (f : A →ₐ[R] Λ) (q : Ideal Λ) [q.IsPrime] (hle : singularRadical R f ≤ q)
    (hmin : q ∈ minimalPrimes Λ) (C : Type u) [CommRing C] [Algebra R C]
    [Algebra.FinitePresentation R C] (gC : A →ₐ[R] C) (hC : C →ₐ[R] Λ) (hgh : hC.comp gC = f)
    (hCq : ¬ (singularIdeal R C).map hC ≤ q) : CanBeResolved R f q := by
  classical
  -- generators of the singular ideal of `A`
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (singularIdeal R A))
  have ha' : Ideal.span (Set.range a) = singularIdeal R A := ha
  have ha_mem : ∀ k, a k ∈ singularIdeal R A := fun k => by
    rw [← ha']; exact Ideal.subset_span ⟨k, rfl⟩
  -- the maximal ideal of `Λ_q` is nilpotent
  set L := Localization.AtPrime q
  have hnil : nilradical L = IsLocalRing.maximalIdeal L := by
    apply le_antisymm
    · exact nilradical_le_prime _
    · rw [nilradical, Ideal.radical_eq_sInf]
      refine le_sInf ?_
      rintro P ⟨-, hP⟩
      have h1 : P.comap (algebraMap Λ L) = q := by
        have hle' : P.comap (algebraMap Λ L) ≤ q := by
          have := Ideal.comap_mono (f := algebraMap Λ L) (IsLocalRing.le_maximalIdeal hP.ne_top)
          have h2 : Ideal.comap (algebraMap Λ L) (IsLocalRing.maximalIdeal L) = q :=
            Localization.AtPrime.under_maximalIdeal
          rwa [h2] at this
        exact le_antisymm hle' (hmin.2 ⟨Ideal.IsPrime.comap _, bot_le⟩ hle')
      have h1' : Ideal.under Λ P = q := h1
      rw [← IsLocalization.map_under q.primeCompl L P, h1',
        Localization.AtPrime.map_eq_maximalIdeal]
  obtain ⟨N, hN⟩ := IsNoetherianRing.isNilpotent_nilradical L
  rw [hnil] at hN
  -- an element `λ ∉ q` killing `f(aₖ)ᴺ`
  have hfa : ∀ k, f (a k) ∈ q := fun k =>
    hle (Ideal.le_radical (Ideal.mem_map_of_mem f (ha_mem k)))
  have hlam : ∀ k, ∃ l ∉ q, l * f (a k) ^ N = 0 := fun k => by
    have h1 : algebraMap Λ L (f (a k)) ∈ IsLocalRing.maximalIdeal L := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal]; exact Ideal.mem_map_of_mem _ (hfa k)
    have h2 : algebraMap Λ L (f (a k) ^ N) = 0 := by
      rw [map_pow, ← Ideal.mem_bot, ← Submodule.zero_eq_bot, ← hN]
      exact Ideal.pow_mem_pow h1 N
    obtain ⟨⟨l, hl⟩, hl'⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl L _).mp h2
    exact ⟨l, hl, hl'⟩
  choose l hlq hl using hlam
  set lam := ∏ k, l k
  have hlamq : lam ∉ q := by
    rw [show lam = ∏ k ∈ Finset.univ, l k from rfl]
    exact fun h => by
      obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp h
      exact hlq k hk
  have hlam0 : ∀ k, lam * f (a k) ^ N = 0 := fun k => by
    rw [show lam = l k * ∏ i ∈ Finset.univ.erase k, l i from
      (Finset.mul_prod_erase _ _ (Finset.mem_univ k)).symm, mul_comm (l k), mul_assoc, hl, mul_zero]
  -- a presentation of `C` over `A`
  let _ : Algebra A C := gC.toAlgebra
  have : IsScalarTower R A C := .of_algebraMap_eq fun x => (gC.commutes x).symm
  have : Algebra.FinitePresentation A C :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R A C
  obtain ⟨n, φ, hφ, hφfg⟩ := Algebra.FinitePresentation.out (R := A) (A := C)
  obtain ⟨m, F, hF⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hφfg
  have hker : RingHom.ker φ = Ideal.span (Set.range F) := hF.symm
  -- the gluing algebra
  set B := Alg r F
  have : Algebra.FinitePresentation A B :=
    show Algebra.FinitePresentation A
      (MvPolynomial (V n m r) A ⧸ Ideal.span (Set.range (rels r F))) from
    Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range _))
  have : Algebra.FinitePresentation R B := Algebra.FinitePresentation.trans R A B
  have hφC : ∀ p, hC (φ p) = eval₂ f.toRingHom (fun i => hC (φ (X i))) p := by
    intro p
    have h : (hC.toRingHom.comp (φ : MvPolynomial (Fin n) A →+* C)) =
        eval₂Hom f.toRingHom (fun i => hC (φ (X i))) := by
      apply MvPolynomial.ringHom_ext
      · intro x
        simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom, eval₂Hom_C]
        rw [← MvPolynomial.algebraMap_eq, φ.commutes]
        exact AlgHom.congr_fun hgh x
      · intro i
        simp
    exact RingHom.congr_fun h p
  let val : V n m r → Λ :=
    Sum.elim (fun i => hC (φ (X i))) (Sum.elim (fun k => f (a k) ^ N)
      (Sum.elim (fun _ => lam) (fun _ => 0)))
  let ρ₀ : MvPolynomial (V n m r) A →+* Λ := eval₂Hom f.toRingHom val
  have hρF : ∀ p : MvPolynomial (Fin n) A, ρ₀ (rename Sum.inl p) = hC (φ p) := fun p => by
    show eval₂ _ val (rename Sum.inl p) = _
    rw [eval₂_rename, hφC]
    rfl
  have hrel : ∀ i, ρ₀ (rels r F i) = 0 := by
    rintro (j | k)
    · have hFj : φ (F j) = 0 := by
        have : F j ∈ RingHom.ker φ := by rw [hker]; exact Ideal.subset_span ⟨j, rfl⟩
        exact this
      simp only [rels, Sum.elim_inl, map_sub, hρF, hFj, map_zero, map_sum, map_mul, ρ₀, yv, tv,
        eval₂Hom_X', val, Sum.elim_inr, Sum.elim_inl, mul_zero, Finset.sum_const_zero, sub_zero]
    · simp only [rels, Sum.elim_inr, map_mul, ρ₀, zv, yv, eval₂Hom_X', val, Sum.elim_inl]
      exact hlam0 k
  have hle' : Ideal.span (Set.range (rels r F)) ≤ RingHom.ker ρ₀ := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hrel i
  let ρ₁ : B →+* Λ := Ideal.Quotient.lift _ ρ₀ fun p hp => hle' hp
  have hρ₁ : ∀ p, ρ₁ (mk r F p) = ρ₀ p := fun p => rfl
  have hρ₁a : ∀ x, ρ₁ (algebraMap A B x) = f x := fun x => by
    rw [← mk_C, hρ₁, eval₂Hom_C]
    rfl
  let h : B →ₐ[R] Λ :=
    { ρ₁ with
      commutes' := fun x => by
        show ρ₁ (algebraMap R B x) = _
        rw [IsScalarTower.algebraMap_apply R A B, hρ₁a, f.commutes] }
  let g : A →ₐ[R] B := IsScalarTower.toAlgHom R A B
  have hgh' : h.comp g = f := by
    ext x
    exact hρ₁a x
  have hsmooth : ∀ b : B, Algebra.FormallySmooth R (Localization.Away b) →
      b ∈ singularIdeal R B := fun b hb => by
    have : Algebra.FinitePresentation B (Localization.Away b) :=
      IsLocalization.Away.finitePresentation b
    have : Algebra.FinitePresentation R (Localization.Away b) :=
      Algebra.FinitePresentation.trans R B _
    exact DimZeroResolutionProof.mem_singularIdeal_of_smooth b ⟨hb, inferInstance⟩
  refine ⟨B, inferInstance, inferInstance, inferInstance, g, h, hgh', ?_, ?_⟩
  · -- `h_A ⊆ h_B`
    show ((singularIdeal R A).map f).radical ≤ _
    refine (Ideal.radical_mono ?_).trans (Ideal.radical_isRadical _)
    rw [← ha', Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    have : Algebra.Smooth R (Localization.Away (a k)) := DimZeroResolutionProof.smooth_away_of_mem_singularIdeal (ha_mem k)
    have hb := hsmooth _ (formallySmooth_away_y r F R (a k) k)
    have h1 := Ideal.mem_map_of_mem h hb
    have h2 : h (algebraMap A B (a k) * mk r F (yv r k)) = f (a k) ^ (N + 1) := by
      rw [map_mul]
      show ρ₁ _ * ρ₁ _ = _
      rw [hρ₁a, hρ₁]
      simp only [ρ₀, yv, eval₂Hom_X', val, Sum.elim_inr, Sum.elim_inl]
      ring
    rw [h2] at h1
    exact ⟨N + 1, h1⟩
  · -- `h_B ⊄ q`
    intro hBq
    apply hCq
    rw [Ideal.map_le_iff_le_comap]
    intro c hc
    rw [Ideal.mem_comap]
    by_contra hcq
    obtain ⟨cc, rfl⟩ := hφ c
    have : Algebra.Smooth R (Localization.Away (φ cc)) := DimZeroResolutionProof.smooth_away_of_mem_singularIdeal hc
    have hb := hsmooth _ (formallySmooth_away_z r F R φ hφ hker cc)
    have h1 := hBq (Ideal.le_radical (Ideal.mem_map_of_mem h hb))
    have h2 : h (mk r F (zv r) * mk r F (rename Sum.inl cc)) = lam * hC (φ cc) := by
      rw [map_mul]
      show ρ₁ _ * ρ₁ _ = _
      rw [hρ₁, hρ₁, hρF]
      simp only [ρ₀, zv, eval₂Hom_X', val, Sum.elim_inr, Sum.elim_inl]
    rw [h2] at h1
    rcases (‹q.IsPrime›.mem_or_mem h1) with h3 | h3
    · exact hlamq h3
    · exact hcq h3

end Langlands.CommutativeAlgebra.Popescu
