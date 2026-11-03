import Langlands.CommutativeAlgebra.IntegralFibre.Model
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Basic

/-! # The diagonal section over a localization -/

open TensorProduct

namespace Langlands.CommutativeAlgebra.IntegralFibre

section Diagonal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (s : S)

/-- The diagonal section `B ⊗[R] S → B` for `B = S[1/s]`. -/
noncomputable def diagSection : Localization.Away s ⊗[R] S →ₐ[Localization.Away s]
    Localization.Away s :=
  Algebra.TensorProduct.lift (AlgHom.id _ _) (IsScalarTower.toAlgHom R S (Localization.Away s))
    (fun _ _ ↦ Commute.all _ _)

@[simp]
lemma diagSection_tmul (b : Localization.Away s) (x : S) :
    diagSection s (b ⊗ₜ[R] x) = b * algebraMap S _ x := by
  simp [diagSection]

/-- The differential along the diagonal section, `b ⊗ x ↦ b • dx`. -/
noncomputable def diagDiff : Localization.Away s ⊗[R] S →ₗ[Localization.Away s]
    Ω[Localization.Away s⁄R] :=
  ((KaehlerDifferential.map R R S (Localization.Away s)).restrictScalars R).liftBaseChange _ ∘ₗ
    (KaehlerDifferential.D R S).toLinearMap.baseChange _

@[simp]
lemma diagDiff_tmul (b : Localization.Away s) (x : S) :
    diagDiff s (b ⊗ₜ[R] x) = b • KaehlerDifferential.D R _ (algebraMap S _ x) := by
  simp [diagDiff, KaehlerDifferential.map_D]

lemma diagDiff_mul (x y : Localization.Away s ⊗[R] S) :
    diagDiff s (x * y) = diagSection s x • diagDiff s y + diagSection s y • diagDiff s x := by
  induction x with
  | add x x' hx hx' => simp only [add_mul, map_add, hx, hx', add_smul, smul_add]; abel
  | tmul b u =>
    induction y with
    | add y y' hy hy' => simp only [mul_add, map_add, hy, hy', smul_add, add_smul]; abel
    | tmul b' u' =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, diagDiff_tmul, diagSection_tmul, map_mul,
        Derivation.leibniz, smul_add, smul_smul]
      congr 1 <;> ring_nf

lemma diagDiff_one : diagDiff (R := R) s 1 = 0 := by
  rw [Algebra.TensorProduct.one_def, diagDiff_tmul, map_one, Derivation.map_one_eq_zero, smul_zero]

lemma diagDiff_algebraMap (b : Localization.Away s) :
    diagDiff (R := R) s (algebraMap _ _ b) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, diagDiff_one, smul_zero]

/-- The diagonal differential is surjective. -/
lemma diagDiff_surjective : Function.Surjective (diagDiff (R := R) s) := by
  have h1 : ∀ ω : Ω[S⁄R], KaehlerDifferential.map R R S (Localization.Away s) ω ∈
      LinearMap.range (diagDiff (R := R) s) := by
    intro ω
    have hω : ω ∈ Submodule.span S (Set.range (KaehlerDifferential.D R S)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    induction hω using Submodule.span_induction with
    | mem ω hω =>
      obtain ⟨x, rfl⟩ := hω
      exact ⟨1 ⊗ₜ x, by rw [diagDiff_tmul, one_smul, KaehlerDifferential.map_D]⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add ω ω' _ _ h h' => rw [map_add]; exact Submodule.add_mem _ h h'
    | smul c ω _ h =>
      rw [map_smul, ← algebraMap_smul (Localization.Away s)]
      exact Submodule.smul_mem _ _ h
  intro ω'
  obtain ⟨⟨ω, t⟩, rfl⟩ := IsLocalizedModule.mk'_surjective (Submonoid.powers s)
    (KaehlerDifferential.map R R S (Localization.Away s)) ω'
  have hu : IsUnit (algebraMap S (Localization.Away s) t) := IsLocalization.map_units _ t
  have key : (algebraMap S (Localization.Away s) t) •
      IsLocalizedModule.mk' (KaehlerDifferential.map R R S (Localization.Away s)) ω t =
      KaehlerDifferential.map R R S (Localization.Away s) ω := by
    rw [algebraMap_smul]
    exact IsLocalizedModule.mk'_cancel' (f := KaehlerDifferential.map R R S (Localization.Away s)) ω t
  have h2 := h1 ω
  rw [← key] at h2
  have := Submodule.smul_mem (LinearMap.range (diagDiff (R := R) s)) (hu.unit⁻¹ : _) h2
  rw [smul_smul, hu.val_inv_mul, one_smul] at this
  exact this

/-- The element `1 ⊗ x - x ⊗ 1` of the kernel of the diagonal section. -/
noncomputable def diagDelta (x : S) : Localization.Away s ⊗[R] S :=
  (1 : Localization.Away s) ⊗ₜ x - algebraMap S (Localization.Away s) x ⊗ₜ 1

lemma diagDelta_mem (x : S) : diagDelta (R := R) s x ∈ RingHom.ker (diagSection (R := R) s) := by
  simp [diagDelta]

lemma diagDiff_diagDelta (x : S) :
    diagDiff (R := R) s (diagDelta s x) = KaehlerDifferential.D R _ (algebraMap S _ x) := by
  simp [diagDelta]

lemma eq_sum_diagDelta (j : Localization.Away s ⊗[R] S) (hj : j ∈ RingHom.ker (diagSection (R := R) s)) :
    ∃ (K : ℕ) (b : Fin K → Localization.Away s) (x : Fin K → S),
      j = ∑ k, algebraMap _ (Localization.Away s ⊗[R] S) (b k) * diagDelta s (x k) := by
  obtain ⟨K, b, x, rfl⟩ := TensorProduct.exists_sum_tmul_eq j
  refine ⟨K, b, x, ?_⟩
  have h0 : ∑ k, b k * algebraMap S (Localization.Away s) (x k) = 0 := by
    simpa [map_sum] using hj
  simp only [diagDelta, mul_sub, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
    Finset.sum_sub_distrib]
  rw [← TensorProduct.sum_tmul, h0, TensorProduct.zero_tmul, sub_zero]

lemma toCotangent_smul' {T A : Type*} [CommRing T] [CommRing A] [Algebra A T] (I : Ideal T)
    (a : A) (x : I) : a • I.toCotangent x = I.toCotangent (a • x) := rfl

lemma diagDelta_smul (r : R) (x : S) : diagDelta (R := R) s (r • x) = r • diagDelta s x := by
  simp only [diagDelta, smul_sub, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  congr 2
  rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, Algebra.smul_def]

lemma diagDelta_add (x y : S) :
    diagDelta (R := R) s (x + y) = diagDelta s x + diagDelta s y := by
  simp only [diagDelta, TensorProduct.tmul_add, map_add, TensorProduct.add_tmul]
  abel

/-- The derivation `x ↦ [1 ⊗ x - x ⊗ 1]` into the conormal module of the diagonal. -/
noncomputable def diagDer : Derivation R S (RingHom.ker (diagSection (R := R) s)).Cotangent :=
  Derivation.mk'
    { toFun := fun x ↦ (RingHom.ker (diagSection (R := R) s)).toCotangent ⟨diagDelta s x, diagDelta_mem s x⟩
      map_add' := fun x y ↦ by
        rw [← map_add]
        congr 1
        exact Subtype.ext (diagDelta_add s x y)
      map_smul' := fun r x ↦ by
        rw [RingHom.id_apply, toCotangent_smul']
        congr 1
        exact Subtype.ext (diagDelta_smul s r x) }
    (by
      intro x y
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [toCotangent_smul', toCotangent_smul', ← map_add, Ideal.toCotangent_eq]
      simp only [Submodule.coe_add, Submodule.coe_smul_of_tower]
      have hsm : ∀ (a : S) (z : Localization.Away s ⊗[R] S),
          a • z = algebraMap S (Localization.Away s ⊗[R] S) a * z := fun a z ↦ Algebra.smul_def a z
      have e : diagDelta (R := R) s (x * y) - (x • diagDelta s y + y • diagDelta s x) =
          diagDelta s x * diagDelta s y := by
        rw [hsm, hsm]
        simp only [diagDelta, Algebra.TensorProduct.algebraMap_apply, map_mul]
        rw [show (1 : Localization.Away s) ⊗ₜ[R] (x * y) = (1 ⊗ₜ x) * (1 ⊗ₜ y) by simp,
          show (algebraMap S (Localization.Away s) x * algebraMap S (Localization.Away s) y) ⊗ₜ[R]
            (1 : S) = (algebraMap S _ x ⊗ₜ 1) * (algebraMap S _ y ⊗ₜ 1) by simp]
        ring
      rw [e, pow_two]
      exact Ideal.mul_mem_mul (diagDelta_mem s x) (diagDelta_mem s y))

lemma diagDer_apply (x : S) : diagDer (R := R) s x =
    (RingHom.ker (diagSection (R := R) s)).toCotangent ⟨diagDelta s x, diagDelta_mem s x⟩ := rfl

lemma diagCotangent_isUnit (x : Submonoid.powers s) :
    IsUnit (algebraMap S (Module.End S (RingHom.ker (diagSection (R := R) s)).Cotangent) x) := by
  have hu : IsUnit (algebraMap S (Localization.Away s) x) := IsLocalization.map_units _ x
  rw [Module.End.isUnit_iff]
  constructor
  · intro c c' hc
    rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply,
      ← algebraMap_smul (Localization.Away s) (x : S) c,
      ← algebraMap_smul (Localization.Away s) (x : S) c'] at hc
    exact hu.smul_left_cancel.mp hc
  · intro c
    refine ⟨(hu.unit⁻¹ : (Localization.Away s)ˣ) • c, ?_⟩
    rw [Module.algebraMap_end_apply, ← algebraMap_smul (Localization.Away s) (x : S),
      Units.smul_def, smul_smul, hu.mul_val_inv, one_smul]

/-- The comparison map `Ω_B → J/J²` sending `d x` to `[1 ⊗ x - x ⊗ 1]`. -/
noncomputable def diagConormal : Ω[Localization.Away s⁄R] →ₗ[Localization.Away s]
    (RingHom.ker (diagSection (R := R) s)).Cotangent :=
  (IsLocalizedModule.lift (Submonoid.powers s)
    (KaehlerDifferential.map R R S (Localization.Away s))
    (diagDer (R := R) s).liftKaehlerDifferential (diagCotangent_isUnit s)).extendScalarsOfIsLocalization
    (Submonoid.powers s) (Localization.Away s)

lemma diagConormal_D (x : S) :
    diagConormal (R := R) s (KaehlerDifferential.D R _ (algebraMap S _ x)) = diagDer s x := by
  rw [← KaehlerDifferential.map_D R R S (Localization.Away s) x, diagConormal,
    LinearMap.extendScalarsOfIsLocalization_apply', IsLocalizedModule.lift_apply,
    Derivation.liftKaehlerDifferential_comp_D]

lemma toCotangent_eq_diagConormal (j : Localization.Away s ⊗[R] S)
    (hj : j ∈ RingHom.ker (diagSection (R := R) s)) :
    (RingHom.ker (diagSection (R := R) s)).toCotangent ⟨j, hj⟩ = diagConormal s (diagDiff s j) := by
  obtain ⟨K, b, x, rfl⟩ := eq_sum_diagDelta s j hj
  have hsum : (⟨∑ k, algebraMap _ (Localization.Away s ⊗[R] S) (b k) * diagDelta s (x k), hj⟩ :
      RingHom.ker (diagSection (R := R) s)) =
      ∑ k, b k • (⟨diagDelta s (x k), diagDelta_mem s (x k)⟩ :
        RingHom.ker (diagSection (R := R) s)) := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]
    exact Finset.sum_congr rfl fun k _ ↦ (Algebra.smul_def _ _).symm
  rw [hsum, map_sum]
  have hterm : ∀ k, algebraMap _ (Localization.Away s ⊗[R] S) (b k) * diagDelta s (x k) =
      b k • diagDelta (R := R) s (x k) := fun k ↦ (Algebra.smul_def _ _).symm
  simp only [hterm, map_sum, map_smul, diagDiff_diagDelta, diagConormal_D, ← toCotangent_smul',
    diagDer_apply]

lemma mem_sq_of_diagDiff_eq_zero (j : Localization.Away s ⊗[R] S)
    (hj : j ∈ RingHom.ker (diagSection (R := R) s)) (h : diagDiff s j = 0) :
    j ∈ RingHom.ker (diagSection (R := R) s) ^ 2 :=
  (Ideal.toCotangent_eq_zero _ ⟨j, hj⟩).mp (by rw [toCotangent_eq_diagConormal, h, map_zero])

section Coordinates

variable [Module.Free (Localization.Away s) Ω[Localization.Away s⁄R]]
  [Module.Finite (Localization.Away s) Ω[Localization.Away s⁄R]]

/-- The number of coordinates. -/
noncomputable abbrev diagDim : ℕ :=
  Fintype.card (Module.Free.ChooseBasisIndex (Localization.Away s) Ω[Localization.Away s⁄R])

/-- A basis of `Ω_B`. -/
noncomputable def diagBasis :
    Module.Basis (Fin (diagDim (R := R) s)) (Localization.Away s) Ω[Localization.Away s⁄R] :=
  (Module.Free.chooseBasis _ _).reindex (Fintype.equivFin _)

/-- Coordinates of the diagonal differential. -/
noncomputable def diagCoord : Localization.Away s ⊗[R] S →ₗ[Localization.Away s]
    (Fin (diagDim (R := R) s) → Localization.Away s) :=
  (diagBasis (R := R) s).equivFun.toLinearMap ∘ₗ diagDiff s

lemma diagCoord_mul (x y : Localization.Away s ⊗[R] S) :
    diagCoord (R := R) s (x * y) =
      diagSection s x • diagCoord s y + diagSection s y • diagCoord s x := by
  simp only [diagCoord, LinearMap.coe_comp, Function.comp_apply, diagDiff_mul, map_add, map_smul,
    LinearEquiv.coe_coe]

/-- Coordinates `t_i` in the kernel of the section with `d t_i` the basis of `Ω_B`. -/
noncomputable def diagT (i : Fin (diagDim (R := R) s)) : Localization.Away s ⊗[R] S :=
  (diagDiff_surjective (R := R) s (diagBasis s i)).choose -
    algebraMap _ _ (diagSection s (diagDiff_surjective (R := R) s (diagBasis s i)).choose)

lemma diagSection_diagT (i) : diagSection (R := R) s (diagT s i) = 0 := by
  simp [diagT]

lemma diagCoord_diagT (i) : diagCoord (R := R) s (diagT s i) = Pi.single i 1 := by
  simp only [diagCoord, diagT, LinearMap.coe_comp, Function.comp_apply, map_sub,
    diagDiff_algebraMap, (diagDiff_surjective (R := R) s (diagBasis s i)).choose_spec,
    LinearEquiv.coe_coe, map_zero, sub_zero]
  ext k
  simp [Pi.single_apply, eq_comm]

lemma ker_diagSection_le :
    RingHom.ker (diagSection (R := R) s) ≤
      Ideal.span (Set.range (diagT (R := R) s)) ⊔ RingHom.ker (diagSection (R := R) s) ^ 2 := by
  intro j hj
  set c := diagCoord (R := R) s j
  set j' := j - ∑ i, algebraMap _ (Localization.Away s ⊗[R] S) (c i) * diagT s i
  have hj' : j' ∈ RingHom.ker (diagSection (R := R) s) := by
    simp only [j', RingHom.mem_ker, map_sub, map_sum, map_mul, diagSection_diagT, mul_zero,
      Finset.sum_const_zero, sub_zero]
    exact hj
  have hc : diagDiff (R := R) s j' = 0 := by
    apply (diagBasis (R := R) s).equivFun.injective
    have : diagCoord (R := R) s j' = 0 := by
      simp only [j', map_sub, map_sum, diagCoord_mul, diagSection_diagT, zero_smul, add_zero,
        diagCoord_diagT]
      ext k
      simp [c, Algebra.algebraMap_self, Pi.single_apply]
    simpa [diagCoord] using this
  have h2 := mem_sq_of_diagDiff_eq_zero s j' hj' hc
  have : j = (∑ i, algebraMap _ (Localization.Away s ⊗[R] S) (c i) * diagT s i) + j' := by
    simp [j']
  rw [this]
  exact Submodule.add_mem_sup
    (Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)) h2

end Coordinates

end Diagonal

section Final

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (s : S)

lemma formallySmooth_away_one_tmul [Algebra.FormallySmooth R (Localization.Away s)] :
    Algebra.FormallySmooth (Localization.Away s)
      (Localization.Away ((1 : Localization.Away s) ⊗ₜ[R] s)) := by
  have hM : (Submonoid.powers s).map
      (Algebra.TensorProduct.includeRight (R := R) (A := Localization.Away s)) =
      Submonoid.powers ((1 : Localization.Away s) ⊗ₜ[R] s) := by
    rw [Submonoid.map_powers]; rfl
  have : IsLocalization ((Submonoid.powers s).map
      (Algebra.TensorProduct.includeRight (R := R) (A := Localization.Away s)))
      (Localization.Away ((1 : Localization.Away s) ⊗ₜ[R] s)) := by
    rw [hM]; infer_instance
  exact Algebra.FormallySmooth.of_equiv
    (IsLocalization.tensorProductEquivOfMapIncludeRight R (Localization.Away s)
      (Submonoid.powers s) (Localization.Away s)
      (Localization.Away ((1 : Localization.Away s) ⊗ₜ[R] s)))

/-- **Local splitting over a smooth localization with free differentials.** -/
theorem locallySplit_away [Algebra.FinitePresentation R S] [Module.Flat R S]
    (hS : ∀ (K : Type u) [Field K] [Algebra R K], IsDomain (K ⊗[R] S))
    [Algebra.Smooth R (Localization.Away s)]
    [Module.Free (Localization.Away s) Ω[Localization.Away s⁄R]] :
    LocallySplit (Localization.Away s) (Localization.Away s ⊗[R] S) := by
  have := formallySmooth_away_one_tmul (R := R) s
  have hh : IsUnit (diagSection (R := R) s ((1 : Localization.Away s) ⊗ₜ[R] s)) := by
    rw [diagSection_tmul, one_mul]
    exact IsLocalization.Away.algebraMap_isUnit s
  have hθB : ∀ k, Function.Injective (theta (diagSection (R := R) s) (diagT s) k) :=
    theta_injective_of_formallySmooth (diagSection (R := R) s) (diagT s) (diagCoord s)
      (diagCoord_mul s) ((1 : Localization.Away s) ⊗ₜ[R] s) hh (diagSection_diagT s)
      (diagCoord_diagT s)
  have hfib : ∀ (P : Ideal (Localization.Away s)) [P.IsPrime],
      IsDomain (P.ResidueField ⊗[Localization.Away s] (Localization.Away s ⊗[R] S)) := by
    intro P _
    exact MulEquiv.isDomain (P.ResidueField ⊗[R] S)
      (Algebra.TensorProduct.cancelBaseChange R (Localization.Away s) P.ResidueField
        P.ResidueField S).toMulEquiv
  obtain ⟨R₀, S₀, _, _, _, _, _, _, _, e, σ₀, t₀, hinj, hσ, htt, hJ₀⟩ :=
    exists_noetherianModel (diagSection (R := R) s) (diagT s) (ker_diagSection_le s)
  exact locallySplit_of_noetherianModel e (diagSection (R := R) s) σ₀ hσ (diagT s) t₀ htt hinj
    (diagSection_diagT s) (by rw [pow_two]; exact hJ₀) hθB hfib

end Final

end Langlands.CommutativeAlgebra.IntegralFibre
