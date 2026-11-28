import Langlands.Algebra.CentralSimple.LandherrArtinianNorm
import Langlands.Algebra.CentralSimple.LandherrHensel
import Langlands.LinearAlgebra.QuadraticNormLocalGlobal
import Langlands.ClassFieldTheory.Global.CyclicHasseNormProof
import Langlands.ClassFieldTheory.Global.IdeleLocalInjectivity
import Mathlib.NumberTheory.RamificationInertia.Valuation

/-! # Binary norm equations in finite-dimensional commutative algebras over a number field -/

noncomputable section

namespace Langlands.CentralSimple.Landherr

open NumberField IsDedekindDomain Polynomial Langlands.Global.AdelicFunctoriality
open scoped TensorProduct NumberField.LiesOver
open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension

universe u

/-- A root of a monic polynomial whose coefficients have valuation at most one has valuation at
most one. -/
theorem valuation_le_one_of_eval_eq_zero {L Γ₀ : Type*} [Field L]
    [LinearOrderedCommGroupWithZero Γ₀] (w : Valuation L Γ₀) {f : L[X]} (hm : f.Monic)
    (hc : ∀ i, w (f.coeff i) ≤ 1) {x : L} (hx : f.eval x = 0) : w x ≤ 1 := by
  by_contra h
  push Not at h
  have hx0 : w x ≠ 0 := ne_of_gt (lt_trans zero_lt_one h)
  by_cases hn : f.natDegree = 0
  · have hf1 : f = 1 := by
      rw [Polynomial.eq_C_of_natDegree_eq_zero hn, ← hn, hm.coeff_natDegree, map_one]
    rw [hf1, eval_one] at hx
    exact one_ne_zero hx
  rw [eval_eq_sum_range, Finset.sum_range_succ, hm.coeff_natDegree, one_mul,
    add_eq_zero_iff_eq_neg] at hx
  have h1 : w x ^ f.natDegree =
      w (∑ i ∈ Finset.range f.natDegree, f.coeff i * x ^ i) := by
    rw [← map_pow, hx, Valuation.map_neg]
  have h2 : w (∑ i ∈ Finset.range f.natDegree, f.coeff i * x ^ i) < w x ^ f.natDegree := by
    refine w.map_sum_lt (pow_ne_zero _ hx0) fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [map_mul, map_pow]
    exact mul_lt_of_le_one_of_lt (hc i) (pow_lt_pow_right₀ h hi)
  exact absurd h1 (ne_of_gt h2)

variable {F : Type u} [Field F] [NumberField F]

/-- Let `P` be a finite place of `L` above `v` in `F` and let `d ≠ 0`. The equation
`x² - d y² = π z` is solvable in `L_P` if `d` is a square in `F_v`, if `1 ⊗ z` is a
square in `F_v ⊗_F K`, or if `2` and `d` are `v`-units and `π z` is a `P`-unit. -/
theorem localSolvable_finite {K : Type u} [CommRing K] [Algebra F K] {L : Type u} [Field L]
    [NumberField L] [Algebra F L] (π : K →ₐ[F] L) (d : F) (hd : d ≠ 0) (z : K)
    (P : HeightOneSpectrum (𝓞 L))
    (h : IsSquare (algebraMap F ((ClassFieldTheory.Global.placeBelow F P).adicCompletion F) d) ∨
      (∃ s : (ClassFieldTheory.Global.placeBelow F P).adicCompletion F ⊗[F] K,
        s * s = 1 ⊗ₜ z) ∨
      ((ClassFieldTheory.Global.placeBelow F P).valuation F 2 = 1 ∧
        (ClassFieldTheory.Global.placeBelow F P).valuation F d = 1 ∧
        P.valuation L (π z) = 1)) :
    ∃ x y : P.adicCompletion L,
      x ^ 2 - algebraMap L _ (algebraMap F L d) * y ^ 2 = algebraMap L _ (π z) := by
  set v := ClassFieldTheory.Global.placeBelow F P with hv
  have : P.asIdeal.LiesOver v.asIdeal := ClassFieldTheory.Global.liesOver_placeBelow F P
  let φ := FiniteExtension.completionMap v P
  have hφ : ∀ c : F, φ (algebraMap F (v.adicCompletion F) c) =
      algebraMap L (P.adicCompletion L) (algebraMap F L c) := fun c =>
    FiniteExtension.completionMap_coe v P c
  have hchar : CharZero (P.adicCompletion L) :=
    charZero_of_injective_algebraMap (algebraMap L (P.adicCompletion L)).injective
  have hd' : algebraMap L (P.adicCompletion L) (algebraMap F L d) ≠ 0 := by
    rw [_root_.map_ne_zero, _root_.map_ne_zero]; exact hd
  rcases h with ⟨e, he⟩ | ⟨s, hs⟩ | ⟨h2, hdv, hz⟩
  · apply QuadraticNormEquation.exists_eq_of_isSquare hd'
    exact ⟨φ e, by rw [← hφ, he, map_mul]⟩
  · let _ : Algebra F (P.adicCompletion L) :=
      ((algebraMap L (P.adicCompletion L)).comp (algebraMap F L)).toAlgebra
    let φF : v.adicCompletion F →ₐ[F] P.adicCompletion L :=
      { φ with commutes' := fun c => hφ c }
    let πP : K →ₐ[F] P.adicCompletion L :=
      { (algebraMap L (P.adicCompletion L)).comp π.toRingHom with
        commutes' := fun c => by simp [RingHom.algebraMap_toAlgebra] }
    let ψ : v.adicCompletion F ⊗[F] K →ₐ[F] P.adicCompletion L :=
      Algebra.TensorProduct.lift φF πP (fun _ _ => Commute.all _ _)
    refine ⟨ψ s, 0, ?_⟩
    rw [sq, ← map_mul, hs]
    simp [ψ, πP]
  · have key : ∀ x : L, Valued.v (algebraMap L (P.adicCompletion L) x) = P.valuation L x :=
      fun x => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P x
    have hval : ∀ c : F, (ClassFieldTheory.Global.placeBelow F P).valuation F c = 1 →
        Valued.v (algebraMap L (P.adicCompletion L) (algebraMap F L c)) = 1 := by
      intro c hc
      rw [key, ← HeightOneSpectrum.valuation_liesOver L v P, hc, one_pow]
    have h2' := hval 2 h2
    rw [map_ofNat, map_ofNat] at h2'
    refine Landherr.exists_sq_sub_mul_sq_of_units P _ _ (hval d hdv) ?_ h2'
    rw [key]
    exact hz

omit [NumberField F] in
/-- Let `P` be an infinite place of `L` above `v` in `F` and let `d ≠ 0`. The equation
`x² - d y² = π z` is solvable in `L_P` if `d` is a square in `F_v` or `1 ⊗ z` is a
square in `F_v ⊗_F K`. -/
theorem localSolvable_infinite {K : Type u} [CommRing K] [Algebra F K] {L : Type u} [Field L]
    [NumberField L] [Algebra F L] (π : K →ₐ[F] L) (d : F) (hd : d ≠ 0) (z : K)
    (P : NumberField.InfinitePlace L)
    (h : IsSquare (algebraMap F (P.comap (algebraMap F L)).Completion d) ∨
      ∃ s : (P.comap (algebraMap F L)).Completion ⊗[F] K, s * s = 1 ⊗ₜ z) :
    ∃ x y : P.Completion,
      x ^ 2 - algebraMap L _ (algebraMap F L d) * y ^ 2 = algebraMap L _ (π z) := by
  set v := P.comap (algebraMap F L) with hv
  have : P.LiesOver v := ⟨rfl⟩
  let φ := NumberField.LiesOver.completionMap v P
  have hφ : ∀ c : F, φ (algebraMap F v.Completion c) =
      algebraMap L P.Completion (algebraMap F L c) := fun c => by
    rw [← RingHom.algebraMap_toAlgebra φ, ← IsScalarTower.algebraMap_apply]
    rfl
  have hchar : CharZero P.Completion :=
    charZero_of_injective_algebraMap (algebraMap L P.Completion).injective
  have hd' : algebraMap L P.Completion (algebraMap F L d) ≠ 0 := by
    rw [_root_.map_ne_zero, _root_.map_ne_zero]; exact hd
  rcases h with ⟨e, he⟩ | ⟨s, hs⟩
  · apply QuadraticNormEquation.exists_eq_of_isSquare hd'
    exact ⟨φ e, by rw [← hφ, he, map_mul]⟩
  · let _ : Algebra F P.Completion :=
      ((algebraMap L P.Completion).comp (algebraMap F L)).toAlgebra
    let φF : v.Completion →ₐ[F] P.Completion := { φ with commutes' := fun c => hφ c }
    let πP : K →ₐ[F] P.Completion :=
      { (algebraMap L P.Completion).comp π.toRingHom with
        commutes' := fun c => by simp [RingHom.algebraMap_toAlgebra] }
    let ψ : v.Completion ⊗[F] K →ₐ[F] P.Completion :=
      Algebra.TensorProduct.lift φF πP (fun _ _ => Commute.all _ _)
    refine ⟨ψ s, 0, ?_⟩
    rw [sq, ← map_mul, hs]
    simp [ψ, πP]

/-- The valuation at a place above `v` of a root of a monic polynomial over `F` with
`v`-integral coefficients is at most one. -/
theorem valuation_le_one_of_aeval {L : Type u} [Field L] [NumberField L] [Algebra F L]
    (P : HeightOneSpectrum (𝓞 L)) {f : F[X]} (hf : f.Monic)
    (hc : ∀ i, (ClassFieldTheory.Global.placeBelow F P).valuation F (f.coeff i) ≤ 1) {x : L}
    (hx : aeval x f = 0) : P.valuation L x ≤ 1 := by
  have : P.asIdeal.LiesOver (ClassFieldTheory.Global.placeBelow F P).asIdeal :=
    ClassFieldTheory.Global.liesOver_placeBelow F P
  refine valuation_le_one_of_eval_eq_zero (P.valuation L) (hf.map (algebraMap F L)) (fun i => ?_)
    (by rw [eval_map_algebraMap]; exact hx)
  rw [coeff_map, ← HeightOneSpectrum.valuation_liesOver L
    (ClassFieldTheory.Global.placeBelow F P) P]
  exact pow_le_one₀ zero_le (hc i)

/-- **Binary norm equations in finite-dimensional commutative algebras.** Let `K` be a
finite-dimensional commutative algebra over a number field `F`, `d ≠ 0` in `F` and `z` a unit of
`K`. Suppose that at every finite place `v` of `F`, either `d` is a square in `F_v`, or `z` has a
square root in `F_v ⊗_F K`, or `2`, `d` are `v`-units and `z`, `z⁻¹` are roots of monic polynomials
with `v`-integral coefficients; and at every infinite place `w`, either `d` is a square in `F_w`
or `z` has a square root in `F_w ⊗_F K`. Then `z = X² - d Y²` for some `X, Y ∈ K`. -/
theorem exists_sq_sub_mul_sq_of_local {K : Type u} [CommRing K] [Algebra F K]
    [FiniteDimensional F K] (d : F) (hd : d ≠ 0) (z : K) (hz : IsUnit z)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 F), IsSquare (algebraMap F (v.adicCompletion F) d) ∨
      (∃ s : v.adicCompletion F ⊗[F] K, s * s = 1 ⊗ₜ z) ∨
      (v.valuation F 2 = 1 ∧ v.valuation F d = 1 ∧ ∃ f g : F[X], f.Monic ∧ g.Monic ∧
        (∀ i, v.valuation F (f.coeff i) ≤ 1) ∧ (∀ i, v.valuation F (g.coeff i) ≤ 1) ∧
        aeval z f = 0 ∧ aeval ((hz.unit⁻¹ : Kˣ) : K) g = 0))
    (hinf : ∀ w : NumberField.InfinitePlace F, IsSquare (algebraMap F w.Completion d) ∨
      ∃ s : w.Completion ⊗[F] K, s * s = 1 ⊗ₜ z) :
    ∃ X Y : K, X ^ 2 - algebraMap F K d * Y ^ 2 = z := by
  classical
  have : IsArtinianRing K := IsArtinianRing.of_finite F K
  have h2 : IsUnit (2 : K) := by
    have := (IsUnit.mk0 (2 : F) two_ne_zero).map (algebraMap F K)
    rwa [map_ofNat] at this
  apply exists_sq_sub_mul_sq_eq_of_maximal h2 (algebraMap F K d) z hz
  intro m hm
  let L := K ⧸ m
  let _ : Field L := Ideal.Quotient.field m
  let π : K →ₐ[F] L := Ideal.Quotient.mkₐ F m
  have hπ : Function.Surjective π := Ideal.Quotient.mkₐ_surjective F m
  have : FiniteDimensional F L := Module.Finite.of_surjective π.toLinearMap hπ
  let _ : NumberField L := NumberField.of_module_finite F L
  have hzL : π z ≠ 0 := (hz.map π).ne_zero
  have hdL : algebraMap F L d ≠ 0 := by rw [_root_.map_ne_zero]; exact hd
  have hfin' : ∀ P : HeightOneSpectrum (𝓞 L), ∃ x y : P.adicCompletion L,
      x ^ 2 - algebraMap L _ (algebraMap F L d) * y ^ 2 = algebraMap L _ (π z) := by
    intro P
    apply localSolvable_finite π d hd z P
    rcases hfin (ClassFieldTheory.Global.placeBelow F P) with h | h | ⟨h2v, hdv, f, g, hf, hg, hfc,
      hgc, hfz, hgz⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · refine Or.inr (Or.inr ⟨h2v, hdv, ?_⟩)
      have hle : P.valuation L (π z) ≤ 1 :=
        valuation_le_one_of_aeval P hf hfc (by rw [aeval_algHom_apply, hfz, map_zero])
      have hle' : P.valuation L (π z)⁻¹ ≤ 1 := by
        have hinv : (π z)⁻¹ = π ((hz.unit⁻¹ : Kˣ) : K) := by
          rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ hzL, ← map_mul]
          rw [IsUnit.val_inv_mul hz, map_one]
        rw [hinv]
        exact valuation_le_one_of_aeval P hg hgc (by rw [aeval_algHom_apply, hgz, map_zero])
      rw [map_inv₀] at hle'
      have hpos : P.valuation L (π z) ≠ 0 := by rwa [Ne, Valuation.zero_iff]
      refine le_antisymm hle ?_
      calc (1 : _) = P.valuation L (π z) * (P.valuation L (π z))⁻¹ := (mul_inv_cancel₀ hpos).symm
        _ ≤ P.valuation L (π z) * 1 := by gcongr
        _ = P.valuation L (π z) := mul_one _
  have hinf' : ∀ P : NumberField.InfinitePlace L, ∃ x y : P.Completion,
      x ^ 2 - algebraMap L _ (algebraMap F L d) * y ^ 2 = algebraMap L _ (π z) := fun P =>
    localSolvable_infinite π d hd z P (hinf _)
  obtain ⟨X, Y, hXY⟩ := QuadraticNormLocalGlobal.exists_eq_of_local
    ClassFieldTheory.Global.cyclicHasseNorm hdL hzL hfin' hinf'
  obtain ⟨X', rfl⟩ := hπ X
  obtain ⟨Y', rfl⟩ := hπ Y
  refine ⟨X', Y', ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change π (X' ^ 2 - algebraMap F K d * Y' ^ 2 - z) = 0
  rw [map_sub, map_sub, map_mul, map_pow, map_pow, AlgHom.commutes, hXY, sub_self]

end Langlands.CentralSimple.Landherr
