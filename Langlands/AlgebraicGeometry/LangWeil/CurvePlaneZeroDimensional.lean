import Mathlib.RingTheory.Jacobson.Artinian
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.FiniteStability
import Mathlib.Algebra.Polynomial.Roots

/-!
# Uniform point bounds from zero-dimensional generic fibres

For a finite-type algebra `D` over a domain `A` whose generic fibre `K ⊗[A] D` has Krull
dimension zero, the number of `A`-algebra maps from `D` to a field is bounded uniformly,
away from one nonzero element of `A`. A principal hypersurface in an irreducible generic
fibre of dimension at most one has a zero-dimensional generic fibre.
-/

universe u v w t

open scoped TensorProduct
open Polynomial

namespace Langlands.AlgebraicGeometry.LangWeil.CurvePlane

section ZeroDimensional

variable {A : Type u} {D : Type v} (K : Type w)
  [CommRing A] [IsDomain A] [CommRing D] [Algebra A D] [Field K] [Algebra A K]
  [IsFractionRing A K]

/-- Each element of an algebra with module-finite generic fibre is a root of a polynomial
with nonzero leading coefficient, after multiplication by a nonzero scalar. -/
theorem exists_polynomial_of_finite_tensor [Module.Finite K (K ⊗[A] D)] (x : D) :
    ∃ Q : A[X], Q.leadingCoeff ≠ 0 ∧ ∃ c : A, c ≠ 0 ∧ c • aeval x Q = 0 := by
  classical
  obtain ⟨P, hPm, hP⟩ := Algebra.IsIntegral.isIntegral (R := K) (1 ⊗ₜ[A] x : K ⊗[A] D)
  let Q := IsLocalization.integerNormalization (nonZeroDivisors A) P
  obtain ⟨b, hb, hQb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors A) P
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hb0 : (b : A) ≠ 0 := nonZeroDivisors.ne_zero hb
  have hlead : Q.leadingCoeff = b := by
    apply hinj
    rw [← Polynomial.leadingCoeff_map_of_injective hinj, hQb, Algebra.smul_def,
      Polynomial.algebraMap_apply, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      hPm.leadingCoeff, mul_one]
  have hQ : aeval (1 ⊗ₜ[A] x : K ⊗[A] D) Q = 0 :=
    IsLocalization.integerNormalization_aeval_eq_zero (nonZeroDivisors A) P hP
  have hQ' : TensorProduct.mk A K D 1 (aeval x Q) = 0 := by
    rw [← hQ, TensorProduct.mk_apply]
    exact (aeval_algHom_apply (Algebra.TensorProduct.includeRight : D →ₐ[A] K ⊗[A] D)
      x Q).symm
  obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors A)
    (TensorProduct.mk A K D 1)).mp hQ'
  exact ⟨Q, by rw [hlead]; exact hb0, c, nonZeroDivisors.ne_zero c.2, hc⟩

/-- An algebra of finite type whose generic fibre has dimension zero has uniformly finitely
many points in every field over which one fixed nonzero element of the base stays nonzero. -/
theorem exists_card_algHom_le_of_krullDimLE_zero [Algebra.FiniteType A D]
    [Ring.KrullDimLE 0 (K ⊗[A] D)] :
    ∃ a : A, a ≠ 0 ∧ ∃ N : ℕ, ∀ (κ : Type t) [Field κ] [Algebra A κ],
      algebraMap A κ a ≠ 0 → Finite (D →ₐ[A] κ) ∧ Nat.card (D →ₐ[A] κ) ≤ N := by
  classical
  have : Module.Finite K (K ⊗[A] D) :=
    (Module.finite_iff_krullDimLE_zero K (K ⊗[A] D)).mpr inferInstance
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType A D).out
  have hp (x : s) := exists_polynomial_of_finite_tensor (A := A) K (x : D)
  choose Q hQlc c hc0 hcQ using hp
  refine ⟨∏ x : s, (c x * (Q x).leadingCoeff), ?_, ∏ x : s, (Q x).natDegree, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr fun x _ => mul_ne_zero (hc0 x) (hQlc x)
  intro κ _ _ ha
  have hfac (x : s) : algebraMap A κ (c x) ≠ 0 ∧ algebraMap A κ (Q x).leadingCoeff ≠ 0 := by
    rw [map_prod, Finset.prod_ne_zero_iff] at ha
    have := ha x (Finset.mem_univ x)
    rw [map_mul] at this
    exact ⟨left_ne_zero_of_mul this, right_ne_zero_of_mul this⟩
  have hroot (φ : D →ₐ[A] κ) (x : s) : φ (x : D) ∈ (Q x).rootSet κ := by
    rw [mem_rootSet']
    refine ⟨fun h => (hfac x).2 ?_, ?_⟩
    · rw [← Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ (hfac x).2, h,
        Polynomial.leadingCoeff_zero]
    · have h := congrArg φ (hcQ x)
      rw [map_smul, map_zero, ← aeval_algHom_apply, Algebra.smul_def] at h
      exact (mul_eq_zero.mp h).resolve_left (hfac x).1
  let ev : (D →ₐ[A] κ) → ((x : s) → (Q x).rootSet κ) := fun φ x => ⟨φ (x : D), hroot φ x⟩
  have hev : Function.Injective ev := by
    intro φ ψ h
    apply AlgHom.ext_of_adjoin_eq_top hs
    intro a ha
    exact congrArg Subtype.val (congrFun h ⟨a, ha⟩)
  refine ⟨Finite.of_injective ev hev, ?_⟩
  calc
    Nat.card (D →ₐ[A] κ) ≤ Nat.card ((x : s) → (Q x).rootSet κ) :=
      Nat.card_le_card_of_injective ev hev
    _ = ∏ x : s, Nat.card ((Q x).rootSet κ) := Nat.card_pi
    _ ≤ ∏ x : s, (Q x).natDegree :=
      Finset.prod_le_prod fun x _ => ncard_rootSet_le (Q x) κ

end ZeroDimensional

section Fibre

/-- The zero-dimensional point bound over the residue field of an arbitrary prime: away from
one element outside the prime, the points over fields in which the prime vanishes are
uniformly bounded. -/
theorem exists_card_algHom_le_of_fiber_krullDimLE_zero {A : Type u} {D : Type v}
    [CommRing A] [CommRing D] [Algebra A D] [Algebra.FiniteType A D] (p : Ideal A) [p.IsPrime]
    [Ring.KrullDimLE 0 (p.ResidueField ⊗[A] D)] :
    ∃ a : A, a ∉ p ∧ ∃ N : ℕ, ∀ (κ : Type t) [Field κ] [Algebra A κ],
      (∀ x ∈ p, algebraMap A κ x = 0) → algebraMap A κ a ≠ 0 →
        Finite (D →ₐ[A] κ) ∧ Nat.card (D →ₐ[A] κ) ≤ N := by
  classical
  let e := Algebra.TensorProduct.cancelBaseChange A (A ⧸ p) p.ResidueField p.ResidueField D
  have : Ring.KrullDimLE 0 (p.ResidueField ⊗[A ⧸ p] ((A ⧸ p) ⊗[A] D)) := by
    rw [Ring.krullDimLE_iff, ringKrullDim_eq_of_ringEquiv e.toRingEquiv, ← Ring.krullDimLE_iff]
    infer_instance
  obtain ⟨a₀, ha₀, N, hN⟩ := exists_card_algHom_le_of_krullDimLE_zero.{u, max u v, u, t}
    (A := A ⧸ p) (D := (A ⧸ p) ⊗[A] D) p.ResidueField
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a₀
  refine ⟨a, fun h => ha₀ (Ideal.Quotient.eq_zero_iff_mem.mpr h), N, ?_⟩
  intro κ _ _ hp ha
  let : Algebra (A ⧸ p) κ := (Ideal.Quotient.lift p (algebraMap A κ) hp).toAlgebra
  have : IsScalarTower A (A ⧸ p) κ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let E := Algebra.TensorProduct.liftEquivRight A (A ⧸ p) D κ
  obtain ⟨hfin, hcard⟩ := hN κ ha
  exact ⟨Finite.of_equiv _ E.symm, (Nat.card_congr E).trans_le hcard⟩

end Fibre

section Codimension

/-- In a ring with prime nilradical and Krull dimension at most one, the quotient by a
non-nilpotent element has Krull dimension zero. -/
theorem krullDimLE_zero_quotient_span_singleton {T : Type v} [CommRing T]
    [(nilradical T).IsPrime] [Ring.KrullDimLE 1 T] {y : T} (hy : ¬IsNilpotent y) :
    Ring.KrullDimLE 0 (T ⧸ Ideal.span {y}) := by
  rw [Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal]
  intro J hJ
  have hJp : J.IsPrime := hJ.1.1
  rcases Ring.krullDimLE_one_iff.mp inferInstance J hJp with hmin | hmax
  · exfalso
    apply hy
    have hle : J ≤ nilradical T :=
      hmin.2 ⟨inferInstance, bot_le⟩ (nilradical_le_prime J)
    exact mem_nilradical.mp (hle (hJ.1.2 (Ideal.mem_span_singleton_self y)))
  · exact hmax

/-- A principal hypersurface cut out by an element that is not nilpotent on an irreducible
fibre of dimension at most one has a zero-dimensional fibre. The fibre is taken over an
arbitrary commutative algebra `L` of the base, for instance a residue field or a fraction
field. -/
theorem fiber_quotient_krullDimLE_zero {A : Type u} {R : Type v} (L : Type w) [CommRing A]
    [CommRing R] [Algebra A R] [CommRing L] [Algebra A L] [(nilradical (L ⊗[A] R)).IsPrime]
    [Ring.KrullDimLE 1 (L ⊗[A] R)] {h : R} (hh : ¬IsNilpotent ((1 : L) ⊗ₜ[A] h)) :
    Ring.KrullDimLE 0 (L ⊗[A] (R ⧸ Ideal.span {h})) := by
  let e := Algebra.TensorProduct.tensorQuotientEquiv (R := A) L R L (Ideal.span {h})
  rw [Ideal.map_span, Set.image_singleton] at e
  have := krullDimLE_zero_quotient_span_singleton hh
  rw [Ring.krullDimLE_iff, ringKrullDim_eq_of_ringEquiv e.toRingEquiv, ← Ring.krullDimLE_iff]
  exact this

/-- If the fibre is empty, so is every quotient fibre. -/
theorem fiber_krullDimLE_zero_of_subsingleton {A : Type u} {R : Type v} (L : Type w)
    [CommRing A] [CommRing R] [Algebra A R] [CommRing L] [Algebra A L]
    [Subsingleton (L ⊗[A] R)] (I : Ideal R) :
    Ring.KrullDimLE 0 (L ⊗[A] (R ⧸ I)) := by
  have : Subsingleton (L ⊗[A] (R ⧸ I)) := by
    let f : L ⊗[A] R →ₐ[L] L ⊗[A] (R ⧸ I) :=
      Algebra.TensorProduct.map (AlgHom.id _ _) (Ideal.Quotient.mkₐ A I)
    refine subsingleton_of_zero_eq_one ?_
    rw [← map_zero f, ← map_one f, Subsingleton.elim (0 : L ⊗[A] R) 1]
  infer_instance

end Codimension

end Langlands.AlgebraicGeometry.LangWeil.CurvePlane
