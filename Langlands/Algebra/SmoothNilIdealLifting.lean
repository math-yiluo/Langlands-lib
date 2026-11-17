import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Noetherian.Nilpotent

/-! # Lifting smooth algebra maps through arbitrary nil kernels -/

noncomputable section

universe u v w z

namespace Langlands.SmoothNilIdealLifting

variable {R : Type u} {A : Type v} {B : Type w} {C : Type z}
  [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C]

/-- Every algebra map out of `A` lifts through the specified algebra map. -/
def LiftsThrough (q : B →ₐ[R] C) : Prop :=
  ∀ f : A →ₐ[R] C, ∃ g : A →ₐ[R] B, q.comp g = f

/-- Finite presentation confines the relations of a provisional lift to a
finitely generated subideal of the kernel. -/
theorem exists_finite_kernel_lift [Algebra.FinitePresentation R A]
    (f : A →ₐ[R] C) (q : B →ₐ[R] C) (hq : Function.Surjective q) :
    ∃ (J : Ideal B) (_ : J.FG) (hJ : J ≤ RingHom.ker q.toRingHom)
      (g : A →ₐ[R] B ⧸ J),
      (Ideal.Quotient.liftₐ J q hJ).comp g = f := by
  classical
  obtain ⟨n, p, hp, s, hs⟩ := Algebra.FinitePresentation.out (R := R) (A := A)
  choose b hb using fun i : Fin n => hq (f (p (MvPolynomial.X i)))
  let e : MvPolynomial (Fin n) R →ₐ[R] B := MvPolynomial.aeval b
  have he : q.comp e = f.comp p := by
    ext i
    simpa [e] using hb i
  let J : Ideal B := Ideal.span (e '' (s : Set (MvPolynomial (Fin n) R)))
  have hJfg : J.FG := Submodule.fg_span (s.finite_toSet.image e)
  have hJ : J ≤ RingHom.ker q.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨a, ha, rfl⟩
    change q (e a) = 0
    rw [← AlgHom.comp_apply, he, AlgHom.comp_apply]
    have hpa : p a = 0 := by
      have ha' : a ∈ RingHom.ker p.toRingHom := by
        rw [← hs]
        exact Ideal.subset_span ha
      exact ha'
    rw [hpa, map_zero]
  let eJ := (Ideal.Quotient.mkₐ R J).comp e
  have hk : RingHom.ker p.toRingHom ≤ RingHom.ker eJ.toRingHom := by
    rw [← hs]
    apply Ideal.span_le.mpr
    intro a ha
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span ⟨a, ha, rfl⟩)
  let g := AlgHom.liftOfSurjective p hp eJ hk
  refine ⟨J, hJfg, hJ, g, ?_⟩
  apply AlgHom.ext
  intro a
  obtain ⟨a, rfl⟩ := hp a
  change Ideal.Quotient.liftₐ J q hJ (g (p a)) = f (p a)
  rw [AlgHom.liftOfSurjective_apply]
  exact AlgHom.congr_fun he a

/-- A finitely presented formally smooth algebra lifts through every
surjective algebra map with nil kernel, without a uniform nilpotence bound. -/
theorem exists_lift_of_nil_kernel [Algebra.FinitePresentation R A]
    [Algebra.FormallySmooth R A]
    (f : A →ₐ[R] C) (q : B →ₐ[R] C) (hq : Function.Surjective q)
    (hnil : RingHom.ker q.toRingHom ≤ nilradical B) :
    ∃ g : A →ₐ[R] B, q.comp g = f := by
  obtain ⟨J, hJfg, hJ, g, hg⟩ := exists_finite_kernel_lift f q hq
  have hJnil : IsNilpotent J := hJfg.isNilpotent_iff_le_nilradical.mpr (hJ.trans hnil)
  obtain ⟨l, hl⟩ := Algebra.FormallySmooth.exists_lift J hJnil g
  refine ⟨l, ?_⟩
  calc
    q.comp l =
        (Ideal.Quotient.liftₐ J q hJ).comp ((Ideal.Quotient.mkₐ R J).comp l) := rfl
    _ = (Ideal.Quotient.liftₐ J q hJ).comp g := by rw [hl]
    _ = f := hg

/-- The quotient specialization for any ideal contained in the nilradical. -/
theorem exists_lift_of_nil_ideal [Algebra.FinitePresentation R A]
    [Algebra.FormallySmooth R A] (I : Ideal B) (hI : I ≤ nilradical B)
    (f : A →ₐ[R] B ⧸ I) :
    ∃ g : A →ₐ[R] B, (Ideal.Quotient.mkₐ R I).comp g = f := by
  apply exists_lift_of_nil_kernel f (Ideal.Quotient.mkₐ R I)
    (Ideal.Quotient.mkₐ_surjective R I)
  change RingHom.ker (Ideal.Quotient.mk I) ≤ nilradical B
  simpa only [Ideal.mk_ker] using hI

end Langlands.SmoothNilIdealLifting
