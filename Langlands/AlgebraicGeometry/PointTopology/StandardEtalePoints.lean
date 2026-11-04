import Langlands.AlgebraicGeometry.PointTopology.Affine
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.Analysis.Normed.Field.Lemmas

/-! # Actual points in a standard etale presentation -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v w

open Polynomial
open scoped Topology

namespace Langlands.AlgebraicGeometry.PointTopology

variable {K : Type u} [NontriviallyNormedField K]
variable {A : Type v} [CommRing A] [Algebra K A]
variable {B : Type w} [CommRing B] [Algebra K B] [Algebra A B]
variable [IsScalarTower K A B]

/-- Joint evaluation of an actual polynomial, allowing its coefficient point to vary. -/
theorem continuous_point_polynomial_eval (f : A[X]) :
    Continuous (fun z : AlgPoint K A K × K => f.eval₂ z.1.toAlgHom.toRingHom z.2) := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    exact (hf.add hg).congr (fun z => (Polynomial.eval₂_add _ _).symm)
  | monomial n a =>
    have ha : Continuous (fun z : AlgPoint K A K × K => z.1 a) :=
      (AlgPoint.continuous_eval a).comp continuous_fst
    have hx : Continuous (fun z : AlgPoint K A K × K => z.2 ^ n) :=
      continuous_snd.pow n
    exact (ha.mul hx).congr (fun z => (Polynomial.eval₂_monomial _ _).symm)

/-- The equations and invertibility condition of a standard etale presentation. -/
abbrev StandardEtalePointCoordinates (P : StandardEtalePresentation A B) :=
  {z : AlgPoint K A K × K //
    P.f.eval₂ z.1.toAlgHom.toRingHom z.2 = 0 ∧
      P.g.eval₂ z.1.toAlgHom.toRingHom z.2 ≠ 0}

/-- Lift a coefficient point and a permitted root to an actual algebra-map point. -/
def standardEtalePointLift (P : StandardEtalePresentation A B)
    (p : AlgPoint K A K) (x : K)
    (hf : P.f.eval₂ p.toAlgHom.toRingHom x = 0)
    (hg : P.g.eval₂ p.toAlgHom.toRingHom x ≠ 0) : AlgPoint K B K := by
  letI : Algebra A K := p.toAlgHom.toRingHom.toAlgebra
  have h : P.P.HasMap x := by
    constructor
    · exact hf
    · exact isUnit_iff_ne_zero.mpr hg
  let q : B →ₐ[A] K := (P.P.lift x h).comp P.equivRing.toAlgHom
  exact AlgPoint.ofAlgHom
    { __ := q.toRingHom
      commutes' := fun k => by
        change q (algebraMap K B k) = algebraMap K K k
        rw [IsScalarTower.algebraMap_apply K A B, q.commutes]
        exact p.toAlgHom.commutes k }

@[simp]
theorem standardEtalePointLift_base (P : StandardEtalePresentation A B)
    (p : AlgPoint K A K) (x : K) (hf hg) (a : A) :
    standardEtalePointLift P p x hf hg (algebraMap A B a) = p a := by
  simp [standardEtalePointLift, AlgPoint.ofAlgHom, AlgHom.commutes,
    RingHom.algebraMap_toAlgebra]

@[simp]
theorem standardEtalePointLift_root (P : StandardEtalePresentation A B)
    (p : AlgPoint K A K) (x : K) (hf hg) :
    standardEtalePointLift P p x hf hg P.x = x := by
  simp [standardEtalePointLift, AlgPoint.ofAlgHom]

omit [Algebra K A] [IsScalarTower K A B] in
/-- An algebra-map point evaluates a polynomial in the presentation's generator. -/
theorem standardEtalePoint_eval (P : StandardEtalePresentation A B)
    (q : AlgPoint K B K) (f : A[X]) :
    q (aeval P.x f) = f.eval₂
      (q.toAlgHom.toRingHom.comp (algebraMap A B)) (q P.x) := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp only [map_add, hf, hg, Polynomial.eval₂_add]
  | monomial n a => simp [Polynomial.aeval_monomial]

/-- The canonical coordinate map uses restriction and evaluation of the generator. -/
def standardEtalePointToCoordinates (P : StandardEtalePresentation A B)
    (q : AlgPoint K B K) : StandardEtalePointCoordinates (K := K) P := by
  refine ⟨(AlgPoint.precomp (IsScalarTower.toAlgHom K A B) q, q P.x), ?_, ?_⟩
  · change P.f.eval₂
      (q.toAlgHom.toRingHom.comp (algebraMap A B)) (q P.x) = 0
    rw [← standardEtalePoint_eval P q P.f]
    exact congrArg q P.hasMap.1 |>.trans (map_zero q.toAlgHom)
  · change P.g.eval₂
      (q.toAlgHom.toRingHom.comp (algebraMap A B)) (q P.x) ≠ 0
    rw [← standardEtalePoint_eval P q P.g]
    exact isUnit_iff_ne_zero.mp (P.hasMap.2.map q.toAlgHom)

/-- Polynomial evaluation under the lift is ordinary evaluation at the chosen root. -/
theorem standardEtalePointLift_eval (P : StandardEtalePresentation A B)
    (p : AlgPoint K A K) (x : K) (hf hg) (f : A[X]) :
    standardEtalePointLift P p x hf hg (aeval P.x f) =
      f.eval₂ p.toAlgHom.toRingHom x := by
  rw [standardEtalePoint_eval, standardEtalePointLift_root]
  congr 1
  ext a
  exact standardEtalePointLift_base P p x hf hg a

/-- Every evaluation of a lifted point is a polynomial numerator over a nonzero denominator. -/
theorem standardEtalePointLift_fraction (P : StandardEtalePresentation A B) (b : B) :
    ∃ (f : A[X]) (n : ℕ), ∀ (p : AlgPoint K A K) (x : K) (hf hg),
      standardEtalePointLift P p x hf hg b =
        f.eval₂ p.toAlgHom.toRingHom x / (P.g.eval₂ p.toAlgHom.toRingHom x) ^ n := by
  obtain ⟨f, n, h⟩ := P.exists_mul_aeval_x_g_pow_eq_aeval_x b
  refine ⟨f, n, fun p x hf hg => ?_⟩
  apply (eq_div_iff (pow_ne_zero n hg)).mpr
  have he := congrArg (standardEtalePointLift P p x hf hg).toAlgHom h
  simpa only [map_mul, map_pow, AlgPoint.toAlgHom_apply,
    standardEtalePointLift_eval] using he

omit [Algebra K A] [IsScalarTower K A B] in
/-- Restriction and generator evaluation determine every actual point. -/
theorem standardEtalePoint_ext (P : StandardEtalePresentation A B)
    {q r : AlgPoint K B K}
    (hbase : ∀ a : A, q (algebraMap A B a) = r (algebraMap A B a))
    (hroot : q P.x = r P.x) : q = r := by
  have hcoeff : q.toAlgHom.toRingHom.comp (algebraMap A B) =
      r.toAlgHom.toRingHom.comp (algebraMap A B) := RingHom.ext hbase
  have heval (f : A[X]) : q (aeval P.x f) = r (aeval P.x f) := by
    rw [standardEtalePoint_eval, standardEtalePoint_eval, hcoeff, hroot]
  apply AlgPoint.ext
  intro b
  obtain ⟨f, n, h⟩ := P.exists_mul_aeval_x_g_pow_eq_aeval_x b
  have hq := congrArg q.toAlgHom h
  have hr := congrArg r.toAlgHom h
  simp only [map_mul, map_pow, AlgPoint.toAlgHom_apply] at hq hr
  have hg : r (aeval P.x P.g) ≠ 0 :=
    isUnit_iff_ne_zero.mp (P.hasMap.2.map r.toAlgHom)
  apply mul_right_cancel₀ (pow_ne_zero n hg)
  exact (congrArg (fun t : K => q b * t ^ n) (heval P.g).symm).trans
    (hq.trans ((heval f).trans hr.symm))

/-- The inverse coordinate map is built by the standard etale universal property. -/
def standardEtalePointFromCoordinates (P : StandardEtalePresentation A B)
    (z : StandardEtalePointCoordinates (K := K) P) : AlgPoint K B K :=
  standardEtalePointLift P z.1.1 z.1.2 z.2.1 z.2.2

/-- Actual algebra-map points are homeomorphic to the polynomial root coordinates. -/
def standardEtalePointHomeomorph (P : StandardEtalePresentation A B) :
    AlgPoint K B K ≃ₜ StandardEtalePointCoordinates (K := K) P where
  toFun := standardEtalePointToCoordinates P
  invFun := standardEtalePointFromCoordinates P
  left_inv q := by
    apply standardEtalePoint_ext P
    · intro a
      exact standardEtalePointLift_base P _ _ _ _ a
    · exact standardEtalePointLift_root P _ _ _ _
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · apply AlgPoint.ext
      intro a
      exact standardEtalePointLift_base P z.1.1 z.1.2 z.2.1 z.2.2 a
    · exact standardEtalePointLift_root P z.1.1 z.1.2 z.2.1 z.2.2
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (AlgPoint.continuous_precomp (IsScalarTower.toAlgHom K A B)).prodMk
      (AlgPoint.continuous_eval P.x)
  continuous_invFun := by
    apply (AlgPoint.continuous_iff _).mpr
    intro b
    obtain ⟨f, n, h⟩ := standardEtalePointLift_fraction (K := K) P b
    have hf : Continuous (fun z : StandardEtalePointCoordinates (K := K) P =>
        f.eval₂ z.1.1.toAlgHom.toRingHom z.1.2) :=
      (continuous_point_polynomial_eval (K := K) f).comp continuous_subtype_val
    have hg : Continuous (fun z : StandardEtalePointCoordinates (K := K) P =>
        P.g.eval₂ z.1.1.toAlgHom.toRingHom z.1.2) :=
      (continuous_point_polynomial_eval (K := K) P.g).comp continuous_subtype_val
    exact (hf.div (hg.pow n) (fun z => pow_ne_zero n z.2.2)).congr
      (fun z => (h z.1.1 z.1.2 z.2.1 z.2.2).symm)

end Langlands.AlgebraicGeometry.PointTopology
