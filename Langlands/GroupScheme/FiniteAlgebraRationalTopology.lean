import Langlands.GroupScheme.FiniteAlgebraUnits
import Langlands.GroupScheme.Rational.PointTopology
import Mathlib.Topology.Algebra.MvPolynomial

/-! # Continuity of finite-algebra unit families as rational points -/

noncomputable section
universe u v

open CategoryTheory Opposite _root_.AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct Topology

namespace Langlands.GroupScheme.FiniteAlgebraUnits

open Langlands.AlgebraicGeometry.PointTopology

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable {n : ℕ} (b : Module.Basis (Fin n) k A)

private theorem affinePointsEquiv_symm_eq_map (x : (k ⊗[k] A)ˣ) :
    (affinePointsEquiv b (CommAlgCat.of (CommRingCat.of k) k)).symm x =
      (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom (unitCoefficientMap b x)).op := by
  apply (affinePointsEquiv b _).injective
  rw [MulEquiv.apply_symm_apply]
  have h := Corepresented.affinePointsEquiv_map (functor k A) (corepresentableBy b)
    (CommAlgCat.of (CommRingCat.of k) k) (CommAlgCat.ofHom (unitCoefficientMap b x))
  exact (h.trans (algebraicPoint_unitCoefficientMap b x)).symm

private theorem affinePointEvaluation_unitCoefficientMap (x : (k ⊗[k] A)ˣ)
    (a : Γ((groupScheme b).X.left, ⊤)) :
    (groupScheme b).affinePointEvaluation (CommAlgCat.of (CommRingCat.of k) k)
      ((affinePointsEquiv b _).symm x) a =
      unitCoefficientMap b x ((Scheme.ΓSpecIso (CommRingCat.of (candidateRing b))).hom a) := by
  rw [affinePointsEquiv_symm_eq_map]
  change (((Spec.map (CommRingCat.ofHom (unitCoefficientMap b x).toRingHom)).appTop ≫
    (Scheme.ΓSpecIso (CommRingCat.of k)).hom) a) = _
  rw [Scheme.ΓSpecIso_naturality]
  rfl

variable [TopologicalSpace k] [IsTopologicalRing k] [ContinuousInv₀ k]
variable {X : Type v} [TopologicalSpace X]

/-- Every coordinate of the determinant-open scheme is continuous when the basis
coordinates of the unit family are continuous. -/
theorem continuous_unitCoefficientMap_eval (f : X → (k ⊗[k] A)ˣ)
    (hf : ∀ i, Continuous fun x => (b.baseChange k).repr (f x).val i)
    (a : candidateRing b) : Continuous fun x => unitCoefficientMap b (f x) a := by
  have hp (p : coordinateRing k n) :
      Continuous fun x => coefficientMap b (f x).val p :=
    p.continuous_eval.comp (continuous_pi hf)
  obtain ⟨p, q, rfl⟩ := IsLocalization.exists_mk'_eq (.powers (determinant b)) a
  have he (x : X) : coefficientMap b (f x).val q ≠ 0 := by
    obtain ⟨m, hm⟩ := q.property
    rw [← hm, map_pow]
    exact pow_ne_zero _ (coefficientMap_determinant_isUnit b (f x)).ne_zero
  have heval (x : X) :
      unitCoefficientMap b (f x) (IsLocalization.mk' (candidateRing b) p q) =
        coefficientMap b (f x).val p / coefficientMap b (f x).val q := by
    apply (eq_div_iff (he x)).mpr
    have h := congrArg (unitCoefficientMap b (f x)) (IsLocalization.mk'_spec (candidateRing b) p q)
    simpa only [map_mul, unitCoefficientMap_algebraMap] using h
  simp_rw [heval]
  exact (hp p).div₀ (hp q) he

/-- Continuous basis coordinates give a continuous family of points of the actual
finite-algebra unit scheme in the canonical rational-point topology. -/
theorem continuous_rationalPointsEquiv_symm_of_basis (f : X → Aˣ)
    (hf : ∀ i, Continuous fun x => b.repr (f x).val i) :
    Continuous[inferInstance, rationalPointTopology k (groupScheme b).X]
      (fun x => (rationalPointsEquiv b).symm (f x)) := by
  let S := CommAlgCat.of (CommRingCat.of k) k
  let : TopologicalSpace S := inferInstanceAs (TopologicalSpace k)
  let : TopologicalSpace ((groupScheme b).affinePoints S) :=
    (groupScheme b).affinePointsTopologicalSpace S
  let : TopologicalSpace (rationalPoints (groupScheme b)) :=
    rationalPointTopology k (groupScheme b).X
  let v : X → (k ⊗[k] A)ˣ :=
    fun x => (Units.mapEquiv (Algebra.TensorProduct.lid k A).symm.toMulEquiv) (f x)
  have hr (a : A) : (Algebra.TensorProduct.lid k A).symm a = (1 : k) ⊗ₜ[k] a := by
    apply (Algebra.TensorProduct.lid k A).injective
    simp
  have hv (i : Fin n) : Continuous fun x => (b.baseChange k).repr (v x).val i := by
    change Continuous fun x => (b.baseChange k).repr ((Algebra.TensorProduct.lid k A).symm (f x).val) i
    simp_rw [hr, Module.Basis.baseChange_repr_tmul, smul_eq_mul, mul_one]
    exact hf i
  have ha : Continuous fun x => (affinePointsEquiv b S).symm (v x) := by
    apply ((groupScheme b).continuous_affinePoints_iff S _).mpr
    intro a
    have heval : (fun x => (groupScheme b).affinePointEvaluation S
        ((affinePointsEquiv b S).symm (v x)) a) =
        (fun x => unitCoefficientMap b (v x)
          ((Scheme.ΓSpecIso (CommRingCat.of (candidateRing b))).hom a)) := by
      funext x
      exact affinePointEvaluation_unitCoefficientMap b (v x) a
    rw [heval]
    exact continuous_unitCoefficientMap_eval b v hv _
  have h := (rationalPointsAffineHomeomorph (groupScheme b)).symm.continuous_toFun.comp ha
  convert h using 1
  funext x
  let e := rationalPointsAffineHomeomorph (groupScheme b)
  apply e.injective
  change e ((rationalPointsEquiv b).symm (f x)) = e (e.symm ((affinePointsEquiv b S).symm (v x)))
  rw [Homeomorph.apply_symm_apply]
  change rationalPointEquiv k (groupScheme b).X ((rationalPointsEquiv b).symm (f x)) = _
  rw [← GaloisPointComparison.rationalCoeffEquiv_eq]
  exact (GaloisPointComparison.rationalCoeffEquiv k (groupScheme b)).apply_symm_apply _

/-- Send algebra units to rational points by the canonical continuous homomorphism
when the finite basis coordinates are continuous. -/
def rationalPointOfUnit [TopologicalSpace A] (h : ∀ i, Continuous fun a : A => b.repr a i) :
    letI : TopologicalSpace (rationalPoints (groupScheme b)) :=
      rationalPointTopology k (groupScheme b).X
    Aˣ →ₜ* rationalPoints (groupScheme b) := by
  letI : TopologicalSpace (rationalPoints (groupScheme b)) :=
    rationalPointTopology k (groupScheme b).X
  exact
    { toMonoidHom := (rationalPointsEquiv b).symm.toMonoidHom
      continuous_toFun :=
        continuous_rationalPointsEquiv_symm_of_basis b id
          (fun i => (h i).comp Units.continuous_val) }

end Langlands.GroupScheme.FiniteAlgebraUnits
