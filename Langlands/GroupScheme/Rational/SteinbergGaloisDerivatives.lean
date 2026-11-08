import Langlands.GroupScheme.Rational.SteinbergNormalizedGaloisTransport

/-! # Coefficients and derivatives of actual semilinear root transport -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option autoImplicit false

namespace VectorGroup

variable (K : Type u) [Field K]

/-- The standard epsilon vector is the scalar point with coordinate epsilon. -/
theorem standardEpsilon_val_eq_scalarPoint :
    (standardEpsilon K).toMul.val =
      scalarPoint (CommRingCat.of K)
        ((algSpec (CommRingCat.of K)).obj (op (CommAlgCat.of K (DualNumber K))))
        ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv
          (TrivSqZeroExt.inr (1 : K))) := by
  apply points_ext
  intro j
  rw [coordinates_scalarPoint]
  apply (Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).commRingCatIsoToRingEquiv.injective
  have h := congrFun
    (RelativeRoot.vectorAffineCoordinates_vectorLiePoint
      (coordinates (CommRingCat.of K) 1) isNaturalVectorCoordinates
      (fun _ => (1 : K))) j
  exact h.trans ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv_hom_id_apply _).symm

/-- On the generic polynomial test the coordinate scalar point is the identity. -/
theorem scalarPoint_generic_eq_id :
    scalarPoint (CommRingCat.of K)
        ((algSpec (CommRingCat.of K)).obj
          (op (CommAlgCat.of K (MvPolynomial (Fin 1) K))))
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin 1) K))).inv
          (MvPolynomial.X (0 : Fin 1))) = 𝟙 _ := by
  rw [scalarPoint_eq_algSpec_aeval]
  have h : (MvPolynomial.aeval (fun _ : Fin 1 => MvPolynomial.X (0 : Fin 1)) :
      MvPolynomial (Fin 1) K →ₐ[K] MvPolynomial (Fin 1) K) =
        AlgHom.id K (MvPolynomial (Fin 1) K) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [MvPolynomial.aeval_X, AlgHom.id_apply]
    exact congrArg (MvPolynomial.X (R := K)) (Subsingleton.elim 0 j)
  rw [h]
  exact (algSpec (CommRingCat.of K)).map_id _

end VectorGroup

namespace PolynomialGalois

variable (k K : Type u) [Field k] [Field K] [Algebra k K] (σ : K ≃ₐ[k] K)

/-- Twisting the coefficient structure while fixing the generic variable is
exactly coefficient conjugation of the polynomial algebra. -/
theorem aeval_generic_twisted :
    ((MvPolynomial.aeval (fun _ : Fin 1 =>
        (MvPolynomial.X (0 : Fin 1) : Lie.GaloisTestAlgebra σ (MvPolynomial (Fin 1) K))) :
      MvPolynomial (Fin 1) K →ₐ[K] Lie.GaloisTestAlgebra σ (MvPolynomial (Fin 1) K)).restrictScalars k) =
      lineConjugate k K σ := by
  apply AlgHom.coe_ringHom_injective
  apply MvPolynomial.ringHom_ext
  · intro c
    change (MvPolynomial.aeval (fun _ : Fin 1 =>
        (MvPolynomial.X (0 : Fin 1) : Lie.GaloisTestAlgebra σ (MvPolynomial (Fin 1) K))) :
      MvPolynomial (Fin 1) K →ₐ[K] Lie.GaloisTestAlgebra σ (MvPolynomial (Fin 1) K))
        (MvPolynomial.C c) =
      MvPolynomial.map σ.toRingHom (MvPolynomial.C c)
    rw [MvPolynomial.aeval_C, MvPolynomial.map_C]
    rfl
  · intro j
    change (MvPolynomial.aeval (fun _ : Fin 1 =>
        (MvPolynomial.X (0 : Fin 1) : Lie.GaloisTestAlgebra σ (MvPolynomial (Fin 1) K))) :
      MvPolynomial (Fin 1) K →ₐ[K] Lie.GaloisTestAlgebra σ (MvPolynomial (Fin 1) K))
        (MvPolynomial.X j) =
      MvPolynomial.map σ.toRingHom (MvPolynomial.X j)
    rw [MvPolynomial.aeval_X, MvPolynomial.map_X]
    exact congrArg MvPolynomial.X (Subsingleton.elim 0 j)

/-- Evaluation at epsilon on the twisted test equals ordinary epsilon
evaluation followed by the actual dual-number coefficient map. -/
theorem aeval_epsilon_twisted :
    ((MvPolynomial.aeval (fun _ : Fin 1 =>
        (TrivSqZeroExt.inr (1 : K) : Lie.GaloisTestAlgebra σ (DualNumber K))) :
      MvPolynomial (Fin 1) K →ₐ[K] Lie.GaloisTestAlgebra σ (DualNumber K)).restrictScalars k) =
      (GeneralLinear.DualNumber.coefficientAlgMap (R := CommRingCat.of k) σ.toAlgHom).comp
        ((MvPolynomial.aeval (fun _ : Fin 1 =>
          (TrivSqZeroExt.inr (1 : K) : DualNumber K)) :
            MvPolynomial (Fin 1) K →ₐ[K] DualNumber K).restrictScalars k) := by
  apply AlgHom.coe_ringHom_injective
  apply MvPolynomial.ringHom_ext
  · intro c
    change (MvPolynomial.aeval (fun _ : Fin 1 =>
        (TrivSqZeroExt.inr (1 : K) : Lie.GaloisTestAlgebra σ (DualNumber K))) :
      MvPolynomial (Fin 1) K →ₐ[K] Lie.GaloisTestAlgebra σ (DualNumber K))
        (MvPolynomial.C c) =
      GeneralLinear.DualNumber.coefficientAlgMap (R := CommRingCat.of k) σ.toAlgHom
        ((MvPolynomial.aeval (fun _ : Fin 1 =>
          (TrivSqZeroExt.inr (1 : K) : DualNumber K)) :
            MvPolynomial (Fin 1) K →ₐ[K] DualNumber K) (MvPolynomial.C c))
    rw [MvPolynomial.aeval_C, MvPolynomial.aeval_C]
    apply TrivSqZeroExt.ext
    · rfl
    · exact (map_zero σ).symm
  · intro j
    change (MvPolynomial.aeval (fun _ : Fin 1 =>
        (TrivSqZeroExt.inr (1 : K) : Lie.GaloisTestAlgebra σ (DualNumber K))) :
      MvPolynomial (Fin 1) K →ₐ[K] Lie.GaloisTestAlgebra σ (DualNumber K))
        (MvPolynomial.X j) =
      GeneralLinear.DualNumber.coefficientAlgMap (R := CommRingCat.of k) σ.toAlgHom
        ((MvPolynomial.aeval (fun _ : Fin 1 =>
          (TrivSqZeroExt.inr (1 : K) : DualNumber K)) :
            MvPolynomial (Fin 1) K →ₐ[K] DualNumber K) (MvPolynomial.X j))
    rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    apply TrivSqZeroExt.ext
    · exact (map_zero σ).symm
    · exact (map_one σ).symm

end PolynomialGalois

namespace VectorGroup

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    (f : groupScheme (CommRingCat.of K) 1 ⟶
      (GroupScheme.baseChange (algebraBaseMap k K)).obj G)

/-- An arbitrary additive-line homomorphism as a polynomial-valued point of
the original group. -/
def affineCoefficientCurve : Lie.AffinePoints G (MvPolynomial (Fin 1) K) :=
  Lie.affineBaseChangeEquiv k K G _ f.hom.hom

/-- Substitution evaluates the whole homomorphism on any affine test. -/
theorem affineCoefficientCurve_evaluate
    (A : Type u) [CommRing A] [Algebra k A] [Algebra K A] [IsScalarTower k K A]
    (c : A) :
    Lie.affineMap G
        ((MvPolynomial.aeval (fun _ : Fin 1 => c)).restrictScalars k)
        (affineCoefficientCurve k K G f) =
      Lie.affineBaseChangeEquiv k K G A
        (scalarPoint (CommRingCat.of K) _
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv c) ≫ f.hom.hom) := by
  rw [affineCoefficientCurve, ← Lie.affineBaseChangeEquiv_naturality]
  apply congrArg (Lie.affineBaseChangeEquiv k K G A)
  rw [Lie.affineMap_apply, scalarPoint_eq_algSpec_aeval]

variable (σ : K ≃ₐ[k] K)
    (f' : groupScheme (CommRingCat.of K) 1 ⟶
      (GroupScheme.baseChange (algebraBaseMap k K)).obj G)
    (hf : ∀ (U : Over (Spec (CommRingCat.of K))) (z : Γ(U.left, ⊤)),
      descentPoint (algebraBaseMap k K) (galoisBaseMap k K σ)
          (galoisBaseMap_over k K σ) G U
          (scalarPoint (CommRingCat.of K) U z ≫ f'.hom.hom) =
        scalarPoint (CommRingCat.of K) ((Over.map (galoisBaseMap k K σ)).obj U) z ≫
          f.hom.hom)

include hf in
/-- All-test scalar descent gives twisted coefficient evaluation. -/
theorem affinePoint_of_scalar_descent
    (A : Type u) [CommRing A] [Algebra k A] [Algebra K A] [IsScalarTower k K A]
    (c : A) :
    Lie.affineBaseChangeEquiv k K G A
        (scalarPoint (CommRingCat.of K) _
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv c) ≫ f'.hom.hom) =
      Lie.affineMap G
        ((MvPolynomial.aeval (fun _ : Fin 1 => (c : Lie.GaloisTestAlgebra σ A)) :
          MvPolynomial (Fin 1) K →ₐ[K] Lie.GaloisTestAlgebra σ A).restrictScalars k)
        (affineCoefficientCurve k K G f) := by
  calc
    _ = Lie.affineBaseChangeEquiv k K G (Lie.GaloisTestAlgebra σ A)
        (Lie.galoisTestPoint k K σ A G _) :=
      (Lie.affineBaseChangeEquiv_galoisTestPoint k K σ A G _).symm
    _ = _ := by
      rw [galoisTestPoint_of_scalar_descent k K G σ f f' hf]
      exact (affineCoefficientCurve_evaluate k K G f
        (Lie.GaloisTestAlgebra σ A) c).symm

include hf in
/-- All-test scalar descent conjugates the complete coefficient curve. -/
theorem affineCoefficientCurve_conjugate_of_scalar_descent :
    affineCoefficientCurve k K G f' =
      Lie.affineMap G (PolynomialGalois.lineConjugate k K σ)
        (affineCoefficientCurve k K G f) := by
  have h := affinePoint_of_scalar_descent k K G f σ f' hf
    (MvPolynomial (Fin 1) K) (MvPolynomial.X (0 : Fin 1))
  rw [scalarPoint_generic_eq_id, Category.id_comp,
    PolynomialGalois.aeval_generic_twisted] at h
  exact h

variable [IsAffineHom G.X.hom]

local instance :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

local instance steinbergGaloisDerivativesVectorGroupAffine :
    IsAffineHom (groupScheme (CommRingCat.of K) 1).X.hom :=
  isAffineHom_groupScheme (CommRingCat.of K) 1

include hf in
/-- All-test scalar descent transports the actual epsilon differential. -/
theorem derivative_of_scalar_descent :
    Lie.targetMapLinear f' K (standardEpsilon K) =
      Lie.baseChangeGaloisEquiv k K G σ (Lie.targetMapLinear f K (standardEpsilon K)) := by
  have h := affinePoint_of_scalar_descent k K G f σ f' hf
    (DualNumber K) (TrivSqZeroExt.inr (1 : K))
  rw [PolynomialGalois.aeval_epsilon_twisted, Lie.affineMap_comp,
    affineCoefficientCurve_evaluate] at h
  apply (Lie.kernelBaseChangeLinearEquiv k K G K).injective
  rw [Lie.baseChangeGaloisEquiv_apply, LinearEquiv.apply_symm_apply]
  apply Additive.toMul.injective
  apply Subtype.ext
  change Lie.affineBaseChangeEquiv k K G (DualNumber K)
      ((standardEpsilon K).toMul.val ≫ f'.hom.hom) =
    Lie.affineMap G
      (GeneralLinear.DualNumber.coefficientAlgMap (R := CommRingCat.of k) σ.toAlgHom)
      (Lie.affineBaseChangeEquiv k K G (DualNumber K)
        ((standardEpsilon K).toMul.val ≫ f.hom.hom))
  rw [standardEpsilon_val_eq_scalarPoint]
  exact h

end VectorGroup

namespace SplitPinning.NormalizedRootParametrization

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]

local instance :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

local instance :
    IsAffineHom (VectorGroup.groupScheme (CommRingCat.of K) 1).X.hom :=
  VectorGroup.isAffineHom_groupScheme (CommRingCat.of K) 1

variable {p : SplitPinning ((GroupScheme.baseChange (algebraBaseMap k K)).obj G)}
    {a : p.base.support} (x : p.NormalizedRootParametrization a) (σ : K ≃ₐ[k] K)

/-- The whole transported homomorphism has the conjugated coefficient curve. -/
theorem galoisHom_coefficientCurve :
    Lie.affineBaseChangeEquiv k K G (MvPolynomial (Fin 1) K)
        (x.galoisHom k K G σ).hom.hom =
      Lie.affineMap G (PolynomialGalois.lineConjugate k K σ)
        (x.coefficientCurve k K G) := by
  exact VectorGroup.affineCoefficientCurve_conjugate_of_scalar_descent k K G x.hom σ
    (x.galoisHom k K G σ) (x.galoisHom_point k K G σ)

/-- The derivative of actual transport is canonical semilinear transport of
the supplied root vector. -/
theorem galoisHom_derivative :
    Lie.targetMapLinear (x.galoisHom k K G σ) K (VectorGroup.standardEpsilon K) =
      Lie.baseChangeGaloisEquiv k K G σ (p.pinning.rootVector a) := by
  rw [← x.derivative]
  exact VectorGroup.derivative_of_scalar_descent k K G x.hom σ
    (x.galoisHom k K G σ) (x.galoisHom_point k K G σ)

end SplitPinning.NormalizedRootParametrization

end Langlands.GroupScheme
