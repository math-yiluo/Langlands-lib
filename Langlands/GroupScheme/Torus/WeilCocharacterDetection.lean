import Langlands.GroupScheme.Torus.WeilCocharacterTransfer

/-! # Detection of cocharacters by finite-Galois transfer -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open Langlands.Algebra.SeparableTensor
open scoped TensorProduct CategoryTheory.MonObj BigOperators

namespace Langlands.GroupScheme.WeilGm

set_option backward.isDefEq.respectTransparency false

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  (A : Type u) [CommRing A] [Algebra k A] [Algebra K A] [IsScalarTower k K A]

/-- Evaluate the first tensor factor at an embedding. -/
def transferCoordinate (tau : K →ₐ[k] K) : K ⊗[k] A →ₐ[k] A :=
  tensorCoordinate (IsScalarTower.toAlgHom k K A) tau

@[simp]
theorem transferCoordinate_tmul (tau : K →ₐ[k] K) (c : K) (a : A) :
    transferCoordinate k K A tau (c ⊗ₜ[k] a) = algebraMap K A (tau c) * a := rfl

/-- Multiplication of the scalar and test-algebra factors is linear over `K`. -/
def transferMultiply : K ⊗[k] A →ₐ[K] A :=
  Algebra.TensorProduct.lift (Algebra.ofId K A) (AlgHom.id k A)
    (fun _ _ => Commute.all _ _)

theorem transferMultiply_restrictScalars :
    (transferMultiply k K A).restrictScalars k =
      transferCoordinate k K A (AlgHom.id k K) := by
  ext <;> simp [transferMultiply]

variable [FiniteDimensional k K] [IsGalois k K]

local instance weilCocharacterDetectionEmbeddingDecidableEq : DecidableEq (K →ₐ[k] K) := Classical.decEq _

/-- Units in the tensor product split into their embedding coordinates. -/
def transferUnitsEquiv : (K ⊗[k] A)ˣ ≃* ((K →ₐ[k] K) → Aˣ) :=
  (Units.mapEquiv
    (decompositionTensorEquiv k K K A (K →ₐ[k] K)
      (separableEmbeddingDecomposition k K K (IsGalois.splits k))).toMulEquiv).trans
    MulEquiv.piUnits

theorem transferUnitsEquiv_apply (x : (K ⊗[k] A)ˣ) (tau : K →ₐ[k] K) :
    transferUnitsEquiv k K A x tau =
      Units.map (transferCoordinate k K A tau).toMonoidHom x := by
  apply Units.ext
  exact embeddingDecompositionTensorEquiv_apply k K K
    (embeddingEvaluationStatement k K K (IsGalois.splits k)) A x.val tau

/-- A tensor unit whose only nontrivial embedding coordinate is the identity. -/
def identitySupportedUnit (t : Aˣ) : (K ⊗[k] A)ˣ :=
  (transferUnitsEquiv k K A).symm
    (fun tau => if tau = AlgHom.id k K then t else 1)

@[simp]
theorem transferCoordinate_identitySupportedUnit (t : Aˣ) (tau : K →ₐ[k] K) :
    Units.map (transferCoordinate k K A tau).toMonoidHom
        (identitySupportedUnit k K A t) =
      if tau = AlgHom.id k K then t else 1 := by
  rw [← transferUnitsEquiv_apply]
  exact congrFun ((transferUnitsEquiv k K A).apply_symm_apply _) tau

omit [FiniteDimensional k K] [IsGalois k K] in
/-- Undo a semilinear automorphism on the second factor to get a `K`-linear map. -/
def untwistedTransferCoordinate (q : A ≃ₐ[k] A) : K ⊗[k] A →ₐ[K] A :=
  Algebra.TensorProduct.lift (Algebra.ofId K A) q.symm.toAlgHom
    (fun _ _ => Commute.all _ _)

omit [FiniteDimensional k K] [IsGalois k K] in
theorem transferCoordinate_factor (sigma : K ≃ₐ[k] K) (q : A ≃ₐ[k] A)
    (hq : ∀ c : K, q (algebraMap K A c) = algebraMap K A (sigma c)) :
    transferCoordinate k K A sigma.toAlgHom =
      q.toAlgHom.comp ((untwistedTransferCoordinate k K A q).restrictScalars k) := by
  ext c <;> simp [transferCoordinate, tensorCoordinate, untwistedTransferCoordinate, hq]

variable (Z : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffine Z.X.left]

local notation "Z_K" =>
  Functor.obj (GroupScheme.baseChange (algebraBaseMap k K)) Z.toGrp

omit [IsAffine Z.X.left] [FiniteDimensional k K] [IsGalois k K] in
theorem cocharacterValue_coordinate_eq_one
    (nu : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ Z_K)
    (sigma : K ≃ₐ[k] K) (q : A ≃ₐ[k] A)
    (hq : ∀ c : K, q (algebraMap K A c) = algebraMap K A (sigma c))
    (x : (K ⊗[k] A)ˣ)
    (hx : Units.map (transferCoordinate k K A sigma.toAlgHom).toMonoidHom x = 1) :
    Lie.affineMap Z.toGrp (transferCoordinate k K A sigma.toAlgHom)
      (cocharacterValue k K Z nu (K ⊗[k] A) x) = 1 := by
  have hu : Units.map (untwistedTransferCoordinate k K A q).toMonoidHom x = 1 := by
    apply Units.ext
    apply q.injective
    have hv := congrArg Units.val hx
    rw [transferCoordinate_factor k K A sigma q hq] at hv
    exact hv.trans (map_one q).symm
  rw [transferCoordinate_factor k K A sigma q hq, Lie.affineMap_comp]
  rw [← cocharacterValue_naturality k K Z nu
    (untwistedTransferCoordinate k K A q) x, hu, map_one, map_one]

/-- Evaluating the descended norm expresses transfer as a product of embedding values. -/
theorem transferPoint_eq_prod_coordinates
    (nu : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ Z_K) (x : (K ⊗[k] A)ˣ) :
    transferPoint k K Z nu A x =
      ∏ sigma : K ≃ₐ[k] K,
        Lie.affineMap Z.toGrp (transferCoordinate k K A sigma.toAlgHom)
          (cocharacterValue k K Z nu (K ⊗[k] A) x) := by
  have he : ((transferMultiply k K A).restrictScalars k).comp
      (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A) = AlgHom.id k A := by
    ext a
    simp [transferMultiply]
  have hc (sigma : K ≃ₐ[k] K) :
      ((transferMultiply k K A).restrictScalars k).comp
          (TensorGaloisPoint.coefficientConjugate k K A sigma) =
        transferCoordinate k K A sigma.toAlgHom := by
    ext c <;> simp [transferMultiply, transferCoordinate, tensorCoordinate,
      TensorGaloisPoint.coefficientConjugate]
  have h := congrArg (Lie.affineMap Z.toGrp ((transferMultiply k K A).restrictScalars k))
    (TensorGaloisPoint.extend_norm k K A Z (cocharacterValue k K Z nu (K ⊗[k] A) x))
  simp only [TensorGaloisPoint.extend, ← Lie.affineMap_comp, he,
    map_prod, TensorGaloisPoint.conjugate, hc] at h
  rw [Lie.affineMap_id] at h
  exact h

/-- A unit supported in the identity factor recovers the original cocharacter value. -/
theorem transferPoint_identitySupportedUnit
    (nu : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ Z_K)
    (hsemilinear : ∀ sigma : K ≃ₐ[k] K, ∃ q : A ≃ₐ[k] A,
      ∀ c : K, q (algebraMap K A c) = algebraMap K A (sigma c))
    (t : Aˣ) :
    transferPoint k K Z nu A (identitySupportedUnit k K A t) =
      cocharacterValue k K Z nu A t := by
  classical
  rw [transferPoint_eq_prod_coordinates]
  have hf (sigma : K ≃ₐ[k] K) :
      Lie.affineMap Z.toGrp (transferCoordinate k K A sigma.toAlgHom)
          (cocharacterValue k K Z nu (K ⊗[k] A) (identitySupportedUnit k K A t)) =
        if sigma = 1 then cocharacterValue k K Z nu A t else 1 := by
    by_cases hs : sigma = 1
    · subst sigma
      rw [ite_eq_left rfl]
      change Lie.affineMap Z.toGrp (transferCoordinate k K A (AlgHom.id k K)) _ = _
      rw [← transferMultiply_restrictScalars,
        ← cocharacterValue_naturality]
      congr 1
      change Units.map ((transferMultiply k K A).restrictScalars k).toMonoidHom
        (identitySupportedUnit k K A t) = t
      rw [transferMultiply_restrictScalars, transferCoordinate_identitySupportedUnit,
        ite_eq_left rfl]
    · rw [ite_eq_right hs]
      obtain ⟨q, hq⟩ := hsemilinear sigma
      apply cocharacterValue_coordinate_eq_one k K A Z nu sigma q hq
      rw [transferCoordinate_identitySupportedUnit, ite_eq_right]
      intro h
      apply hs
      exact AlgEquiv.ext fun c => DFunLike.congr_fun h c
  simp only [hf]
  simp

omit [FiniteDimensional k K] [IsGalois k K] in
/-- Laurent polynomials carry every coefficient automorphism semilinearly. -/
theorem laurent_semilinear (sigma : K ≃ₐ[k] K) :
    ∃ q : LaurentPolynomial K ≃ₐ[k] LaurentPolynomial K,
      ∀ c : K, q (algebraMap K (LaurentPolynomial K) c) =
        algebraMap K (LaurentPolynomial K) (sigma c) := by
  refine ⟨AddMonoidAlgebra.mapAlgEquiv k ℤ sigma, ?_⟩
  intro c
  change AddMonoidAlgebra.mapAlgHom ℤ sigma.toAlgHom
    (AddMonoidAlgebra.single 0 c) = AddMonoidAlgebra.single 0 (sigma c)
  exact AddMonoidAlgebra.mapAlgHom_single sigma.toAlgHom 0 c

/-- Identity-factor recovery always applies to the universal Laurent test algebra. -/
theorem transferPoint_identitySupportedLaurentUnit
    (nu : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ Z_K)
    (t : (LaurentPolynomial K)ˣ) :
    transferPoint k K Z nu (LaurentPolynomial K)
        (identitySupportedUnit k K (LaurentPolynomial K) t) =
      cocharacterValue k K Z nu (LaurentPolynomial K) t :=
  transferPoint_identitySupportedUnit k K (LaurentPolynomial K) Z nu
    (laurent_semilinear k K) t

/-- A zero actual transfer vanishes at every tensor unit over every test algebra. -/
theorem transferPoint_eq_one_of_transfer_eq_zero
    (nu : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ Z_K)
    (hzero : cocharacterTransfer k K Z nu = 0)
    (B : Type u) [CommRing B] [Algebra k B] (x : (K ⊗[k] B)ˣ) :
    transferPoint k K Z nu B x = 1 := by
  let y := (Corepresented.affinePointsEquiv _ (corepresentableBy (CommRingCat.of k) K)
    (CommAlgCat.of k B)).symm x
  have he := cocharacterTransfer_affinePoints k K Z nu (CommAlgCat.of k B) y
  have hy : Corepresented.affinePointsEquiv _ (corepresentableBy (CommRingCat.of k) K)
      (CommAlgCat.of k B) y = x := MulEquiv.apply_symm_apply _ x
  rw [hy, hzero] at he
  have hz : y ≫ (0 : groupScheme (CommRingCat.of k) K ⟶ Z.toGrp).hom.hom = 1 :=
    MonObj.comp_one y
  exact he.symm.trans hz

/-- Finite-Galois Weil transfer detects whether an actual cocharacter is zero. -/
theorem cocharacter_eq_zero_of_transfer_eq_zero
    (nu : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ Z_K)
    (hzero : cocharacterTransfer k K Z nu = 0) : nu = 0 := by
  have hv : cocharacterValue k K Z nu (LaurentPolynomial K)
      (GeneralLinear.cocharacterLaurentUnit (CommRingCat.of K)) = 1 := by
    rw [← transferPoint_identitySupportedLaurentUnit]
    exact transferPoint_eq_one_of_transfer_eq_zero k K Z nu hzero _ _
  apply Gm.hom_ext_universalPoint (CommRingCat.of K)
  apply (Lie.affineBaseChangeEquiv k K Z.toGrp (LaurentPolynomial K)).injective
  rw [GeneralLinear.universalPoint_eq_algebraPointsEquiv_symm]
  rw [show (0 : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ Z_K).hom.hom = 1 from rfl,
    MonObj.comp_one, map_one]
  exact hv

/-- Every nonzero cocharacter has nonzero finite-Galois Weil transfer. -/
theorem cocharacterTransfer_ne_zero
    (nu : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ Z_K) (hnu : nu ≠ 0) :
    cocharacterTransfer k K Z nu ≠ 0 :=
  fun hzero => hnu (cocharacter_eq_zero_of_transfer_eq_zero k K Z nu hzero)

end Langlands.GroupScheme.WeilGm
