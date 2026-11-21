import Langlands.TraceFormula.GeneralLinearBaseChangeLocal

/-! # Local coordinates of rational points and rational norm pairs -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.TraceFormula

open Langlands.Global Langlands.GroupScheme
open AdelicGroupAutomorphism BaseChange

universe u

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

local instance (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of K)

local instance (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of K)

set_option hygiene false in
local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)

set_option hygiene false in
local notation "Wₙ" => weilGroup K L GLₙ

section GroundPoints

variable [FiniteDimensional K L] (n : ℕ)

/-- Rational points of the Weil restriction are the upper rational matrices. -/
def rationalWeilGLEquiv :
    (Wₙ).affinePoints (CommAlgCat.of K K) ≃* GeneralLinear n L :=
  (AffineWeil.unitGroundPointsEquiv K L GLₙ (CommAlgCat.of K K)).trans
    ((GroupScheme.GeneralLinear.affinePointsEquiv (Fin n) (CommRingCat.of K)
      (CommAlgCat.of K (L ⊗[K] K))).trans
        (Units.mapEquiv (Algebra.TensorProduct.rid K K L).mapMatrix.toMulEquiv))

private theorem unitGroundPointsEquiv_naturality
    {A B : Type u} [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    (a : A →ₐ[K] B) (q : (Wₙ).affinePoints (CommAlgCat.of K A)) :
    AffineWeil.unitGroundPointsEquiv K L GLₙ (CommAlgCat.of K B)
        ((Wₙ).affinePointMap (CommAlgCat.ofHom a) q) =
      (GLₙ).affinePointMap (CommAlgCat.ofHom
        ((Algebra.TensorProduct.lTensor (S := L) L a).restrictScalars K))
        (AffineWeil.unitGroundPointsEquiv K L GLₙ (CommAlgCat.of K A) q) := by
  let eA := affinePointsBaseChangeMulEquiv K L (L ⊗[K] A) GLₙ
  let eB := affinePointsBaseChangeMulEquiv K L (L ⊗[K] B) GLₙ
  apply eB.injective
  have h := AffineWeil.pointsEquiv_naturality K L (AffineWeil.unitBaseChange K L GLₙ) a q
  change eB (eB.symm (AffineWeil.pointsEquiv K L (AffineWeil.unitBaseChange K L GLₙ)
    (CommAlgCat.of K B) ((Wₙ).affinePointMap (CommAlgCat.ofHom a) q))) = _
  rw [MulEquiv.apply_symm_apply]
  change _ = affinePointsBaseChangeMulEquiv K L (L ⊗[K] B) GLₙ _
  rw [← affinePointsBaseChangeMulEquiv_naturality]
  simpa only [AffineWeil.unitGroundPointsEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    using h

/-- Rational Weil coordinates intertwine the rational Galois action with
entrywise conjugation over `L`. -/
theorem rationalWeilGLEquiv_twist (σ : L ≃ₐ[K] L) (q : (Wₙ).affinePoints (CommAlgCat.of K K)) :
    rationalWeilGLEquiv K L n
        ((Wₙ).affinePointsTarget (unitGaloisAut K L GLₙ σ).hom (CommAlgCat.of K K) q) =
      entrywiseAut σ n (rationalWeilGLEquiv K L n q) := by
  simp only [rationalWeilGLEquiv, MulEquiv.trans_apply, unitGaloisAut_hom]
  rw [AffineWeil.unitGaloisAction_groundPoints]
  change Units.mapEquiv (Algebra.TensorProduct.rid K K L).mapMatrix.toMulEquiv
    (GroupScheme.GeneralLinear.affinePointsEquiv (Fin n) (CommRingCat.of K) _
      ((algSpec (CommRingCat.of K)).map (CommAlgCat.ofHom
        (TensorGaloisPoint.coefficientConjugate K L K σ)).op ≫ _)) = _
  rw [GroupScheme.GeneralLinear.affinePointsEquiv_naturality]
  apply Units.ext
  apply Matrix.ext
  intro a b
  have hcoef (z : L ⊗[K] K) :
      Algebra.TensorProduct.rid K K L (TensorGaloisPoint.coefficientConjugate K L K σ z) =
        σ (Algebra.TensorProduct.rid K K L z) := by
    obtain ⟨c, rfl⟩ := (Algebra.TensorProduct.rid K K L).symm.surjective z
    rw [AlgEquiv.apply_symm_apply, Algebra.TensorProduct.rid_symm_apply]
    change Algebra.TensorProduct.rid K K L (σ c ⊗ₜ[K] (1 : K)) = σ c
    simp
  exact hcoef _

end GroundPoints

variable [NumberField K]

private theorem atPlace_rational_apply
    (G : GroupScheme (Spec (CommRingCat.of K))) (i : Place K) (q : RationalGroupPoints K G) :
    AdelicGroupPoints.atPlace K G i (AdelicGroupPoints.rational K G q) =
      G.affinePointMap (CommAlgCat.ofHom (Algebra.ofId K (placeCompletion K i))) q := by
  change G.affinePointMap (CommAlgCat.ofHom (adeleProjection K i))
    (G.affinePointMap (CommAlgCat.ofHom (Algebra.ofId K (Adeles K))) q) = _
  rw [← MonoidHom.comp_apply, ← GroupScheme.affinePointMap_comp]
  have he : CommAlgCat.ofHom (Algebra.ofId K (Adeles K)) ≫
      CommAlgCat.ofHom (adeleProjection K i) = CommAlgCat.ofHom (Algebra.ofId K (placeCompletion K i)) := by
    ext1
    exact Subsingleton.elim _ _
  rw [he]

/-- The local points equivalence sends localization of an ordinary rational
point to entrywise completion of its rational matrix. -/
theorem localGLEquiv_atPlace_rational (n : ℕ) (i : Place K)
    (q : RationalGroupPoints K GLₙ) :
    localGLEquiv K n i (AdelicGroupPoints.atPlace K GLₙ i (AdelicGroupPoints.rational K GLₙ q)) =
      Matrix.GeneralLinearGroup.map (algebraMap K (placeCompletion K i))
        (GeneralLinearGroupPoints.rationalEquiv K n q) := by
  rw [atPlace_rational_apply]
  exact GroupScheme.GeneralLinear.affinePointsEquiv_naturality (n := Fin n) (R := CommRingCat.of K)
    (CommAlgCat.ofHom (Algebra.ofId K (placeCompletion K i))) q

/-- Scalar extension of upper coefficients into the actual local tensor algebra. -/
def upperRationalLocalMap (i : Place K) : L →ₐ[K] LocalBaseChangeAlgebra K L i :=
  Algebra.TensorProduct.includeRight

private theorem swap_tensorMap_eq (i : Place K) :
    (localSwap K L i).toRingHom.comp
        (Algebra.TensorProduct.lTensor (S := L) L (Algebra.ofId K (placeCompletion K i))).toRingHom =
      (upperRationalLocalMap K L i).toRingHom.comp
        (Algebra.TensorProduct.rid K K L).toRingHom := by
  apply RingHom.ext
  intro z
  obtain ⟨a, rfl⟩ := (Algebra.TensorProduct.rid K K L).symm.surjective z
  change localSwap K L i (Algebra.TensorProduct.lTensor (S := L) L
    (Algebra.ofId K (placeCompletion K i)) ((Algebra.TensorProduct.rid K K L).symm a)) =
    upperRationalLocalMap K L i (Algebra.TensorProduct.rid K K L
      ((Algebra.TensorProduct.rid K K L).symm a))
  rw [AlgEquiv.apply_symm_apply, Algebra.TensorProduct.rid_symm_apply]
  change (Algebra.ofId K (placeCompletion K i) 1) ⊗ₜ[K] a = (1 : placeCompletion K i) ⊗ₜ[K] a
  rw [map_one]

variable [FiniteDimensional K L] in
/-- The local points equivalence sends localization of a rational Weil
point to the upper rational matrix in the actual local tensor algebra. -/
theorem localPointsEquiv_atPlace_rational (n : ℕ) (i : Place K)
    (q : RationalGroupPoints K Wₙ) :
    localPointsEquiv K L n i (AdelicGroupPoints.atPlace K Wₙ i (AdelicGroupPoints.rational K Wₙ q)) =
      Matrix.GeneralLinearGroup.map (upperRationalLocalMap K L i).toRingHom
        (rationalWeilGLEquiv K L n q) := by
  rw [atPlace_rational_apply]
  simp only [localPointsEquiv, MulEquiv.trans_apply]
  rw [unitGroundPointsEquiv_naturality K L]
  rw [GroupScheme.affinePointMap_apply, GroupScheme.GeneralLinear.affinePointsEquiv_naturality]
  apply Units.ext
  apply Matrix.ext
  intro a b
  exact RingHom.congr_fun (swap_tensorMap_eq K L i) _

/-- The cyclic norm commutes with the upper rational coefficient map
into the completed tensor algebra. -/
theorem cyclicNorm_upperRationalLocalMap (σ : L ≃ₐ[K] L) (l n : ℕ) (i : Place K)
    (δ : GeneralLinear n L) :
    cyclicNorm (localGalois K L σ i) l
        (Matrix.GeneralLinearGroup.map (upperRationalLocalMap K L i).toRingHom δ) =
      Matrix.GeneralLinearGroup.map (upperRationalLocalMap K L i).toRingHom (cyclicNorm σ l δ) := by
  rw [cyclicNorm, cyclicNorm, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  rw [Function.comp_apply, ← localGalois_pow]
  apply Units.ext
  apply Matrix.ext
  intro a b
  change localGalois K L (σ ^ k) i ((1 : placeCompletion K i) ⊗ₜ[K] δ a b) =
    (1 : placeCompletion K i) ⊗ₜ[K] (σ ^ k) (δ a b)
  exact localGalois_tmul K L (σ ^ k) i 1 (δ a b)

/-- Associated rational matrices remain associated in the actual local
algebra at every place. -/
theorem localize_normAssociated (σ : L ≃ₐ[K] L) (l n : ℕ) (i : Place K)
    (δ : GeneralLinear n L) (γ : GeneralLinear n K) (h : IsNormAssociated σ l δ γ) :
    IsNormAssociated (localGalois K L σ i) l
      (Matrix.GeneralLinearGroup.map (upperRationalLocalMap K L i).toRingHom δ)
      (Matrix.GeneralLinearGroup.map (algebraMap K (placeCompletion K i)) γ) := by
  obtain ⟨y, hy⟩ := h
  let inc := Matrix.GeneralLinearGroup.map (n := Fin n) (upperRationalLocalMap K L i).toRingHom
  refine ⟨inc y, ?_⟩
  change (inc y)⁻¹ * cyclicNorm (localGalois K L σ i) l (inc δ) * inc y = _
  rw [cyclicNorm_upperRationalLocalMap K L σ l n i δ, ← map_inv, ← map_mul, ← map_mul, hy]
  apply Units.ext
  apply Matrix.ext
  intro a b
  change upperRationalLocalMap K L i (algebraMap K L (γ a b)) =
    algebraMap (placeCompletion K i) (LocalBaseChangeAlgebra K L i)
      (algebraMap K (placeCompletion K i) (γ a b))
  rw [(upperRationalLocalMap K L i).commutes, IsScalarTower.algebraMap_apply K (placeCompletion K i)]

/-- A rational norm pair, written in the ordinary and Weil-restriction
point groups, gives a norm pair in the actual matrix groups at every place. -/
def RationalLocalNormAssociationStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [Algebra K L] [FiniteDimensional K L]
    (σ : L ≃ₐ[K] L) (l n : ℕ)
    (δ : RationalGroupPoints K Wₙ) (γ : RationalGroupPoints K GLₙ),
    IsNormAssociated σ l (rationalWeilGLEquiv K L n δ) (GeneralLinearGroupPoints.rationalEquiv K n γ) →
    ∀ i : Place K, IsNormAssociated (localGalois K L σ i) l
      (localPointsEquiv K L n i
        (AdelicGroupPoints.atPlace K Wₙ i (AdelicGroupPoints.rational K Wₙ δ)))
      (localGLEquiv K n i
        (AdelicGroupPoints.atPlace K GLₙ i (AdelicGroupPoints.rational K GLₙ γ)))

theorem rationalLocalNormAssociation : RationalLocalNormAssociationStatement.{u} := by
  intro K L _ _ _ _ _ σ l n δ γ h i
  rw [localPointsEquiv_atPlace_rational, localGLEquiv_atPlace_rational]
  exact localize_normAssociated K L σ l n i _ _ h

end Langlands.TraceFormula
