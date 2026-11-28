import Langlands.Shimura.Unitary.DiscriminantPresentation
import Langlands.Shimura.Unitary.SymmetricReducedCharpoly
import Langlands.Algebra.UnitaryDiscriminant.HermitianBaseChange
import Langlands.ClassFieldTheory.Local.FiniteArtinTransport

/-! # The discriminant in a completed Hermitian matrix chart -/

noncomputable section

universe u v w

open Matrix
open scoped TensorProduct

namespace Langlands.Shimura.FiniteUnitary

open NumberField _root_.Algebra Langlands.UnitaryDiscriminant
open Langlands.LocalClassField Langlands.LocalClassField.FiniteArtinTransport
open Langlands.ClassFieldTheory.Local

variable {E F : Type u} {K : Type v} {C : Type w}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K] [Algebra E K] [IsQuadraticExtension E K]
  [Field F] [Algebra E F] [CharZero F]
  [Field C] [Algebra F C] [Algebra K C] [Algebra E C]
  [IsScalarTower E F C] [IsScalarTower E K C] [IsQuadraticExtension F C]
  {A : CSA.{v, v} K} [Algebra E A] [IsScalarTower E K A] {m : ℕ}
  (P : EvenDiscriminantPresentation E A m) (D : CentralSimpleUnitaryData E K A (2 * m))
  (φ : C ≃ₐ[F] C) (hφ : φ ≠ 1)
  (hφK : ∀ k, φ (algebraMap K C k) = algebraMap K C (cmConjugation E K k))
  (e : F ⊗[E] A ≃ₐ[F] Matrix (Fin (2 * m)) (Fin (2 * m)) C)
  (he : ∀ k, e (1 ⊗ₜ[E] algebraMap K A k) =
    algebraMap C (Matrix (Fin (2 * m)) (Fin (2 * m)) C) (algebraMap K C k))
  (H : GL (Fin (2 * m)) C)
  (hH : ((H : Matrix (Fin (2 * m)) (Fin (2 * m)) C).map φ)ᵀ = H)
  (hAdj : ∀ a : A, e (1 ⊗ₜ[E] D.involution a) =
    ((H⁻¹ : GL (Fin (2 * m)) C) : Matrix _ _ C) * ((e (1 ⊗ₜ[E] a)).map φ)ᵀ *
      (H : Matrix _ _ C))
  (d : Fˣ) (hd : algebraMap F C (d : F) = (-1 : C)^m * (GeneralLinearGroup.det H : C))

include hφ hφK he hH hAdj hd in
set_option maxRecDepth 8192 in
omit [NumberField E] in
/-- For a completed Hermitian chart, the scalar-extended discriminant class
vanishes exactly when the signed Gram determinant is a norm of the actual coefficient field. -/
theorem discriminantClass_eq_zero_of_hermitian_chart :
    Brauer.scalarExtension F (P.brauerClass D.toSecondKindInvolution) = 0 ↔
      d ∈ normSubgroup F C := by
  classical
  let : Small.{u} C := Module.Finite.small F C
  let C' := Shrink.{u} C
  let j : C' ≃ₐ[F] C := Shrink.algEquiv F C
  let : IsQuadraticExtension F C' :=
    ⟨j.toLinearEquiv.finrank_eq.trans (IsQuadraticExtension.finrank_eq_two F C)⟩
  let jE : C' ≃ₐ[E] C := Shrink.algEquiv E C
  let : IsScalarTower E F C' := IsScalarTower.of_algebraMap_eq fun x => by
    apply j.injective
    change jE (algebraMap E C' x) = j (algebraMap F C' (algebraMap E F x))
    rw [jE.commutes, j.commutes, ← IsScalarTower.algebraMap_apply E F C]
  let R := P.pair
  let L := R.center
  let B := R.algebra
  let i : L →+* C' := j.symm.toRingHom.comp ((algebraMap K C).comp R.centerEquiv.toRingHom)
  let : Algebra L C' := i.toAlgebra
  let : IsScalarTower E L C' := IsScalarTower.of_algebraMap_eq fun x => by
    apply j.injective
    change jE (algebraMap E C' x) =
      j (j.symm (algebraMap K C (R.centerEquiv (algebraMap E L x))))
    rw [jE.commutes, j.apply_symm_apply, R.centerEquiv.commutes,
      ← IsScalarTower.algebraMap_apply E K C]
  let : Algebra E B := Algebra.compHom B (algebraMap E L)
  let eB : B ≃ₐ[E] A := AlgEquiv.ofRingEquiv (f := R.algebraEquiv) fun x => by
    change R.algebraEquiv (algebraMap L B (algebraMap E L x)) = algebraMap E A x
    rw [R.scalar_eq, R.centerEquiv.commutes, ← IsScalarTower.algebraMap_apply E K A]
  let N := Fin (2 * m)
  let J : Matrix N N C ≃ₐ[F] Matrix N N C' := j.symm.mapMatrix
  let e' := (Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[F] F) eB).trans (e.trans J)
  have he'_pure (b : B) : e' (1 ⊗ₜ[E] b) = J (e (1 ⊗ₜ[E] R.algebraEquiv b)) := rfl
  have he' (l : L) : e' (1 ⊗ₜ[E] algebraMap L B l) =
      algebraMap C' (Matrix N N C') (algebraMap L C' l) := by
    rw [he'_pure, R.scalar_eq, he]
    apply Matrix.ext
    intro a b
    change j.symm (Matrix.scalar N (algebraMap K C (R.centerEquiv l)) a b) =
      Matrix.scalar N (j.symm (algebraMap K C (R.centerEquiv l))) a b
    by_cases hab : a = b <;> simp [Matrix.scalar_apply, hab]
  let f := matrixChartOfCenterCompatible (E := E) (S := F) (K := L) (L := C')
    (R.algebra_finrank.trans D.dimension) e'.toAlgHom e'.surjective he'
  have hfbase (b : B) : f.val (1 ⊗ₜ[L] b) = J (e (1 ⊗ₜ[E] R.algebraEquiv b)) :=
    (f.property b).trans (he'_pure b)
  let φ' := j.trans (φ.trans j.symm)
  have hφ' : φ' ≠ 1 := by
    intro h
    apply hφ
    apply AlgEquiv.ext
    intro x
    obtain ⟨y, rfl⟩ := j.surjective x
    have heq := congrArg (fun z : C' ≃ₐ[F] C' => j (z y)) h
    exact (j.apply_symm_apply _).symm.trans heq
  have hφ'_compat (l : L) :
      φ' (algebraMap L C' l) = algebraMap L C' (R.centerAutomorphism (cmConjugation E K) l) := by
    change j.symm (φ (j (j.symm (algebraMap K C (R.centerEquiv l))))) =
      j.symm (algebraMap K C (R.centerEquiv (R.centerAutomorphism (cmConjugation E K) l)))
    rw [j.apply_symm_apply, hφK, R.centerAutomorphism_equiv]
  let c : AlgebraInvolution F C' :=
    { linear := φ'.toLinearEquiv.toLinearMap
      map_one := φ'.map_one
      map_mul := fun x y => (φ'.map_mul x y).trans (mul_comm _ _)
      involutive := UnitaryDiscriminant.apply_apply_of_ne_one hφ' }
  let H' : GL N C' := Units.map J.toMonoidHom H
  have hJ (X : Matrix N N C) : ((J X).map φ')ᵀ = J ((X.map φ)ᵀ) := by
    apply Matrix.ext
    intro i j'
    change j.symm (φ (j (j.symm (X j' i)))) = j.symm (φ (X j' i))
    rw [j.apply_symm_apply]
  have hH' : ((H' : Matrix N N C').map φ')ᵀ = H' :=
    (hJ (H : Matrix N N C)).trans (congrArg J hH)
  have hH'' : matrixTranspose c (2 * m) (H' : Matrix N N C') = H' := by
    exact hH'
  let adj := (matrixTranspose c (2 * m)).adjoint H' hH''
  let t (b : C' ⊗[L] B) := f.val.symm (adj (f.val b))
  have ht : IsUnitaryInvolution φ' t := by
    refine ⟨fun x y => f.val.injective ?_, fun x y => f.val.injective ?_,
      fun x => f.val.injective ?_, fun z => f.val.injective ?_⟩
    · simp only [t, AlgEquiv.apply_symm_apply, map_add, adj.apply_add]
    · simp only [t, AlgEquiv.apply_symm_apply, map_mul, adj.apply_mul]
    · simp only [t, AlgEquiv.apply_symm_apply, adj.apply_apply]
    · simp only [t, AlgEquiv.apply_symm_apply]
      rw [f.val.commutes z, f.val.commutes (φ' z)]
      have hscalar : matrixTranspose c (2 * m) (algebraMap C' (Matrix N N C') z) =
          algebraMap C' (Matrix N N C') (φ' z) := by
        apply Matrix.ext
        intro i j
        change φ' (Matrix.scalar N z j i) = Matrix.scalar N (φ' z) i j
        by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij, eq_comm]
      change (↑H'⁻¹ : Matrix N N C') *
        matrixTranspose c (2 * m) (algebraMap C' (Matrix N N C') z) * (H' : Matrix N N C') =
        algebraMap C' (Matrix N N C') (φ' z)
      rw [hscalar, ← Algebra.commutes (φ' z) (↑H'⁻¹ : Matrix N N C'),
        Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  have htbase (b : B) :
      t (1 ⊗ₜ[L] b) = 1 ⊗ₜ[L] R.involution D.involution b := by
    apply f.val.injective
    simp only [t, AlgEquiv.apply_symm_apply]
    rw [hfbase b, hfbase (R.involution D.involution b), R.involution_equiv]
    change (H'⁻¹ : GL N C').val * ((J (e (1 ⊗ₜ[E] R.algebraEquiv b))).map φ')ᵀ *
      H'.val = J (e (1 ⊗ₜ[E] D.involution (R.algebraEquiv b)))
    rw [hJ, hAdj, map_mul, map_mul]
    have hInv : (H'⁻¹ : GL N C').val = J ((H⁻¹ : GL N C).val) := by
      change ((Units.map J.toMonoidHom H)⁻¹ : GL N C').val = _
      rw [← map_inv]
      rfl
    rw [hInv]
    rfl
  have hd' : algebraMap F C' (d : F) = (-1 : C')^m * (GeneralLinearGroup.det H' : C') := by
    rw [← j.symm.commutes, hd, map_mul, map_pow, map_neg, map_one]
    congr 1
    change j.symm.toRingHom ((H : Matrix N N C).det) = ((H : Matrix N N C).map j.symm).det
    exact RingHom.map_det j.symm.toRingHom _
  have hnorm := scalarExtension_discriminantClass_eq_zero_iff_norm P.center_ne_one hφ' hφ'_compat
    (P.isUnitary D.toSecondKindInvolution) ht htbase P.splitting.chart f.val H' hH'
    (fun x => by simp only [t, AlgEquiv.apply_symm_apply]; rfl) d hd'
  refine hnorm.trans ?_
  have hunit : Units.mapEquiv (RingEquiv.refl F).toMulEquiv d = d := Units.ext rfl
  simpa only [hunit] using (mem_normSubgroup_map_iff (RingEquiv.refl F) j.toRingEquiv
    (RingHom.ext fun x => (j.commutes x).symm) d).symm

end Langlands.Shimura.FiniteUnitary
