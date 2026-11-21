import Langlands.GroupScheme.CliffordSpin.ScalarKernel
import Langlands.GroupScheme.OrthogonalMatrix.Hyperbolic
import Langlands.LinearAlgebra.CliffordUnitReflections
import Mathlib.Algebra.Polynomial.Laurent

/-! # A connected Clifford family through the scalar kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.CliffordSpin

open CliffordAlgebra Langlands.QuadraticForm Quaternionic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 850000

section ScalarChange

variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V] [Invertible (2 : F)]
  (Q : QuadraticForm F V) {A B : Type u} [CommRing A] [CommRing B] [Algebra F A] [Algebra F B]

private abbrev vectorMap (f : A →ₐ[F] B) : A ⊗[F] V →ₗ[F] B ⊗[F] V :=
  TensorProduct.map f.toLinearMap LinearMap.id

omit [Invertible (2 : F)] in
private theorem vectorMap_smul (f : A →ₐ[F] B) (a : A) (x : A ⊗[F] V) :
    vectorMap f (a • x) = f a • vectorMap f x := by
  induction x using TensorProduct.inductionOn with
  | tmul t v => simp [TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

private theorem polar_vectorMap (f : A →ₐ[F] B) (x y : A ⊗[F] V) :
    QuadraticMap.polar (Q.baseChange B) (vectorMap f x) (vectorMap f y) =
      f (QuadraticMap.polar (Q.baseChange A) x y) := by
  let : Invertible (2 : A) := (Invertible.map (algebraMap F A) 2).copy 2 (map_ofNat _ _).symm
  let : Invertible (2 : B) := (Invertible.map (algebraMap F B) 2).copy 2 (map_ofNat _ _).symm
  change (Q.baseChange B).polarBilin (vectorMap f x) (vectorMap f y) = f ((Q.baseChange A).polarBilin x y)
  rw [QuadraticForm.polarBilin_baseChange, QuadraticForm.polarBilin_baseChange]
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
  | tmul a v =>
    induction y using TensorProduct.inductionOn with
    | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | tmul c w =>
      simp only [TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply,
        LinearMap.BilinForm.baseChange_tmul, Algebra.smul_def, map_mul, AlgHom.commutes]

private theorem quadratic_vectorMap (f : A →ₐ[F] B) (x : A ⊗[F] V) :
    Q.baseChange B (vectorMap f x) = f (Q.baseChange A x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a v => simp [Algebra.smul_def, AlgHom.commutes]
  | add x y hx hy =>
    rw [map_add, QuadraticMap.map_add (⇑(Q.baseChange B)), QuadraticMap.map_add (⇑(Q.baseChange A)),
      polar_vectorMap Q f, hx, hy, map_add, map_add]

private theorem tensorMap_cliffordVector (f : A →ₐ[F] B) (x : A ⊗[F] V) :
    tensorMap Q f (toBaseChange A Q (CliffordAlgebra.ι (Q.baseChange A) x)) =
      toBaseChange B Q (CliffordAlgebra.ι (Q.baseChange B) (vectorMap f x)) := by
  induction x using TensorProduct.inductionOn with
  | tmul a v => simp [tensorMap]
  | add x y hx hy => simp only [map_add, hx, hy]

end ScalarChange

variable {F : Type u} [Field F] [CharZero F] [Invertible (2 : F)] {n : ℕ} [NeZero n]
  (q : (FirstKindInvolution.scalar F).QuadraticForms (Fin n))

local notation "τ" => FirstKindInvolution.scalar F
local notation "Q" => Matrix.toQuadraticForm' (FirstKindInvolution.polar τ q)
local notation "b" => Pi.basisFun F (Fin n)
local notation "P" => groupScheme Q b
local notation "V" => (Fin n → F)

/-- The affine point defined by a coefficient scalar of square one. -/
def scalarPoint (K : Type u) [CommRing K] [Algebra F K] (a : rootsOfUnity 2 K) :
    (P).affinePoints (CommAlgCat.of F K) :=
  (affinePairEquiv Q b (CommAlgCat.of F K)).symm (scalarPair Q K a)

omit [CharZero F] [NeZero n] in
@[simp] theorem scalarPoint_one (K : Type u) [CommRing K] [Algebra F K] :
    scalarPoint q K 1 = 1 :=
  ((affinePairEquiv Q b (CommAlgCat.of F K)).symm.toMonoidHom.comp (scalarPair Q K)).map_one

variable (K : Type u) [Field K] [Algebra F K]

/-- Specialization of the Laurent parameter to a unit of the coefficient field. -/
def evaluateLaurent (s : Kˣ) : LaurentPolynomial K →ₐ[F] K where
  toRingHom := LaurentPolynomial.eval₂ (RingHom.id K) s
  commutes' r := by
    rw [IsScalarTower.algebraMap_apply F K (LaurentPolynomial K)]
    exact LaurentPolynomial.eval₂_C _ _ _

omit [CharZero F] [Invertible (2 : F)] [NeZero n] in
private theorem vectorMap_evaluateLaurent (s : Kˣ) (v : K ⊗[F] V) :
    vectorMap (evaluateLaurent (F := F) K s)
      (vectorMap (IsScalarTower.toAlgHom F K (LaurentPolynomial K)) v) = v := by
  induction v using TensorProduct.inductionOn with
  | add v w hv hw => simp only [map_add, hv, hw]
  | tmul a x =>
    simp only [TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply]
    congr 1
    exact LaurentPolynomial.eval₂_C (RingHom.id K) s a

omit [CharZero F] [NeZero n] in
private theorem coefficientPair_eq_of_unit_eq
    (x y : coefficientSubgroup Q b K) (h : x.val.1 = y.val.1) : x = y := by
  let : Invertible (2 : K) := (Invertible.map (algebraMap F K) 2).copy 2 (map_ofNat _ _).symm
  let D := (Q).baseChange K
  let E := coefficientLiftEquiv Q K
  let z := E x
  let w := E y
  have hunit : CliffordSpinLift.unit D z = CliffordSpinLift.unit D w :=
    congrArg (Units.map (ofBaseChange K Q).toMonoidHom) h
  have hι : Function.Injective (CliffordAlgebra.ι D) := by
    intro v₁ v₂ h
    apply (ExteriorAlgebra.ι_leftInverse (R := K)).injective
    have hh := congrArg (equivExterior D) h
    change changeForm changeForm.associated_neg_proof (CliffordAlgebra.ι D v₁) =
      changeForm changeForm.associated_neg_proof (CliffordAlgebra.ι D v₂) at hh
    rw [changeForm_ι, changeForm_ι] at hh
    exact hh
  apply E.injective
  apply Subtype.ext
  apply Prod.ext hunit
  apply LinearEquiv.ext
  intro v
  apply hι
  change CliffordAlgebra.ι D (CliffordSpinLift.vectorAction D z v) =
    CliffordAlgebra.ι D (CliffordSpinLift.vectorAction D w v)
  rw [← CliffordSpinLift.unit_conj_vector D z v, ← CliffordSpinLift.unit_conj_vector D w v, hunit]

variable [IsAlgClosed K]

omit [NeZero n] in
/-- The Clifford lift group has a Laurent-parameter point over an algebraically closed
coefficient field whose values at all square roots of unity are the corresponding scalar points. -/
theorem exists_laurentPoint_through_scalarKernel (hq : (τ).IsNondegenerateQuadratic q) (hn : 2 ≤ n) :
    ∃ x : (P).affinePoints (CommAlgCat.of F (LaurentPolynomial K)),
      ∀ t : rootsOfUnity 2 K,
        GroupScheme.affinePointMap (P) (CommAlgCat.ofHom (evaluateLaurent (F := F) K t.val)) x =
          scalarPoint q K t := by
  let D := (Q).baseChange K
  let c := (b).baseChange K
  let : Module.Finite K (K ⊗[F] V) := Module.Finite.of_basis c
  have hdim : 1 < Module.finrank K (K ⊗[F] V) := by
    rw [Module.finrank_eq_card_basis c, Fintype.card_fin]
    omega
  obtain ⟨e, f, he, hf, hef⟩ := OrthogonalMatrix.exists_hyperbolicPair hdim D
    (nondegenerate_polar_baseChange q hq K).1
  let A := LaurentPolynomial K
  let Qₐ := (Q).baseChange A
  let incl := IsScalarTower.toAlgHom F K A
  let eₐ := vectorMap incl e
  let fₐ := vectorMap incl f
  let v := eₐ + fₐ
  let w := (LaurentPolynomial.T (R := K) 1) • eₐ + (LaurentPolynomial.T (R := K) (-1)) • fₐ
  have heₐ : Qₐ eₐ = 0 := by rw [show Qₐ eₐ = incl (D e) from quadratic_vectorMap Q incl e, he, map_zero]
  have hfₐ : Qₐ fₐ = 0 := by rw [show Qₐ fₐ = incl (D f) from quadratic_vectorMap Q incl f, hf, map_zero]
  have hefₐ : QuadraticMap.polar Qₐ eₐ fₐ = 1 := by
    rw [show QuadraticMap.polar Qₐ eₐ fₐ = incl (QuadraticMap.polar D e f) from polar_vectorMap Q incl e f,
      hef, map_one]
  have hv : Qₐ v = 1 := by
    change Qₐ (eₐ + fₐ) = 1
    rw [QuadraticMap.map_add (⇑Qₐ), heₐ, hfₐ, hefₐ, zero_add, zero_add]
  have hw : Qₐ w = 1 := by
    change Qₐ (_ • eₐ + _ • fₐ) = 1
    rw [QuadraticMap.map_add (⇑Qₐ), Qₐ.map_smul, Qₐ.map_smul, heₐ, hfₐ, smul_zero, smul_zero,
      zero_add, zero_add, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hefₐ,
      smul_eq_mul, smul_eq_mul, mul_one, ← LaurentPolynomial.T_add]
    exact LaurentPolynomial.T_zero
  let s := unitReflectionPair Qₐ ((b).baseChange A) v w hv hw
  let y := (coefficientLiftEquiv Q A).symm s
  let x := (affinePairEquiv Q b (CommAlgCat.of F A)).symm y
  refine ⟨x, fun t => ?_⟩
  let φ : A →ₐ[F] K := evaluateLaurent K t.val
  let z := GroupScheme.affinePointMap (P) (CommAlgCat.ofHom φ) x
  apply (affinePairEquiv Q b (CommAlgCat.of F K)).injective
  rw [show affinePairEquiv Q b (CommAlgCat.of F K) (scalarPoint q K t) =
      scalarPair Q K t from MulEquiv.apply_symm_apply _ _]
  apply coefficientPair_eq_of_unit_eq q K
  apply Units.ext
  have hc := congrArg (fun p : (K ⊗[F] CliffordAlgebra Q)ˣ × GL (Fin n) K =>
    (p.1 : K ⊗[F] CliffordAlgebra Q)) (affinePairEquiv_naturality Q b (CommAlgCat.ofHom φ) x)
  change ((affinePairEquiv Q b (CommAlgCat.of F K) z).val.1 : K ⊗[F] CliffordAlgebra Q) =
    tensorMap Q φ ((affinePairEquiv Q b (CommAlgCat.of F A) x).val.1 : A ⊗[F] CliffordAlgebra Q) at hc
  change ((affinePairEquiv Q b (CommAlgCat.of F K) z).val.1 : K ⊗[F] CliffordAlgebra Q) = _
  rw [hc, show affinePairEquiv Q b (CommAlgCat.of F A) x = y from MulEquiv.apply_symm_apply _ _,
    scalarPair_val]
  change tensorMap Q φ (toBaseChange A Q (CliffordAlgebra.ι Qₐ v * CliffordAlgebra.ι Qₐ w)) =
    algebraMap K (K ⊗[F] CliffordAlgebra Q) (t.val : K)
  rw [map_mul, map_mul, tensorMap_cliffordVector, tensorMap_cliffordVector, ← map_mul]
  have hve : vectorMap φ v = e + f := by
    change vectorMap φ (eₐ + fₐ) = _
    rw [map_add, vectorMap_evaluateLaurent, vectorMap_evaluateLaurent]
  have ht : (t.val : Kˣ) ^ 2 = 1 := (mem_rootsOfUnity 2 _).mp t.property
  have hinv : t.val⁻¹ = t.val := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using ht)
  have hwe : vectorMap φ w = (t.val : K) • (e + f) := by
    change vectorMap φ (_ • eₐ + _ • fₐ) = _
    rw [map_add, vectorMap_smul, vectorMap_smul, vectorMap_evaluateLaurent, vectorMap_evaluateLaurent,
      smul_add]
    have hT : φ (LaurentPolynomial.T 1) = (t.val : K) := by
      change LaurentPolynomial.eval₂ (RingHom.id K) t.val (LaurentPolynomial.T 1) = _
      simp [LaurentPolynomial.eval₂_T]
    have hT' : φ (LaurentPolynomial.T (-1)) = (t.val : K) := by
      change LaurentPolynomial.eval₂ (RingHom.id K) t.val (LaurentPolynomial.T (-1)) = _
      simp [LaurentPolynomial.eval₂_T, hinv]
    rw [hT, hT']
  have hval : D (e + f) = 1 := by
    rw [QuadraticMap.map_add (⇑D), he, hf, hef, zero_add, zero_add]
  rw [hve, hwe, map_smul, mul_smul_comm, ι_sq_scalar, hval, map_one, map_smul, map_one,
    ← Algebra.algebraMap_eq_smul_one]

end Langlands.GroupScheme.CliffordSpin
