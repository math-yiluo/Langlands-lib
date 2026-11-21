import Langlands.Representation.Archimedean.RealCartanArgumentJacobian
import Langlands.Representation.Archimedean.RealCartanOffBlockDeterminant
import Langlands.Representation.Archimedean.RealLeviBlockDecomposition
import Mathlib.LinearAlgebra.Matrix.Block

/-! # The rectangular factors of the transverse real Cartan determinant -/

noncomputable section

open Matrix
open scoped Matrix.Norms.Operator

namespace Langlands.Archimedean.RealCartanTransverseDeterminant

open RealLeviChart RealCartanArgumentJacobian
  RealLeviCartanDifferential RealCartanOffBlockDeterminant

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {c : ℕ} (sz : Fin c → ℕ)
local notation "N" => ∑ i, sz i
local notation "Mat" => Matrix (Fin N) (Fin N) ℝ
local notation "K" => Matrix.unitaryGroup (Fin N) ℝ
local notation "X" => (Coord sz → ℝ)

/-- The lower off-diagonal rectangles of a block partition. -/
abbrev OffPair (c : ℕ) := {ij : Fin c × Fin c // ij.2 < ij.1}

private def coordPair (z : Coord sz) : OffPair c :=
  ⟨(cls sz z.1.1, cls sz z.1.2), z.2⟩

private abbrev Rect (b : OffPair c) := Matrix (Fin (sz b.1.1)) (Fin (sz b.1.2)) ℝ

private def rectCoord (b : OffPair c) (i : Fin (sz b.1.1)) (j : Fin (sz b.1.2)) : Coord sz :=
  ⟨(pos sz b.1.1 i, pos sz b.1.2 j), by simpa only [cls_pos] using b.2⟩

private theorem coordPair_rectCoord (b : OffPair c) (i : Fin (sz b.1.1)) (j : Fin (sz b.1.2)) :
    coordPair sz (rectCoord sz b i j) = b := by
  apply Subtype.ext
  simp [coordPair, rectCoord, cls_pos]

private def rectFiberEquiv (b : OffPair c) :
    (Fin (sz b.1.1) × Fin (sz b.1.2)) ≃ {z : Coord sz // coordPair sz z = b} :=
  Equiv.ofBijective (fun ij => ⟨rectCoord sz b ij.1 ij.2, coordPair_rectCoord sz b ij.1 ij.2⟩) (by
    constructor
    · intro u v h
      have h' := congrArg (fun p : {z : Coord sz // coordPair sz z = b} => p.1.1) h
      have hi := finSigmaFinEquiv.injective (congrArg Prod.fst h')
      have hj := finSigmaFinEquiv.injective (congrArg Prod.snd h')
      exact Prod.ext (eq_of_heq (Sigma.mk.inj_iff.mp hi).2) (eq_of_heq (Sigma.mk.inj_iff.mp hj).2)
    · rintro ⟨q, hq⟩
      have hi := congrArg (fun z : OffPair c => z.1.1) hq
      have hj := congrArg (fun z : OffPair c => z.1.2) hq
      have he₁ : ∃ u : Fin (sz b.1.1), pos sz b.1.1 u = q.1.1 := by
        have hp := pos_cls sz q.1.1
        change cls sz q.1.1 = b.1.1 at hi
        rwa [hi] at hp
      have he₂ : ∃ v : Fin (sz b.1.2), pos sz b.1.2 v = q.1.2 := by
        have hp := pos_cls sz q.1.2
        change cls sz q.1.2 = b.1.2 at hj
        rwa [hj] at hp
      obtain ⟨u, hu⟩ := he₁
      obtain ⟨v, hv⟩ := he₂
      exact ⟨(u, v), Subtype.ext (Subtype.ext (Prod.ext hu hv))⟩)

private def rectangle (b : OffPair c) (x : X) : Rect sz b :=
  Matrix.of fun i j => x (rectCoord sz b i j)

private def matrixBlock (M : Mat) (i j : Fin c) : Matrix (Fin (sz i)) (Fin (sz j)) ℝ :=
  M.submatrix (pos sz i) (pos sz j)

private theorem matrixBlock_mul_left {B : Mat} (hB : BlockZero sz B) (A : Mat) (i j : Fin c) :
    matrixBlock sz (B * A) i j = matrixBlock sz B i i * matrixBlock sz A i j := by
  ext a b
  change (∑ p, B (pos sz i a) p * A p (pos sz j b)) =
    ∑ p, B (pos sz i a) (pos sz i p) * A (pos sz i p) (pos sz j b)
  rw [← finSigmaFinEquiv.sum_comp (fun p => B (pos sz i a) p * A p (pos sz j b)), Fintype.sum_sigma]
  refine Finset.sum_eq_single i (fun k _ hki => ?_) (by simp)
  refine Finset.sum_eq_zero fun p _ => ?_
  change B (pos sz i a) (pos sz k p) * A (pos sz k p) (pos sz j b) = 0
  rw [hB _ _ (by simpa only [cls_pos] using hki.symm), zero_mul]

private theorem matrixBlock_mul_right {B : Mat} (hB : BlockZero sz B) (A : Mat) (i j : Fin c) :
    matrixBlock sz (A * Bᵀ) i j = matrixBlock sz A i j * (matrixBlock sz B j j)ᵀ := by
  ext a b
  change (∑ p, A (pos sz i a) p * B (pos sz j b) p) =
    ∑ p, A (pos sz i a) (pos sz j p) * B (pos sz j b) (pos sz j p)
  rw [← finSigmaFinEquiv.sum_comp (fun p => A (pos sz i a) p * B (pos sz j b) p), Fintype.sum_sigma]
  refine Finset.sum_eq_single j (fun k _ hkj => ?_) (by simp)
  refine Finset.sum_eq_zero fun p _ => ?_
  change A (pos sz i a) (pos sz k p) * B (pos sz j b) (pos sz k p) = 0
  rw [hB _ _ (by simpa only [cls_pos] using hkj.symm), mul_zero]

private theorem mul_transpose_matrixBlock (B : K) (hB : BlockZero sz (B : Mat)) (i : Fin c) :
    matrixBlock sz (B : Mat) i i * (matrixBlock sz (B : Mat) i i)ᵀ = 1 := by
  exact RealLeviTorus.diagBlock_mul_transpose hB (by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.mem_unitaryGroup_iff.mp B.2) i

/-- The scaled inverse of the orthogonal block of the fixed left factor. -/
def scaledBlock (d : Fin c → ℝ) (hd : ∀ i, 0 < d i) (B : K)
    (hB : BlockZero sz (B : Mat)) (i : Fin c) : (Matrix (Fin (sz i)) (Fin (sz i)) ℝ)ˣ where
  val := d i • (matrixBlock sz (B : Mat) i i)ᵀ
  inv := (d i)⁻¹ • matrixBlock sz (B : Mat) i i
  val_inv := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ (hd i).ne', one_smul,
      mul_eq_one_comm.mp (mul_transpose_matrixBlock sz B hB i)]
  inv_val := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ (hd i).ne', one_smul,
      mul_transpose_matrixBlock sz B hB i]

/-- The rectangular endomorphism in one pair of blocks. -/
def rectangleDifference (d : Fin c → ℝ) (hd : ∀ i, 0 < d i) (B : K)
    (hB : BlockZero sz (B : Mat)) (b : OffPair c) : Module.End ℝ (Rect sz b) :=
  1 - (offBlockAction (scaledBlock sz d hd B hB b.1.1)
    (scaledBlock sz d hd B hB b.1.2)).toLinearMap

private theorem rectangle_transverseDifference (d : Fin c → ℝ) (hd : ∀ i, 0 < d i) (B : K)
    (hB : BlockZero sz (B : Mat)) (b : OffPair c) (x : X) :
    rectangle sz b (transverseDifference sz (d ∘ cls sz) B x) =
      rectangleDifference sz d hd B hB b (rectangle sz b x) := by
  let i := b.1.1
  let j := b.1.2
  let x' := radialScale sz (d ∘ cls sz) x
  have hrad : matrixBlock sz (strict x') i j = (d j / d i) • rectangle sz b x := by
    ext p q
    let z := rectCoord sz b p q
    change strict x' z.1.1 z.1.2 = (d j / d i) * x z
    rw [strict_apply_coord x' z]
    change radialScale sz (d ∘ cls sz) x z = _
    rw [radialScale_apply]
    simp only [z, rectCoord, Function.comp_apply, cls_pos, i, j]
  have hblock : rectangle sz b (adLin (B : Mat) x') =
      matrixBlock sz (B : Mat) i i * ((d j / d i) • rectangle sz b x) *
        (matrixBlock sz (B : Mat) j j)ᵀ := by
    change matrixBlock sz ((B : Mat) * strict x' * (B : Mat)ᵀ) i j = _
    rw [matrixBlock_mul_right sz hB, matrixBlock_mul_left sz hB, hrad]
  rw [transverseDifference_apply]
  change rectangle sz b x - rectangle sz b (adLin (B : Mat) x') =
    rectangle sz b x - offBlockAction (scaledBlock sz d hd B hB i)
      (scaledBlock sz d hd B hB j) (rectangle sz b x)
  rw [hblock, offBlockAction_apply]
  congr 1
  change _ = ((d i)⁻¹ • matrixBlock sz (B : Mat) i i) * rectangle sz b x *
    (d j • (matrixBlock sz (B : Mat) j j)ᵀ)
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [div_eq_mul_inv, mul_comm (d j)]

private theorem rectangle_basis (b : OffPair c) (q : Coord sz) :
    rectangle sz b (Pi.basisFun ℝ (Coord sz) q) =
      if h : coordPair sz q = b then
        stdBasis ℝ (Fin (sz b.1.1)) (Fin (sz b.1.2)) ((rectFiberEquiv sz b).symm ⟨q, h⟩) else 0 := by
  by_cases hq : coordPair sz q = b
  · rw [dite_eq_left hq]
    let qr := (rectFiberEquiv sz b).symm ⟨q, hq⟩
    have hqr : rectCoord sz b qr.1 qr.2 = q :=
      congrArg Subtype.val ((rectFiberEquiv sz b).apply_symm_apply ⟨q, hq⟩)
    rw [stdBasis_eq_single]
    ext i j
    change Pi.basisFun ℝ (Coord sz) q (rectCoord sz b i j) = single qr.1 qr.2 1 i j
    rw [Pi.basisFun_apply, Pi.single_apply, Matrix.single_apply, ← hqr]
    have h (p : Fin (sz b.1.1)) (r : Fin (sz b.1.2)) :
        rectCoord sz b i j = rectCoord sz b p r ↔ i = p ∧ j = r := by
      constructor
      · intro he
        have hh : rectFiberEquiv sz b (i, j) = rectFiberEquiv sz b (p, r) := Subtype.ext he
        exact Prod.mk.inj ((rectFiberEquiv sz b).injective hh)
      · rintro ⟨rfl, rfl⟩
        rfl
    simp [h, eq_comm]
  · rw [dite_eq_right hq]
    ext i j
    change Pi.basisFun ℝ (Coord sz) q (rectCoord sz b i j) = 0
    rw [Pi.basisFun_apply, Pi.single_apply]
    have he : rectCoord sz b i j ≠ q := fun he => hq ((congrArg (coordPair sz) he).symm.trans
      (coordPair_rectCoord sz b i j))
    rw [ite_eq_right he]

private theorem det_operator_from_rectangles (T : Module.End ℝ X)
    (D : ∀ b : OffPair c, Module.End ℝ (Rect sz b))
    (hT : ∀ b x, rectangle sz b (T x) = D b (rectangle sz b x)) :
    T.det = ∏ b : OffPair c, (D b).det := by
  classical
  let e := Fintype.equivFin (OffPair c)
  let lbl (q : Coord sz) := e (coordPair sz q)
  let b := Pi.basisFun ℝ (Coord sz)
  let A := LinearMap.toMatrix b b T
  have hentry (p q : Coord sz) : A p q = T (b q) p := by
    simp only [A, b, LinearMap.toMatrix_apply, Pi.basisFun_repr]
  have hA : A.BlockTriangular lbl := by
    intro p q hpq
    have hp : ∀ b' : OffPair c, coordPair sz p = b' →
        ∃ u v, rectCoord sz b' u v = p := by
      intro b' hp
      obtain ⟨⟨u, v⟩, huv⟩ := (rectFiberEquiv sz b').surjective ⟨p, hp⟩
      exact ⟨u, v, congrArg Subtype.val huv⟩
    obtain ⟨u, v, huv⟩ := hp (coordPair sz p) rfl
    have hn : coordPair sz q ≠ coordPair sz p := fun h => hpq.ne ((congrArg e h))
    have hz := congrArg (fun M : Rect sz (coordPair sz p) => M u v) (hT (coordPair sz p) (b q))
    rw [rectangle_basis, dite_eq_right hn, map_zero, Matrix.zero_apply] at hz
    rw [hentry, ← huv]
    exact hz
  rw [← LinearMap.det_toMatrix b, hA.det_fintype, ← e.prod_comp]
  apply Finset.prod_congr rfl
  intro i _
  let ei : {p : Coord sz // coordPair sz p = i} ≃ {p : Coord sz // lbl p = e i} :=
    Equiv.subtypeEquivRight fun p => e.injective.eq_iff.symm
  let r := (rectFiberEquiv sz i).trans ei
  let b' := stdBasis ℝ (Fin (sz i.1.1)) (Fin (sz i.1.2))
  rw [← LinearMap.det_toMatrix b', ← Matrix.det_submatrix_equiv_self r]
  congr 1
  ext ⟨u, v⟩ ⟨p, q⟩
  have he := congrArg (fun M : Rect sz i => M u v) (hT i (b (rectCoord sz i p q)))
  rw [rectangle_basis, dite_eq_left (coordPair_rectCoord sz i p q)] at he
  have hi : (rectFiberEquiv sz i).symm ⟨rectCoord sz i p q, coordPair_rectCoord sz i p q⟩ = (p, q) :=
    (rectFiberEquiv sz i).symm_apply_apply (p, q)
  rw [hi] at he
  change A (rectCoord sz i u v) (rectCoord sz i p q) =
    LinearMap.toMatrix b' b' (D i) (u, v) (p, q)
  rw [hentry, LinearMap.toMatrix_apply]
  have hrepr (M : Rect sz i) : b'.repr M (u, v) = M u v := by
    simp [b', stdBasis, Pi.basis_repr]
  rw [hrepr]
  exact he

/-- The absolute transverse derivative determinant is the product of the
absolute determinants of the rectangular differences. -/
def RealCartanTransverseDeterminantStatement : Prop :=
  ∀ (c : ℕ) (sz : Fin c → ℕ) (d : Fin c → ℝ) (hd : ∀ i, 0 < d i)
    (B : Matrix.unitaryGroup (Fin (∑ i, sz i)) ℝ)
    (hB : BlockZero sz (B : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ)),
    |(transverseDifference sz (d ∘ cls sz) B).det| =
      ∏ b : OffPair c, |(rectangleDifference sz d hd B hB b).det|

theorem realCartanTransverseDeterminant : RealCartanTransverseDeterminantStatement := by
  intro c sz d hd B hB
  have he := det_operator_from_rectangles sz (transverseDifference sz (d ∘ cls sz) B).toLinearMap
    (rectangleDifference sz d hd B hB) (rectangle_transverseDifference sz d hd B hB)
  change |LinearMap.det (transverseDifference sz (d ∘ cls sz) B).toLinearMap| = _
  rw [he, Finset.abs_prod]

end Langlands.Archimedean.RealCartanTransverseDeterminant
