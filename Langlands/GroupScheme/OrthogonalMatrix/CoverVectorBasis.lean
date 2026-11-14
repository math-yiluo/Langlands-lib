import Langlands.GroupScheme.OrthogonalMatrix.CoverTorusTransport
import Langlands.GroupScheme.OrthogonalMatrix.TypeD
import Langlands.GroupScheme.MatrixRepresentation.NormalCharacterSpan

/-! # An inverse-right eigenbasis for the supplied orthogonal cover -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Opposite Module
open scoped CategoryTheory.MonObj Matrix
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

namespace MatrixRepresentation

variable {k : Type u} [Field k] {n : Type} [Fintype n] [DecidableEq n]

/-- The rows of one invertible matrix form a basis. -/
def basisOfRows (C : GL n k) : Basis n k (n → k) :=
  (Pi.basisFun k n).map
    (Matrix.toLinearEquivRight'OfInv (M := (C⁻¹ : GL n k).val) (M' := C.val)
      (by simpa only [Units.val_mul, Units.val_one] using
        congrArg Units.val (inv_mul_cancel C))
      (by simpa only [Units.val_mul, Units.val_one] using
        congrArg Units.val (mul_inv_cancel C)))

@[simp] theorem basisOfRows_apply (C : GL n k) (a : n) :
    basisOfRows C a = C.val.row a := by
  rw [basisOfRows, Basis.map_apply]
  change Matrix.vecMul ((Pi.basisFun k n) a) C.val = _
  rw [Pi.basisFun_apply, Matrix.single_one_vecMul]

/-- Conjugacy to a diagonal matrix makes the rows inverse-right eigenvectors,
using the same base-field basis over every coefficient algebra. -/
theorem basisOfRows_inverseRight (C : GL n k)
    (A : CommAlgCat.{u} (CommRingCat.of k)) (M : GL n A) (tau : n → Aˣ)
    (h : Matrix.GeneralLinearGroup.map (algebraMap k A) C * M *
        (Matrix.GeneralLinearGroup.map (algebraMap k A) C)⁻¹ =
      GeneralLinear.diagonalTorusUnits n A (fun a : ULift.{u} n => tau a.down))
    (a : n) :
    Matrix.vecMul (fun j => algebraMap k A (basisOfRows C a j))
        (M⁻¹ : GL n A).val =
      fun j => (((tau a)⁻¹ : Aˣ) : A) * algebraMap k A (basisOfRows C a j) := by
  let CA := Matrix.GeneralLinearGroup.map (algebraMap k A) C
  let D := GeneralLinear.diagonalTorusUnits n A (fun a : ULift.{u} n => tau a.down)
  have he : CA * M⁻¹ = D⁻¹ * CA := by
    dsimp only [D]
    rw [← h]
    dsimp only [CA]
    group
  funext j
  have hr := congrArg (fun Z : GL n A => Z.val a j) he
  have hrow : (Matrix.GeneralLinearGroup.map (algebraMap k A) C).val a =
      fun j => algebraMap k A (C.val a j) := by
    funext r
    exact Matrix.GeneralLinearGroup.map_apply _ _ _ _
  simpa only [basisOfRows_apply, Matrix.row_apply, Matrix.GeneralLinearGroup.coe_mul,
    D, SymplecticMatrix.coe_inv_diagonalTorusUnits, Matrix.diagonal_mul,
    CA, Matrix.mul_apply_eq_vecMul, hrow] using hr

end MatrixRepresentation

namespace OrthogonalMatrix

variable {k : Type u} [Field k] {l : Type} [Fintype l] [DecidableEq l] [Nontrivial l]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G}
  {pi : G ⟶ identityComponent (groupScheme l (CommRingCat.of k))}

/-- The vector representation of the identity component of the orthogonal group. -/
def identityVectorRepresentation :
    MatrixRepresentation (identityComponent (groupScheme l (CommRingCat.of k))) (l ⊕ l) :=
  identityComponentι (groupScheme l (CommRingCat.of k)) ≫ inclusion l (CommRingCat.of k)

namespace StandardTorusTransport

variable (c : StandardTorusTransport i pi)

/-- The matrix over the original field supplied by rational torus conjugation. -/
def conjugatingMatrix : GL (l ⊕ l) k :=
  (identityVectorRepresentation (l := l) (k := k)).rationalMatrix c.point

/-- On every coefficient algebra, the comparison square gives actual matrix
conjugacy to the standard diagonal torus. -/
theorem conjugatingMatrix_square (A : CommAlgCat.{u} (CommRingCat.of k))
    (t : GroupScheme.affinePoints T.toGrp A) :
    Matrix.GeneralLinearGroup.map (algebraMap k A) c.conjugatingMatrix *
        MatrixRepresentation.affineMatrix
          (pi ≫ identityComponentι (groupScheme l (CommRingCat.of k)) ≫
            inclusion l (CommRingCat.of k)) A (t ≫ i.hom.hom) *
        (Matrix.GeneralLinearGroup.map (algebraMap k A) c.conjugatingMatrix)⁻¹ =
      GeneralLinear.diagonalTorusUnits (l ⊕ l) A
        (fun a : ULift.{u} (l ⊕ l) =>
          SymplecticMatrix.torusWeights
            (GeneralLinear.torusCoords
              (t ≫ (CommGroupScheme.groupHom c.torusMap).hom.hom)) a.down) := by
  let H := identityComponent (groupScheme l (CommRingCat.of k))
  let rho := identityVectorRepresentation (l := l) (k := k)
  let s := t ≫ (CommGroupScheme.groupHom c.torusMap).hom.hom
  have ht : (t ≫ (i ≫ pi).hom.hom) ≫ (H.innerIso c.point).hom.hom.hom =
      s ≫ (identityTorus l k).hom.hom := by
    simpa only [H, s, Grp.comp_hom_hom, Category.assoc] using
      congrArg (fun f => t ≫ f.hom.hom) c.square
  rw [comp_innerIso_hom H c.point _ (t ≫ (i ≫ pi).hom.hom)] at ht
  have hm := congrArg (rho.affineMatrix A) ht
  simp only [map_mul, map_inv] at hm
  rw [show rho.affineMatrix A (H.constantPoint c.point _) =
      Matrix.GeneralLinearGroup.map (algebraMap k A) (rho.rationalMatrix c.point)
    from rho.affineMatrix_constantPoint c.point A] at hm
  have hf : identityTorus l k ≫ rho =
      diagonalTorus l (CommRingCat.of k) ≫ inclusion l (CommRingCat.of k) := by
    dsimp only [rho, identityVectorRepresentation]
    rw [← Category.assoc, identityTorus_comp]
  have hd : rho.affineMatrix A (s ≫ (identityTorus l k).hom.hom) =
      GeneralLinear.diagonalTorusUnits (l ⊕ l) A
        (fun a : ULift.{u} (l ⊕ l) =>
          SymplecticMatrix.torusWeights (GeneralLinear.torusCoords s) a.down) := by
    rw [MatrixRepresentation.affineMatrix_apply]
    have he : (s ≫ (identityTorus l k).hom.hom) ≫ rho.hom.hom =
        s ≫ (diagonalTorus l (CommRingCat.of k) ≫
          inclusion l (CommRingCat.of k)).hom.hom := by
      rw [Category.assoc, ← Grp.comp_hom_hom, hf]
    rw [he]
    exact affinePointsEquiv_diagonalTorus_inclusion s
  rw [hd] at hm
  have hrep : rho.affineMatrix A (t ≫ (i ≫ pi).hom.hom) =
      MatrixRepresentation.affineMatrix
        (pi ≫ identityComponentι (groupScheme l (CommRingCat.of k)) ≫
          inclusion l (CommRingCat.of k)) A (t ≫ i.hom.hom) := by
    change GeneralLinear.affinePointsEquiv (l ⊕ l) (CommRingCat.of k) A
        ((t ≫ (i ≫ pi).hom.hom) ≫ rho.hom.hom) =
      GeneralLinear.affinePointsEquiv (l ⊕ l) (CommRingCat.of k) A
        ((t ≫ i.hom.hom) ≫
          (pi ≫ identityComponentι (groupScheme l (CommRingCat.of k)) ≫
            inclusion l (CommRingCat.of k)).hom.hom)
    simp only [rho, identityVectorRepresentation,
      Grp.comp_hom_hom, Category.assoc]
  rw [hrep] at hm
  simpa only [rho, conjugatingMatrix, s] using hm

omit [Nontrivial l] in
/-- The negative standard vector character is the inverse diagonal entry. -/
theorem characterValue_neg_weightChar
    (A : CommAlgCat.{u} (CommRingCat.of k))
    (s : GroupScheme.affinePoints
      (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift l)).toGrp A)
    (a : l ⊕ l) :
    Lie.characterValue (-weightChar l k a) s =
      (SymplecticMatrix.torusWeights (GeneralLinear.torusCoords s) a)⁻¹ := by
  rw [SymplecticMatrix.characterValue_eq_prod, map_neg, characterCoordEquiv_weightChar]
  simp only [Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib]
  rw [← SymplecticMatrix.torusWeights_eq_prod]

/-- One basis over the original field diagonalizes the inverse-right row action
of the supplied torus over every commutative coefficient algebra. -/
theorem exists_inverseRight_eigenbasis :
    ∃ b : Basis (l ⊕ l) k ((l ⊕ l) → k),
      ∀ (A : CommAlgCat.{u} (CommRingCat.of k))
        (t : GroupScheme.affinePoints T.toGrp A) (a : l ⊕ l),
        Matrix.vecMul (fun j => algebraMap k A (b a j))
            ((MatrixRepresentation.affineMatrix
              (pi ≫ identityComponentι (groupScheme l (CommRingCat.of k)) ≫
                inclusion l (CommRingCat.of k)) A (t ≫ i.hom.hom))⁻¹ :
                GL (l ⊕ l) A).val =
          fun j => (Lie.characterValue (c.torusMap ≫ (-weightChar l k a)) t : A) *
            algebraMap k A (b a j) := by
  refine ⟨MatrixRepresentation.basisOfRows c.conjugatingMatrix, ?_⟩
  intro A t a
  rw [Lie.characterValue_comp, characterValue_neg_weightChar]
  exact MatrixRepresentation.basisOfRows_inverseRight c.conjugatingMatrix A _
    (SymplecticMatrix.torusWeights (GeneralLinear.torusCoords
      (t ≫ (CommGroupScheme.groupHom c.torusMap).hom.hom)))
    (c.conjugatingMatrix_square A t) a

end StandardTorusTransport
end OrthogonalMatrix
end Langlands.GroupScheme
