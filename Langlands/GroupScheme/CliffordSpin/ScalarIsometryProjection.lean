import Langlands.Group.GL.Maps
import Langlands.GroupScheme.CliffordSpin.AffineModel
import Langlands.GroupScheme.Rational.NumberFieldSpecialOrthogonalHasse
import Langlands.GroupScheme.SplitComponent.AffineTargetBridge

/-! # Projection of the Clifford lift scheme to the actual scalar isometry group -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Matrix
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.CliffordSpin

open Quaternionic Langlands.QuadraticForm Langlands.LinearAlgebra.OrthogonalCocycleDescent

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 750000
set_option synthInstance.maxHeartbeats 100000

variable {F : Type u} [Field F] [CharZero F] [Invertible (2 : F)] {n : ℕ} [NeZero n]
  (q : (FirstKindInvolution.scalar F).QuadraticForms (Fin n))

local notation "S" => CommRingCat.of F
local notation "τ" => FirstKindInvolution.scalar F
local notation "O" => FirstKindInvolution.isometryGroup τ q
local notation "SO" => FirstKindInvolution.normOneIsometryGroup τ q
local notation "ιSO" => FirstKindInvolution.normOneIsometryGroupι τ q
local notation "B" => FirstKindInvolution.polar τ q
local notation "Q" => Matrix.toQuadraticForm' (FirstKindInvolution.polar τ q)
local notation "b" => Pi.basisFun F (Fin n)
local notation "P" => groupScheme Q b

private abbrev linearMatrixAction (A : CommAlgCat.{u} S) := matrixAction b A

omit [CharZero F] [NeZero n] in
private theorem equivFun_eq_gramBaseChange (A : CommAlgCat.{u} S) :
    ((b).baseChange A).equivFun = (gramBaseChangeIsometry (A := A) B).toLinearEquiv := by
  apply LinearEquiv.toLinearMap_injective
  apply ((b).baseChange A).ext
  intro i
  ext j
  change (((b).baseChange A).repr (((b).baseChange A) i) j) =
    (TensorProduct.piScalarRight F A A (Fin n) ((b).baseChange A i)) j
  rw [Module.Basis.baseChange_apply, TensorProduct.piScalarRight_apply,
    TensorProduct.piScalarRightHom_tmul]
  simp [Module.Basis.baseChange_repr_tmul, Pi.basisFun_apply, Pi.single_apply, Algebra.smul_def]

omit [CharZero F] [NeZero n] in
private theorem matrixAction_via_gramBaseChange (A : CommAlgCat.{u} S) (g : GL (Fin n) A) :
    let e := (gramBaseChangeIsometry (A := A) B).toLinearEquiv
    linearMatrixAction A g = e.trans ((Matrix.GeneralLinearGroup.toLin g).toLinearEquiv.trans e.symm) := by
  intro e
  change (LinearMap.GeneralLinearGroup.congrLinearEquiv ((b).baseChange A).equivFun.symm
    (Matrix.GeneralLinearGroup.toLin g)).toLinearEquiv = _
  rw [LinearMap.GeneralLinearGroup.congrLinearEquiv_apply]
  change ((b).baseChange A).equivFun.symm.symm.trans
    ((Matrix.GeneralLinearGroup.toLin g).toLinearEquiv.trans ((b).baseChange A).equivFun.symm) = _
  rw [LinearEquiv.symm_symm, equivFun_eq_gramBaseChange q A]

omit [CharZero F] [NeZero n] in
/-- In the standard basis the Clifford vector action preserves the form exactly when the
matrix preserves the coordinate Gram form. -/
theorem matrixAction_preserves_iff (A : CommAlgCat.{u} S) (g : GL (Fin n) A) :
    (∀ v : A ⊗[F] (Fin n → F), ((Q).baseChange A) (linearMatrixAction A g v) = ((Q).baseChange A) v) ↔
      (g : Matrix (Fin n) (Fin n) A)ᵀ * ((B).map (algebraMap F A)) *
        (g : Matrix (Fin n) (Fin n) A) = (B).map (algebraMap F A) := by
  let Bₐ := (B).map (algebraMap F A)
  let qₐ := Bₐ.toQuadraticForm'
  let e := gramBaseChangeIsometry (A := A) B
  let G := (Matrix.GeneralLinearGroup.toLin g).toLinearEquiv
  let : Invertible (2 : A) := (Invertible.map (algebraMap F A) 2).copy 2 (map_ofNat _ _).symm
  have hs : Bₐᵀ = Bₐ := by
    dsimp only [Bₐ]
    rw [← Matrix.transpose_map, OrthogonalMatrix.scalar_polar_transpose]
  have hG : LinearMap.toMatrix' G.toLinearMap = (g : Matrix (Fin n) (Fin n) A) :=
    LinearMap.toMatrix'_toLin' _
  have hG' : ((Q).baseChange A).comp (linearMatrixAction A g).toLinearMap = (Q).baseChange A ↔
      qₐ.comp G.toLinearMap = qₐ := by
    have h (v : A ⊗[F] (Fin n → F)) :
        e (linearMatrixAction A g v) = G (e v) := by
      rw [matrixAction_via_gramBaseChange q A g]
      exact e.toLinearEquiv.apply_symm_apply _
    constructor
    · intro hsame
      apply QuadraticMap.ext
      intro y
      obtain ⟨v, rfl⟩ := e.toLinearEquiv.surjective y
      change qₐ (G (e v)) = qₐ (e v)
      rw [← h v, e.map_app, e.map_app]
      exact DFunLike.congr_fun hsame v
    · intro hsame
      apply QuadraticMap.ext
      intro v
      change ((Q).baseChange A) (linearMatrixAction A g v) = ((Q).baseChange A) v
      rw [← e.map_app (linearMatrixAction A g v), h v, ← e.map_app v]
      exact DFunLike.congr_fun hsame (e v)
  have hcomp : (∀ v : A ⊗[F] (Fin n → F),
      ((Q).baseChange A) (linearMatrixAction A g v) = ((Q).baseChange A) v) ↔
      ((Q).baseChange A).comp (linearMatrixAction A g).toLinearMap = (Q).baseChange A := by
    exact ⟨fun h => QuadraticMap.ext (fun v => h v), fun h v => DFunLike.congr_fun h v⟩
  rw [hcomp, hG']
  constructor
  · intro h
    have h' := congrArg QuadraticForm.toMatrix' h
    rw [QuadraticForm.toMatrix'_comp, hG, toMatrix_toQuadraticForm_of_symm hs] at h'
    exact h'
  · intro h
    apply quadratic_toMatrix_injective
    rw [QuadraticForm.toMatrix'_comp, hG, toMatrix_toQuadraticForm_of_symm hs]
    exact h

/-- Matrix of a norm-one isometry, with column-vector action. -/
def actionMatrix (A : CommAlgCat.{u} S) : (SO).affinePoints A →* GL (Fin n) A :=
  (Langlands.GeneralLinear.inverseTranspose n A).toMonoidHom.comp
    ((OrthogonalMatrix.scalarMatrixPoint q A).comp ((SO).affinePointsTarget ιSO A))

omit [CharZero F] [Invertible (2 : F)] [NeZero n] in
private theorem map_inverseTranspose {A A' : CommAlgCat.{u} S} (f : A ⟶ A') (g : GL (Fin n) A) :
    Matrix.GeneralLinearGroup.map f.hom.toRingHom (Langlands.GeneralLinear.inverseTranspose n A g) =
      Langlands.GeneralLinear.inverseTranspose n A' (Matrix.GeneralLinearGroup.map f.hom.toRingHom g) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [Matrix.GeneralLinearGroup.map_apply, Langlands.GeneralLinear.inverseTranspose_entry, ← map_inv]

omit [CharZero F] [Invertible (2 : F)] in
/-- The column-vector matrix commutes with all maps of coefficient algebras. -/
theorem actionMatrix_naturality {A A' : CommAlgCat.{u} S} (f : A ⟶ A') (x : (SO).affinePoints A) :
    actionMatrix q A' ((SO).affinePointMap f x) = Matrix.GeneralLinearGroup.map f.hom.toRingHom
      (actionMatrix q A x) := by
  change Langlands.GeneralLinear.inverseTranspose n A'
    (OrthogonalMatrix.scalarMatrixPoint q A' (((algSpec S).map f.op ≫ x) ≫ (ιSO).hom.hom)) = _
  rw [Category.assoc]
  change Langlands.GeneralLinear.inverseTranspose n A'
    (OrthogonalMatrix.scalarMatrixPoint q A' ((O).affinePointMap f (x ≫ (ιSO).hom.hom))) = _
  rw [OrthogonalMatrix.scalarMatrixPoint_naturality, ← map_inverseTranspose]
  rfl

omit [CharZero F] [Invertible (2 : F)] in
/-- The column-vector matrix determines the actual norm-one isometry point. -/
theorem actionMatrix_injective (A : CommAlgCat.{u} S) : Function.Injective (actionMatrix q A) := by
  intro x y h
  let : Mono (ιSO).hom.hom := kernelι_mono _
  apply (cancel_mono (ιSO).hom.hom).mp
  apply OrthogonalMatrix.scalarMatrixPoint_injective q A
  exact (Langlands.GeneralLinear.inverseTranspose n A).injective h

omit [CharZero F] [Invertible (2 : F)] [NeZero n] in
private theorem gramTransform_inverseTranspose_iff (A : CommAlgCat.{u} S)
    (g : GL (Fin n) A) (D : Matrix (Fin n) (Fin n) A) :
    gramTransform (Langlands.GeneralLinear.inverseTranspose n A g) D = D ↔
      (g : Matrix (Fin n) (Fin n) A)ᵀ * D * (g : Matrix (Fin n) (Fin n) A) = D := by
  let m := (g : Matrix (Fin n) (Fin n) A)
  let k := ((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)
  have hmk : m * k = 1 := Units.mul_inv g
  have hkm : k * m = 1 := Units.inv_mul g
  have hmk' : kᵀ * mᵀ = 1 := by rw [← transpose_mul, hmk, transpose_one]
  have hkm' : mᵀ * kᵀ = 1 := by rw [← transpose_mul, hkm, transpose_one]
  change kᵀ * D * kᵀᵀ = D ↔ mᵀ * D * m = D
  rw [transpose_transpose]
  constructor
  · intro h
    calc
      mᵀ * D * m = mᵀ * (kᵀ * D * k) * m := congrArg (fun A => mᵀ * A * m) h.symm
      _ = D := by
        rw [← mul_assoc _ _ k, ← mul_assoc mᵀ kᵀ, hkm', one_mul, mul_assoc, hkm, mul_one]
  · intro h
    calc
      kᵀ * D * k = kᵀ * (mᵀ * D * m) * k := by rw [h]
      _ = D := by
        rw [← mul_assoc _ _ m, ← mul_assoc kᵀ mᵀ, hmk', one_mul, mul_assoc, hmk, mul_one]

omit [CharZero F] [Invertible (2 : F)] [NeZero n] in
private theorem det_inverseTranspose (A : CommAlgCat.{u} S) (g : GL (Fin n) A) :
    Matrix.GeneralLinearGroup.det (Langlands.GeneralLinear.inverseTranspose n A g) =
      (Matrix.GeneralLinearGroup.det g)⁻¹ := by
  rw [← map_inv]
  apply Units.ext
  change ((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)ᵀ.det = _
  exact Matrix.det_transpose _

/-- The exact image of the norm-one isometry group in column-vector coordinates. -/
theorem mem_range_actionMatrix_iff (A : CommAlgCat.{u} S) (g : GL (Fin n) A) :
    g ∈ (actionMatrix q A).range ↔
      (∀ v : A ⊗[F] (Fin n → F), ((Q).baseChange A) (linearMatrixAction A g v) = ((Q).baseChange A) v) ∧
        Matrix.GeneralLinearGroup.det g = 1 := by
  let t := Langlands.GeneralLinear.inverseTranspose n A
  let D := (B).map (algebraMap F A)
  have hsub (x : (O).affinePoints A) :
      (∃ y : (SO).affinePoints A, y ≫ (ιSO).hom.hom = x) ↔
        Matrix.GeneralLinearGroup.det (OrthogonalMatrix.scalarMatrixPoint q A x) = 1 := by
    rw [← SubgroupFunctor.mem_range, OrthogonalMatrix.mem_range_scalarNormOne_affine_iff]
    rfl
  constructor
  · rintro ⟨s, rfl⟩
    let x := s ≫ (ιSO).hom.hom
    let u := OrthogonalMatrix.scalarMatrixPoint q A x
    have hu := OrthogonalMatrix.scalarMatrixPoint_preserves q A x
    change gramTransform u D = D at hu
    have hd := (hsub x).mp ⟨s, rfl⟩
    change Matrix.GeneralLinearGroup.det u = 1 at hd
    change (∀ v, ((Q).baseChange A) (linearMatrixAction A (t u) v) = ((Q).baseChange A) v) ∧ _
    refine ⟨(matrixAction_preserves_iff q A (t u)).mpr ?_, ?_⟩
    · apply (gramTransform_inverseTranspose_iff A (t u) D).mp
      exact (t.left_inv u).symm ▸ hu
    · change Matrix.GeneralLinearGroup.det (t u) = 1
      rw [det_inverseTranspose, hd, inv_one]
  · rintro ⟨hg, hd⟩
    obtain ⟨x, hx⟩ := OrthogonalMatrix.exists_scalarMatrixPoint_eq q A (t g)
      ((gramTransform_inverseTranspose_iff A g D).mpr ((matrixAction_preserves_iff q A g).mp hg))
    obtain ⟨s, hs⟩ := (hsub x).mpr (by rw [hx, det_inverseTranspose, hd, inv_one])
    refine ⟨s, ?_⟩
    change t (OrthogonalMatrix.scalarMatrixPoint q A (s ≫ (ιSO).hom.hom)) = g
    rw [hs, hx]
    exact t.left_inv g

local instance isAffine_scalarNormOne : IsAffine (SO).X.left := by
  let p := FirstKindInvolution.normOneIsometryAmbientι τ q
  let : IsClosedImmersion p.hom.hom.left := FirstKindInvolution.isClosedSubgroup_normOneIsometryAmbientι τ q
  exact isAffine_of_isAffineHom p.hom.hom.left

private theorem pair_action_in_range (A : CommAlgCat.{u} S) (x : coefficientSubgroup Q b A) :
    x.val.2 ∈ (actionMatrix q A).range := by
  let y : CliffordSpinLift ((Q).baseChange A) := ⟨pairEquiv Q b A x.val, x.property⟩
  let : Invertible (2 : A) := (Invertible.map (algebraMap F A) 2).copy 2 (map_ofNat _ _).symm
  exact (mem_range_actionMatrix_iff q A _).mpr ⟨CliffordSpinLift.vectorAction_preserves _ y,
    (mem_coefficientSubgroup_iff Q b x.val.1 x.val.2).mp x.property |>.2.2.1⟩

private def actionRangeEquiv (A : CommAlgCat.{u} S) :
    (SO).affinePoints A ≃* (actionMatrix q A).range :=
  MulEquiv.ofBijective (actionMatrix q A).rangeRestrict
    ⟨fun _ _ h => actionMatrix_injective q A (congrArg Subtype.val h),
      (actionMatrix q A).rangeRestrict_surjective⟩

private def onPairs (A : CommAlgCat.{u} S) : coefficientSubgroup Q b A →* (SO).affinePoints A :=
  (actionRangeEquiv q A).symm.toMonoidHom.comp
    (((MonoidHom.snd _ _).comp (coefficientSubgroup Q b A).subtype).codRestrict
      _ (pair_action_in_range q A))

private theorem actionMatrix_onPairs (A : CommAlgCat.{u} S) (x : coefficientSubgroup Q b A) :
    actionMatrix q A (onPairs q A x) = x.val.2 := by
  exact congrArg Subtype.val ((actionRangeEquiv q A).apply_symm_apply
    ⟨x.val.2, pair_action_in_range q A x⟩)

private def projectionNat : Corepresented.cutFunctor (isCutOutBy Q b) ⟶ (SO).affinePointFunctor where
  app A := GrpCat.ofHom (onPairs q A)
  naturality A A' f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply actionMatrix_injective q A'
    change actionMatrix q A' (onPairs q A' ((Corepresented.cutFunctor (isCutOutBy Q b)).map f x)) =
      actionMatrix q A' ((SO).affinePointMap f (onPairs q A x))
    rw [actionMatrix_onPairs, actionMatrix_naturality, actionMatrix_onPairs]
    rfl

/-- The affine Clifford group projects to the actual scalar norm-one isometry group. -/
def projection : P ⟶ SO :=
  SplitComponent.homOfNat SO (Corepresented.cutCorepresentableBy (isCutOutBy Q b)) (projectionNat q)

/-- Its coefficient matrix is exactly the Clifford vector action. -/
theorem actionMatrix_projection (A : CommAlgCat.{u} S) (x : (P).affinePoints A) :
    actionMatrix q A (x ≫ (projection q).hom.hom) = (affinePairEquiv Q b A x).val.2 := by
  rw [projection, SplitComponent.homOfNat_affinePoints]
  exact actionMatrix_onPairs q A (affinePairEquiv Q b A x)

end Langlands.GroupScheme.CliffordSpin
