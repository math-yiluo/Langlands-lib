import Langlands.GroupScheme.Rational.NumberFieldScalarEvenSpinHasse
import Langlands.GroupScheme.KernelSquareTransport
import Langlands.GroupScheme.Quaternionic.LineRotationSplit
import Langlands.GroupScheme.Quaternionic.NormOneSplitAffine
import Langlands.LinearAlgebra.CliffordPlaneInvolution
import Langlands.GroupScheme.CliffordSpin.ScalarIsometryProjection
import Langlands.GroupScheme.CliffordSpin.GeometricPoints
import Langlands.GroupScheme.Absolute.CocharacterDescentGroup

/-! # Lifts of the reflection of a quaternionic line to a spin cover -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite Matrix
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The affine base-change comparison commutes with homomorphisms of group schemes. -/
theorem Lie.affineBaseChangeEquiv_comp {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G H : GroupScheme (Spec (CommRingCat.of k))} (f : G ⟶ H) (A : Type u) [CommRing A]
    [Algebra k A] [Algebra K A] [IsScalarTower k K A]
    (x : Lie.AffinePoints ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) A) :
    Lie.affineBaseChangeEquiv k K H A
        (x ≫ ((GroupScheme.baseChange (algebraBaseMap k K)).map f).hom.hom) =
      Lie.affineBaseChangeEquiv k K G A x ≫ f.hom.hom := by
  change (Lie.affineBaseTestIso k K A).inv ≫ GroupScheme.baseChangePointsEquiv
      (algebraBaseMap k K) H _ (x ≫ (Over.pullback (algebraBaseMap k K)).map f.hom.hom) =
    ((Lie.affineBaseTestIso k K A).inv ≫ GroupScheme.baseChangePointsEquiv
      (algebraBaseMap k K) G _ x) ≫ f.hom.hom
  rw [GaloisCocharacterDescent.baseChangePointsEquiv_morphism k K H G f.hom.hom _ x,
    Category.assoc]

namespace CliffordSpin

variable {K V : Type u} [Field K] [AddCommGroup V] [Module K V] [Invertible (2 : K)] {N : ℕ}
  (b : Module.Basis (Fin N) K V) (A : Type u) [Field A] [Algebra K A]

omit [Invertible (2 : K)] in
/-- The matrix action is the linear map of the matrix in the base-changed basis. -/
theorem toLinearMap_matrixAction (g : GL (Fin N) A) :
    ((matrixAction b A g : (A ⊗[K] V) ≃ₗ[A] (A ⊗[K] V)) : (A ⊗[K] V) →ₗ[A] (A ⊗[K] V)) =
      Matrix.toLin (b.baseChange A) (b.baseChange A) (g : Matrix (Fin N) (Fin N) A) := by
  apply LinearMap.ext
  intro v
  change (Matrix.GeneralLinearGroup.toLin' (b.baseChange A) g).toLinearEquiv v = _
  rw [Matrix.GeneralLinearGroup.toLin'_apply, Matrix.toLin_apply,
    Fintype.linearCombination_apply]

omit [Invertible (2 : K)] in
theorem finrank_range_matrixAction_sub_id (g : GL (Fin N) A) :
    Module.finrank A (LinearMap.range
      ((matrixAction b A g : (A ⊗[K] V) ≃ₗ[A] (A ⊗[K] V)).toLinearMap - LinearMap.id)) =
      ((g : Matrix (Fin N) (Fin N) A) - 1).rank := by
  rw [Matrix.rank_eq_finrank_range_toLin _ (b.baseChange A) (b.baseChange A), _root_.map_sub,
    Matrix.toLin_one, ← toLinearMap_matrixAction]

end CliffordSpin

open Quaternionic Quaternionic.FirstKindInvolution MoritaIsometry FiniteAlgebraUnits.MatrixPoints

/-- For a nondegenerate quaternionic form of rank at least three in characteristic zero, a lift
to the simply connected central cover of the negation of a nondegenerate line has square
different from the identity over an algebraically closed coefficient field. -/
theorem lineReflection_lift_mul_self_ne_one
    {F : Type u} [Field F] [CharZero F]
    {D : Type u} [DivisionRing D] [Algebra F D] [Algebra.IsCentral F D] [FiniteDimensional F D]
    (hD : Module.finrank F D = 4) (σ : FirstKindInvolution F D)
    (hσ : Module.finrank F σ.symmetricSubspace = 3) {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    (q : σ.QuadraticForms (Fin n)) (hq : σ.IsNondegenerateQuadratic q)
    {G : GroupScheme (Spec (CommRingCat.of F))} {p : G ⟶ σ.normOneIsometryGroup q}
    (hG : IsSimplyConnected G) (hp : IsCentralIsogeny p)
    (x : Fin n → D) (hx : σ.sesqForm (σ.polar q) x x ≠ 0)
    (Ω : Type u) [Field Ω] [Algebra F Ω] [IsAlgClosed Ω]
    (y : G.affinePoints (CommAlgCat.of F Ω))
    (hy : ((σ.normOneIsometryAffinePointsEquiv q (CommAlgCat.of F Ω)
        (G.affinePointsTarget p (CommAlgCat.of F Ω) y)).val.val :
          Ω ⊗[F] Matrix (Fin n) (Fin n) D) = (1 : Ω) ⊗ₜ[F] σ.lineReflection q x) :
    y * y ≠ 1 := by
  classical
  intro hyy
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  obtain ⟨e₀⟩ := CentralSimple.exists_matrix_chart_reducedDegree F D Ω
  let e : Ω ⊗[F] D ≃ₐ[Ω] Matrix (Fin 2) (Fin 2) Ω :=
    e₀.trans (Matrix.reindexAlgEquiv Ω Ω (finCongr (FirstKindInvolution.reducedDegree_eq_two hD)))
  let b := algebraBaseMap F Ω
  let B := GroupScheme.baseChange b
  let Q := NormOneSplit.gramQ e σ q
  have hQ : (scalar Ω).IsNondegenerateQuadratic Q :=
    MoritaIsometry.isNondegenerateQuadratic_gramN e σ n hσ q _ (Quotient.out_eq q) hq
  let s := NormOneSplit.splitIso e σ q hσ
  let r := B.map p ≫ s.hom
  have hr : IsCentralIsogeny r := (hp.baseChange b).comp_iso s
  have hGΩ : IsSimplyConnected (B.obj G) := isSimplyConnectedFieldExtension F Ω G hG
  let : Invertible (2 : Ω) := invertibleOfNonzero two_ne_zero
  let : NeZero (2 * n) := ⟨by omega⟩
  obtain ⟨hsm, habs⟩ := ordinaryOrthogonalGeometry Ω n hn Q hQ
  let e₁ := scalarConnectedIsometryIso_normOne Q hQ habs.1.isSemisimple
  have hSO : IsSemisimple ((scalar Ω).normOneIsometryGroup Q) :=
    IsSemisimple.of_iso e₁.symm habs.1.isSemisimple
  let p' := r ≫ e₁.inv
  have hp' : IsCentralIsogeny p' := hr.comp_iso e₁.symm
  let k₀ : kernel p' ≅ kernel r := kernelSquareIso p' r (Iso.refl _) e₁ (by simp [p'])
  have hker : Nat.card (affinePoints (kernel r) (CommAlgCat.of Ω (AlgebraicClosure Ω))) = 2 :=
    (Nat.card_congr ((Grp.forget _).mapIso k₀).homToEquiv).symm.trans
      (natCard_scalarEvenSpinKernel Q hn hQ p' hGΩ hp')
  obtain ⟨c, hc⟩ := CliffordSpin.exists_iso_of_simplyConnected_scalarCover
    (K := AlgebraicClosure Ω) Q hQ (by omega) hSO r hGΩ hr hker
  -- The split matrix of the image of `y`.
  set y'' := (Lie.affineBaseChangeEquiv F Ω G Ω).symm y with hy''
  have hpt : y'' ≫ (B.map p).hom.hom = (Lie.affineBaseChangeEquiv F Ω (σ.normOneIsometryGroup q) Ω).symm
      (G.affinePointsTarget p (CommAlgCat.of F Ω) y) := by
    apply (Lie.affineBaseChangeEquiv F Ω (σ.normOneIsometryGroup q) Ω).injective
    rw [MulEquiv.apply_symm_apply, Lie.affineBaseChangeEquiv_comp, hy'', MulEquiv.apply_symm_apply]
    rfl
  set γm := chartN e n Ω ((1 : Ω) ⊗ₜ[F] σ.lineReflection q x) with hγm
  have hγ : (OrthogonalMatrix.scalarMatrixPoint Q (CommAlgCat.of Ω Ω : CommAlgCat (CommRingCat.of Ω))
      ((y'' ≫ r.hom.hom) ≫ ((scalar Ω).normOneIsometryGroupι Q).hom.hom) :
        Matrix (Fin (2 * n)) (Fin (2 * n)) Ω) = γm := by
    have h : y'' ≫ r.hom.hom = (y'' ≫ (B.map p).hom.hom) ≫ s.hom.hom.hom := by
      simp only [r, Grp.comp_hom_hom, Category.assoc]
    rw [h, hpt]
    exact scalarMatrixPoint_splitIso e σ q hσ _ _ hy
  have h1t : (1 : Ω) ⊗ₜ[F] σ.lineReflection q x =
      (coefficientEquiv F D Ω).symm (σ.lineRotationMatrix q x Ω (-1)) := by
    rw [← map_lineReflection, ← coefficientEquiv_one_tmul_eq_map, AlgEquiv.symm_apply_apply]
  have hγ1 : γm * γm = 1 := by
    rw [hγm, h1t, ← _root_.map_mul (chartN e n Ω), ← _root_.map_mul,
      lineRotationMatrix_mul σ q x Ω hx, neg_mul_neg, one_mul, lineRotationMatrix_one,
      _root_.map_one, _root_.map_one]
  have hγne : γm ≠ 1 := by
    intro h
    rw [hγm, h1t] at h
    apply σ.lineRotationMatrix_neg_one_ne_one q x (K := Ω) hx
    apply (coefficientEquiv (m := Fin n) F D Ω).symm.injective
    apply (chartN e n Ω).injective
    rw [h, _root_.map_one, _root_.map_one]
  have hγr : (γm - 1).rank ≤ 2 := by
    rw [hγm, h1t]
    exact rank_chartN_lineRotationMatrix_sub_one e σ q x (-1)
  -- The Clifford lift of the image of `y`.
  let A : CommAlgCat (CommRingCat.of Ω) := CommAlgCat.of Ω Ω
  let Qq := Matrix.toQuadraticForm' (FirstKindInvolution.polar (scalar Ω) Q)
  let bb := Pi.basisFun Ω (Fin (2 * n))
  set xP := y'' ≫ c.hom.hom.hom with hxPdef
  have hxP : xP ≫ (CliffordSpin.projection Q).hom.hom = y'' ≫ r.hom.hom := by
    rw [← hc]
    simp only [xP, Grp.comp_hom_hom, Category.assoc]
  set gG := OrthogonalMatrix.scalarMatrixPoint Q A
    ((y'' ≫ r.hom.hom) ≫ ((scalar Ω).normOneIsometryGroupι Q).hom.hom) with hgGdef
  set pr := CliffordSpin.affinePairEquiv Qq bb A xP with hprdef
  have hpr2 : pr.val.2 = Langlands.GeneralLinear.inverseTranspose (2 * n) Ω gG := by
    rw [← CliffordSpin.actionMatrix_projection Q A xP, hxP]
    rfl
  have hgG : gG * gG = 1 := by
    apply Units.ext
    rw [Units.val_mul, Units.val_one]
    exact (congrArg₂ (· * ·) hγ hγ).trans hγ1
  have hgmat : (pr.val.2 : Matrix (Fin (2 * n)) (Fin (2 * n)) Ω) = γmᵀ := by
    rw [hpr2]
    have hinv : gG⁻¹ = gG := inv_eq_of_mul_eq_one_right hgG
    change ((gG⁻¹ : GL (Fin (2 * n)) Ω) : Matrix (Fin (2 * n)) (Fin (2 * n)) Ω)ᵀ = _
    rw [hinv, hγ]
  set sL := CliffordSpin.coefficientLiftEquiv Qq Ω pr with hsLdef
  have hℓ : QuadraticForm.CliffordSpinLift.vectorAction _ sL =
      CliffordSpin.matrixAction bb Ω pr.val.2 :=
    CliffordSpin.vectorAction_coefficientLiftEquiv Qq Ω pr
  have hgg : pr.val.2 * pr.val.2 = 1 := by
    rw [hpr2, ← _root_.map_mul, hgG, _root_.map_one]
  have hg1 : pr.val.2 ≠ 1 := by
    intro h
    apply hγne
    have h' := congrArg (fun M : GL (Fin (2 * n)) Ω => (M : Matrix (Fin (2 * n)) (Fin (2 * n)) Ω)ᵀ) h
    simp only [hgmat, Matrix.transpose_transpose, Units.val_one, Matrix.transpose_one] at h'
    exact h'
  have h2 : ∀ v, QuadraticForm.CliffordSpinLift.vectorAction _ sL
      (QuadraticForm.CliffordSpinLift.vectorAction _ sL v) = v := by
    intro v
    rw [hℓ]
    have h' := congrArg (fun f => f v) (congrArg (CliffordSpin.matrixAction bb Ω) hgg)
    simpa only [_root_.map_mul, _root_.map_one, LinearEquiv.mul_apply,
      LinearEquiv.coe_one, id] using h'
  have hne : ∃ v, QuadraticForm.CliffordSpinLift.vectorAction _ sL v ≠ v := by
    by_contra h
    push Not at h
    apply hg1
    apply (CliffordSpin.matrixAction bb Ω).injective
    rw [_root_.map_one, ← hℓ]
    ext v
    exact h v
  have hrank : Module.finrank Ω (LinearMap.range
      ((QuadraticForm.CliffordSpinLift.vectorAction _ sL : _ ≃ₗ[Ω] _).toLinearMap -
        LinearMap.id)) ≤ 2 := by
    rw [hℓ, CliffordSpin.finrank_range_matrixAction_sub_id, hgmat, ← Matrix.transpose_one,
      ← Matrix.transpose_sub, Matrix.rank_transpose]
    exact hγr
  have hsq := QuadraticForm.CliffordSpinLift.unit_mul_unit_eq_neg_one_of_involution
    (Qq.baseChange Ω) (CliffordSpin.nondegenerate_polar_baseChange Q hQ Ω) sL h2 hne hrank
  -- If `y` squared to one, so would the Clifford unit.
  have hy2 : y'' * y'' = 1 := by rw [hy'', ← _root_.map_mul, hyy, _root_.map_one]
  have hx2 : xP * xP = 1 := by
    have hxe : xP = (B.obj G).affinePointsTarget c.hom A y'' := rfl
    rw [hxe, ← _root_.map_mul, hy2, _root_.map_one]
  have hp1 : pr * pr = 1 := by
    rw [hprdef, ← (CliffordSpin.affinePairEquiv Qq bb A).map_mul, hx2, MulEquiv.map_one]
  have hs1 : sL * sL = 1 := by
    rw [hsLdef, ← (CliffordSpin.coefficientLiftEquiv Qq Ω).map_mul, hp1, MulEquiv.map_one]
  have hu1 : (QuadraticForm.CliffordSpinLift.unit _ sL : CliffordAlgebra (Qq.baseChange Ω)) *
      QuadraticForm.CliffordSpinLift.unit _ sL = 1 := by
    rw [← Units.val_mul, ← _root_.map_mul, hs1, _root_.map_one, Units.val_one]
  rw [hsq] at hu1
  have h2 : (1 : CliffordAlgebra (Qq.baseChange Ω)) + 1 = 0 := by
    nth_rewrite 1 [← hu1]
    exact neg_add_cancel 1
  apply (two_ne_zero : (2 : Ω) ≠ 0)
  apply (algebraMap Ω (CliffordAlgebra (Qq.baseChange Ω))).injective
  rw [_root_.map_ofNat, _root_.map_zero, ← h2, one_add_one_eq_two]

end Langlands.GroupScheme
