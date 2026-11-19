import Langlands.GroupScheme.Lie.TorusCentralizerSliceBaseChange
import Langlands.GroupScheme.Torus.ConnectedReductive
import Mathlib.Algebra.MvPolynomial.Funext

/-! # A regular point of the torus Lie slice over the ground field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.Lie

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {d : ℕ} (c : FiniteCoordinates G d)

/-- The matrix of `x ↦ [x, v]` in the chosen Lie coordinates. -/
def adjointMatrixAt (A : Type u) [CommRing A] [Algebra k A]
    (v : Fin d → A) : Matrix (Fin d) (Fin d) A :=
  -(adjointRepresentation c).tangentMatrix A
    ((c.equiv (.of (CommRingCat.of k) A)).symm v).toMul

variable {A E : Type u} [CommRing A] [Algebra k A] [CommRing E] [Algebra k E]

/-- Bracket matrices in the chosen coordinates commute with coefficient maps. -/
theorem adjointMatrixAt_map (f : A →ₐ[k] E) (v : Fin d → A) :
    (adjointMatrixAt c A v).map f = adjointMatrixAt c E (fun i => f (v i)) := by
  let x := (c.equiv (.of (CommRingCat.of k) A)).symm v
  have hx : lieKernelMapLinear G f x =
      (c.equiv (.of (CommRingCat.of k) E)).symm (fun i => f (v i)) := by
    apply (c.equiv (.of (CommRingCat.of k) E)).injective
    have h := c.naturality (CommAlgCat.ofHom f) x
    change c.equiv (.of (CommRingCat.of k) E) (lieKernelMapLinear G f x) = _ at h
    rw [LinearEquiv.apply_symm_apply, h]
    simp only [x, LinearEquiv.apply_symm_apply]
    rfl
  have h := congrArg Additive.toMul hx
  change lieKernelMap G f x.toMul = _ at h
  rw [adjointMatrixAt, adjointMatrixAt, Matrix.map_neg f f.map_neg,
    ← MatrixRepresentation.tangentMatrix_naturality, h]

/-- The bracket matrix acts by evaluating the adjoint differential of the argument
on the fixed vector. -/
theorem adjointMatrixAt_mulVec [LocallyOfFiniteType G.X.hom]
    (v : Fin d → k) (X : lieKernel G k) :
    adjointMatrixAt c k v *ᵥ (c.equiv (.of (CommRingCat.of k) k) (Additive.ofMul X)) =
      (adjointRepresentation c).tangentMatrix k X *ᵥ v := by
  rw [adjointRepresentation_tangentMatrix_mulVec, adjointMatrixAt, Matrix.neg_mulVec]
  rfl

variable {e : ℕ}

/-- The determinant of the bracket matrix of `B t` with a constant matrix added. -/
def adjointSliceDeterminant (B : Matrix (Fin d) (Fin e) k)
    (P : Matrix (Fin d) (Fin d) k) : MvPolynomial (Fin e) k :=
  let U := MvPolynomial (Fin e) k
  (adjointMatrixAt c U (B.map (algebraMap k U) *ᵥ MvPolynomial.X) +
    P.map (algebraMap k U)).det

@[simp]
theorem aeval_adjointSliceDeterminant (B : Matrix (Fin d) (Fin e) k)
    (P : Matrix (Fin d) (Fin d) k) (t : Fin e → E) :
    MvPolynomial.aeval t (adjointSliceDeterminant c B P) =
      (adjointMatrixAt c E (B.map (algebraMap k E) *ᵥ t) + P.map (algebraMap k E)).det := by
  let f : MvPolynomial (Fin e) k →ₐ[k] E := MvPolynomial.aeval t
  change f (adjointSliceDeterminant c B P) = _
  unfold adjointSliceDeterminant
  rw [f.map_det, AlgHom.mapMatrix_apply, Matrix.map_add f f.map_add, adjointMatrixAt_map]
  have hB : (B.map (algebraMap k (MvPolynomial (Fin e) k))).map f = B.map (algebraMap k E) := by
    ext i j
    exact f.commutes (B i j)
  have hP : (P.map (algebraMap k (MvPolynomial (Fin e) k))).map f = P.map (algebraMap k E) := by
    ext i j
    exact f.commutes (P i j)
  have hv : (fun i => f ((B.map (algebraMap k _) *ᵥ MvPolynomial.X) i)) =
      B.map (algebraMap k E) *ᵥ t := by
    funext i
    change f.toRingHom ((B.map (algebraMap k _) *ᵥ MvPolynomial.X) i) = _
    rw [RingHom.map_mulVec]
    change ((B.map (algebraMap k _)).map f *ᵥ (fun j => f (MvPolynomial.X j))) i = _
    rw [hB]
    simp [f]
  rw [hv, hP]

private theorem isUnit_add_mul_of_range {K : Type u} [Field K]
    {M : Matrix (Fin d) (Fin d) K} {B : Matrix (Fin d) (Fin e) K}
    {D : Matrix (Fin e) (Fin d) K} (hDB : D * B = 1) (hMB : M * B = 0)
    (h : ∀ v, ∃ x y, M *ᵥ x + B *ᵥ y = v) : IsUnit (M + B * D) := by
  rw [← Matrix.mulVec_surjective_iff_isUnit]
  intro v
  obtain ⟨x, y, rfl⟩ := h v
  have hM (w) : M *ᵥ (B *ᵥ w) = 0 := by rw [Matrix.mulVec_mulVec, hMB, Matrix.zero_mulVec]
  have hD (w) : D *ᵥ (B *ᵥ w) = w := by rw [Matrix.mulVec_mulVec, hDB, Matrix.one_mulVec]
  refine ⟨x - B *ᵥ (D *ᵥ x) + B *ᵥ y, ?_⟩
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_add,
    Matrix.mulVec_sub, hM, hM, sub_zero, add_zero, Matrix.mulVec_add, Matrix.mulVec_sub,
    hD, hD, sub_self, zero_add]

variable {T : CommGroupScheme (Spec (CommRingCat.of k))} (j : T.toGrp ⟶ G)

/-- The basis matrix of the torus Lie centralizer admits a left inverse. -/
theorem exists_leftInverse_torusCentralizerMatrix :
    ∃ D : Matrix (Fin (Module.finrank k (torusCentralizerCoordinates c j))) (Fin d) k,
      D * torusCentralizerMatrix c j = 1 := by
  let C := torusCentralizerCoordinates c j
  let b := Module.finBasis k C
  let B := torusCentralizerMatrix c j
  have hB (x) : B *ᵥ x = (b.equivFun.symm x : Fin d → k) := by
    rw [Module.Basis.equivFun_symm_apply]
    ext i
    simp [B, b, C, torusCentralizerMatrix, Matrix.mulVec, dotProduct, mul_comm]
  have hinj : Function.Injective B.mulVec := fun x y h =>
    b.equivFun.symm.injective (Subtype.ext ((hB x).symm.trans (h.trans (hB y))))
  obtain ⟨L, hL⟩ := B.mulVecLin.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨Matrix.toLin'.symm L, Matrix.ext_iff_mulVec.mpr fun x => ?_⟩
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec, ← Matrix.toLin'_apply,
    LinearEquiv.apply_symm_apply]
  exact LinearMap.congr_fun hL x

variable [LocallyOfFiniteType G.X.hom]

/-- A parameter over a splitting extension gives a nonzero value of the determinant. -/
private theorem exists_regular_torusCentralizerMatrix_over_splittingField (hT : IsTorus T.toGrp)
    (D : Matrix (Fin (Module.finrank k (torusCentralizerCoordinates c j))) (Fin d) k)
    (hDB : D * torusCentralizerMatrix c j = 1) :
    adjointSliceDeterminant c (torusCentralizerMatrix c j) (torusCentralizerMatrix c j * D) ≠ 0 := by
  obtain ⟨Ω, _, _, _, hS'⟩ := hT.exists_infinite_isSplitTorus
  have : Smooth T.toGrp.X.hom := hT.smooth
  have : LocallyOfFiniteType T.toGrp.X.hom := inferInstance
  have : IsAffineHom T.toGrp.X.hom := hT.isConnectedReductive_of_fieldSplitting.isAffineHom
  let f := algebraBaseMap k Ω
  let S := (CommGroupScheme.baseChange f).obj T
  let H := (GroupScheme.baseChange f).obj G
  let i : S.toGrp ⟶ H := (GroupScheme.baseChange f).map j
  have : IsAffineHom H.X.hom := by
    change IsAffineHom (Limits.pullback.snd G.X.hom f)
    infer_instance
  have : LocallyOfFiniteType H.X.hom := by
    change LocallyOfFiniteType (Limits.pullback.snd G.X.hom f)
    infer_instance
  let cH := c.baseChange k Ω
  have hS : IsSplitTorus S.toGrp := hS'
  have : IsAffineHom S.toGrp.X.hom := hS.isAffineHom
  obtain ⟨Y, hY₁, hY₂⟩ := exists_regular_targetMap cH i hS
  let B := torusCentralizerMatrix c j
  let BΩ := B.map (algebraMap k Ω)
  let DΩ := D.map (algebraMap k Ω)
  let X := targetMap i Ω Y
  obtain ⟨t, ht⟩ := exists_torusCentralizerMatrix_map_mulVec c j _ hY₁
  have ht' : BΩ *ᵥ t = cH.equiv (.of (CommRingCat.of Ω) Ω) (Additive.ofMul X) := ht
  let M := adjointMatrixAt c Ω (BΩ *ᵥ t)
  have hM : M = -(adjointRepresentation cH).tangentMatrix Ω X := by
    rw [show M = adjointMatrixAt c Ω (BΩ *ᵥ t) from rfl, ht', adjointMatrixAt,
      FiniteCoordinates.baseChange_equiv_apply, kernelBaseChangeLinearEquiv_ofMul,
      LinearEquiv.symm_apply_apply, toMul_ofMul, adjointRepresentation_baseChange_tangentMatrix]
  have hDBΩ : DΩ * BΩ = 1 := by
    change D.map (algebraMap k Ω) * B.map (algebraMap k Ω) = 1
    rw [← Matrix.map_mul, hDB]
    exact Matrix.map_one (algebraMap k Ω) (map_zero _) (map_one _)
  have hMB : M * BΩ = 0 := by
    apply Matrix.ext_iff_mulVec.mpr
    intro s
    rw [Matrix.zero_mulVec, ← Matrix.mulVec_mulVec, hM, Matrix.neg_mulVec]
    exact neg_eq_zero.mpr (tangentMatrix_targetMap_baseChange_mulVec_eq_zero c j B
      (fun a Y' => targetMap_mem_elementCentralizerLie_torusCentralizerMatrix c j Y' a) s Y)
  have hspan : ∀ v, ∃ x y, M *ᵥ x + BΩ *ᵥ y = v := by
    intro v
    obtain ⟨Z, z, hz, hv⟩ := hY₂ v
    obtain ⟨s, hs⟩ := exists_torusCentralizerMatrix_map_mulVec c j z hz
    refine ⟨cH.equiv (.of (CommRingCat.of Ω) Ω) (Additive.ofMul Z), s, ?_⟩
    rw [hM, hs, Matrix.neg_mulVec]
    change -(adjointDifferentialFamily cH (Additive.ofMul X))
      (cH.equiv (.of (CommRingCat.of Ω) Ω) (Additive.ofMul Z)) + z = v
    rw [← adjointDifferentialFamily_antisymm cH X Z]
    exact hv
  have hu : IsUnit (M + BΩ * DΩ) := isUnit_add_mul_of_range hDBΩ hMB hspan
  intro hp
  have hav := congrArg (MvPolynomial.aeval t) hp
  rw [map_zero, aeval_adjointSliceDeterminant, Matrix.map_mul] at hav
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero hav

/-- The torus Lie slice has a parameter over the infinite ground field where the
bracket matrix plus the projection onto the slice is invertible. -/
theorem exists_isUnit_adjointMatrixAt_torusCentralizerMatrix [Infinite k] (hT : IsTorus T.toGrp)
    (D : Matrix (Fin (Module.finrank k (torusCentralizerCoordinates c j))) (Fin d) k)
    (hDB : D * torusCentralizerMatrix c j = 1) :
    ∃ t, IsUnit (adjointMatrixAt c k (torusCentralizerMatrix c j *ᵥ t) +
      torusCentralizerMatrix c j * D) := by
  let B := torusCentralizerMatrix c j
  have hp := exists_regular_torusCentralizerMatrix_over_splittingField c j hT D hDB
  by_contra! h
  apply hp
  apply MvPolynomial.funext
  intro t
  change MvPolynomial.aeval t (adjointSliceDeterminant c B (B * D)) = MvPolynomial.aeval t 0
  rw [map_zero, aeval_adjointSliceDeterminant]
  have hm {r : ℕ} (N : Matrix (Fin d) (Fin r) k) : N.map (algebraMap k k) = N := by
    ext i j
    simp
  rw [hm, hm]
  by_contra hne
  exact h t ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hne))

/-- Over an infinite field, the torus Lie centralizer basis admits a projection and a
parameter where the bracket matrix plus the projection is invertible. -/
def RegularTorusLieSliceStatement : Prop :=
  ∀ (k : Type u) [Field k] [Infinite k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (d : ℕ) (c : FiniteCoordinates G d)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G),
    IsTorus T.toGrp →
      ∃ D : Matrix (Fin (Module.finrank k (torusCentralizerCoordinates c j))) (Fin d) k,
        let B := torusCentralizerMatrix c j
        D * B = 1 ∧ ∃ t, IsUnit (adjointMatrixAt c k (B *ᵥ t) + B * D)

theorem regularTorusLieSlice : RegularTorusLieSliceStatement.{u} := by
  intro k _ _ G _ _ d c T j hT
  obtain ⟨D, hD⟩ := exists_leftInverse_torusCentralizerMatrix c j
  exact ⟨D, hD, exists_isUnit_adjointMatrixAt_torusCentralizerMatrix c j hT D hD⟩

end Langlands.GroupScheme.Lie
