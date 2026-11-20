import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof
import Langlands.GroupScheme.Lie.CharZeroTorusLieCentralizerProof
import Langlands.GroupScheme.Lie.TorusCentralizerSliceBaseChange
import Langlands.GroupScheme.Lie.TorusElementCentralizer
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Regular parameters of a maximal torus adjoint slice -/

noncomputable section

universe u

open CategoryTheory _root_.AlgebraicGeometry Module
open scoped Matrix

namespace Langlands.GroupScheme.Lie

set_option backward.isDefEq.respectTransparency false

/-- If a polynomial matrix is surjective after specializing over a field extension,
there is a ground-field polynomial open on which its specializations are surjective. -/
private theorem exists_polynomial_surjective_locus
    {k K : Type u} {σ m n : Type*} [Field k] [Infinite k] [Field K] [Algebra k K]
    [Fintype m] [Fintype n] [DecidableEq n] (M : Matrix n m (MvPolynomial σ k))
    (z : σ → K)
    (hz : Function.Surjective (M.map (MvPolynomial.eval₂Hom (algebraMap k K) z)).mulVec) :
    ∃ p : MvPolynomial σ k, p ≠ 0 ∧ ∀ x, MvPolynomial.eval x p ≠ 0 →
      Function.Surjective (M.map (MvPolynomial.eval x)).mulVec := by
  classical
  obtain ⟨Q, hQ⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp hz
  let M' : Matrix n m (MvPolynomial (σ ⊕ (m × n)) k) := M.map (MvPolynomial.rename Sum.inl)
  let Q' : Matrix m n (MvPolynomial (σ ⊕ (m × n)) k) :=
    Matrix.of fun i j => MvPolynomial.X (Sum.inr (i, j))
  let P := (M' * Q').det
  have hEval {E : Type u} [Field E] (f : k →+* E) (a : σ → E) (D : Matrix m n E) :
      MvPolynomial.eval₂Hom f (Sum.elim a fun ij : m × n => D ij.1 ij.2) P =
        (M.map (MvPolynomial.eval₂Hom f a) * D).det := by
    let ev := MvPolynomial.eval₂Hom f (Sum.elim a fun ij : m × n => D ij.1 ij.2)
    change ev (M' * Q').det = _
    rw [RingHom.map_det]
    change ((M' * Q').map ev).det = _
    rw [Matrix.map_mul]
    congr 2
    · ext i j
      change (MvPolynomial.rename Sum.inl (M i j)).eval₂ f _ = (M i j).eval₂ f _
      rw [MvPolynomial.eval₂_rename]
      rfl
    · ext i j
      simp [Q', ev]
  have hP : P ≠ 0 := by
    intro he
    have h := hEval (algebraMap k K) z Q
    rw [hQ, Matrix.det_one, he, map_zero] at h
    exact zero_ne_one h
  obtain ⟨y, hy⟩ : ∃ y, MvPolynomial.eval y P ≠ 0 := by
    by_contra! h
    exact hP (MvPolynomial.funext (q := 0) fun x => by simpa using h x)
  let x := y ∘ Sum.inl
  let D : Matrix m n k := Matrix.of fun i j => y (Sum.inr (i, j))
  have hy' : Sum.elim x (fun ij : m × n => D ij.1 ij.2) = y := by
    funext i
    rcases i with i | ⟨i, j⟩ <;> rfl
  have hD : (M.map (MvPolynomial.eval x) * D).det ≠ 0 := by
    change (M.map (MvPolynomial.eval₂Hom (RingHom.id k) x) * D).det ≠ 0
    rw [← hEval (RingHom.id k) x D, hy']
    exact hy
  let D' : Matrix m n (MvPolynomial σ k) := D.map MvPolynomial.C
  let p : MvPolynomial σ k := (M * D').det
  have hp (t : σ → k) : MvPolynomial.eval t p = (M.map (MvPolynomial.eval t) * D).det := by
    change MvPolynomial.eval t (M * D').det = _
    rw [RingHom.map_det]
    change ((M * D').map (MvPolynomial.eval t)).det = _
    rw [Matrix.map_mul]
    congr 2
    ext i j
    simp [D']
  refine ⟨p, fun h => hD (by rw [← hp, h, map_zero]), fun t ht v => ?_⟩
  have hUnit : IsUnit (M.map (MvPolynomial.eval t) * D) :=
    Matrix.isUnit_iff_isUnit_det _ |>.mpr (isUnit_iff_ne_zero.mpr (by rwa [hp] at ht))
  obtain ⟨w, hw⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hUnit v
  exact ⟨D *ᵥ w, by rwa [Matrix.mulVec_mulVec]⟩

section Slice

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] {d : ℕ} (c : FiniteCoordinates G d)

/-- The first block is the negative adjoint matrix of `B u`, expressed as a polynomial
in the slice coordinates. The second block is the constant matrix `B`. -/
private def sliceDifferentialMatrix {r : ℕ} (B : Matrix (Fin d) (Fin r) k) :
    Matrix (Fin d) (Fin d ⊕ Fin r) (MvPolynomial (Fin r) k) :=
  Matrix.fromCols (Matrix.of fun i j => -∑ l, MvPolynomial.X l * MvPolynomial.C
    ((adjointRepresentation c).tangentMatrix k
      ((c.equiv (.of (CommRingCat.of k) k)).symm (B.col l)).toMul i j))
    (B.map MvPolynomial.C)

variable {K : Type u} [Field K] [Algebra k K]

local notation "G_K" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k K)) G

local instance regularTorusSlice_baseChangeAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

local instance regularTorusSlice_baseChangeFiniteType : LocallyOfFiniteType (G_K).X.hom := by
  change LocallyOfFiniteType (Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
private theorem kernelBaseChangeEquiv_kernelFieldExtension (ξ : lieKernel G k) :
    kernelBaseChangeEquiv k K G K (kernelFieldExtension (K := K) G ξ) =
      lieKernelMap G (Algebra.ofId k K) ξ :=
  (kernelBaseChangeEquiv k K G K).apply_symm_apply _

set_option maxHeartbeats 600000 in
omit [LocallyOfFiniteType G.X.hom] in
private theorem baseChange_tangentMatrix_coordinateColumn (v : Fin d → k) :
    (adjointRepresentation (c.baseChange k K)).tangentMatrix K
      (((c.baseChange k K).equiv (.of (CommRingCat.of K) K)).symm
        (fun i => algebraMap k K (v i))).toMul =
    ((adjointRepresentation c).tangentMatrix k ((c.equiv (.of (CommRingCat.of k) k)).symm v).toMul).map
      (algebraMap k K) := by
  let ξ := ((c.equiv (.of (CommRingCat.of k) k)).symm v).toMul
  have he : (c.baseChange k K).equiv (.of (CommRingCat.of K) K)
      (Additive.ofMul (kernelFieldExtension (K := K) G ξ)) = fun i => algebraMap k K (v i) := by
    rw [FiniteCoordinates.baseChange_equiv_apply, kernelBaseChangeLinearEquiv_ofMul,
      kernelBaseChangeEquiv_kernelFieldExtension]
    change c.equiv (.of (CommRingCat.of k) K)
      (lieKernelMapLinear G (Algebra.ofId k K) (Additive.ofMul ξ)) = _
    have h := c.naturality (CommAlgCat.ofHom (Algebra.ofId k K)) (Additive.ofMul ξ)
    change c.equiv (.of (CommRingCat.of k) K)
      (lieKernelMapLinear G (Algebra.ofId k K) (Additive.ofMul ξ)) =
      (fun i => algebraMap k K (((c.equiv (.of (CommRingCat.of k) k))
        ((c.equiv (.of (CommRingCat.of k) k)).symm v)) i)) at h
    rw [LinearEquiv.apply_symm_apply] at h
    exact h
  rw [← he, LinearEquiv.symm_apply_apply, toMul_ofMul,
    adjointRepresentation_baseChange_tangentMatrix, kernelBaseChangeEquiv_kernelFieldExtension]
  exact MatrixRepresentation.tangentMatrix_naturality _ _ _

omit [LocallyOfFiniteType G.X.hom] in
private theorem sliceDifferentialMatrix_eval₂ {r : ℕ} (B : Matrix (Fin d) (Fin r) k)
    (t : Fin r → K) :
    (sliceDifferentialMatrix c B).map (MvPolynomial.eval₂Hom (algebraMap k K) t) =
      Matrix.fromCols
        (-(adjointRepresentation (c.baseChange k K)).tangentMatrix K
          (((c.baseChange k K).equiv (.of (CommRingCat.of K) K)).symm
            (B.map (algebraMap k K) *ᵥ t)).toMul)
        (B.map (algebraMap k K)) := by
  let e := (c.baseChange k K).equiv (.of (CommRingCat.of K) K)
  have hs : B.map (algebraMap k K) *ᵥ t =
      ∑ l : Fin r, t l • (fun i => algebraMap k K (B.col l i)) := by
    funext i
    simp [Matrix.mulVec, dotProduct, mul_comm]
  have hd : (adjointRepresentation (c.baseChange k K)).tangentMatrix K
      (e.symm (B.map (algebraMap k K) *ᵥ t)).toMul =
      ∑ l : Fin r, t l • ((adjointRepresentation c).tangentMatrix k
        ((c.equiv (.of (CommRingCat.of k) k)).symm (B.col l)).toMul).map (algebraMap k K) := by
    change (adjointRepresentation (c.baseChange k K)).kernelDifferential K
      (e.symm (B.map (algebraMap k K) *ᵥ t)) = _
    rw [hs, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [map_smul, map_smul]
    congr 1
    exact baseChange_tangentMatrix_coordinateColumn c (B.col l)
  ext i (j | j)
  · simp [sliceDifferentialMatrix, Matrix.fromCols, hd, e, Matrix.sum_apply]
  · simp [sliceDifferentialMatrix, Matrix.fromCols]

omit [Field K] [Algebra k K] [LocallyOfFiniteType G.X.hom] in
private theorem sliceDifferentialMatrix_eval {r : ℕ} (B : Matrix (Fin d) (Fin r) k)
    (t : Fin r → k) :
    (sliceDifferentialMatrix c B).map (MvPolynomial.eval t) =
      Matrix.fromCols
        (-(adjointRepresentation c).tangentMatrix k
          ((c.equiv (.of (CommRingCat.of k) k)).symm (B *ᵥ t)).toMul) B := by
  have hs : B *ᵥ t = ∑ l : Fin r, t l • B.col l := by
    funext i
    simp [Matrix.mulVec, dotProduct, Matrix.col, mul_comm]
  let e := c.equiv (.of (CommRingCat.of k) k)
  have hd : (adjointRepresentation c).tangentMatrix k (e.symm (B *ᵥ t)).toMul =
      ∑ l : Fin r, t l • (adjointRepresentation c).tangentMatrix k
        (e.symm (B.col l)).toMul := by
    change (adjointRepresentation c).kernelDifferential k (e.symm (B *ᵥ t)) = _
    rw [hs, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [map_smul, map_smul]
    rfl
  ext i (j | j)
  · simp [sliceDifferentialMatrix, Matrix.fromCols, hd, e, Matrix.sum_apply]
  · simp [sliceDifferentialMatrix, Matrix.fromCols]

variable {T : CommGroupScheme (Spec (CommRingCat.of k))} (j : T.toGrp ⟶ G)

/-- Surjectivity of the differential of the conjugation slice in finite coordinates at
`(1, t)`, computed by the adjoint action and addition of a column-space vector. -/
def IsRegularTorusSliceParameter
    (t : Fin (finrank k (torusCentralizerCoordinates c j)) → k) : Prop :=
  ∀ v : Fin d → k, ∃ (ξ : lieKernel G k) (s : Fin (finrank k (torusCentralizerCoordinates c j)) → k),
    (adjointRepresentation c).tangentMatrix k ξ *ᵥ (torusCentralizerMatrix c j *ᵥ t) +
      torusCentralizerMatrix c j *ᵥ s = v

omit [Field K] [Algebra k K] in
/-- There is a nonempty polynomial open of regular slice parameters over the original
infinite field. The differential is surjective at one parameter over a splitting field. -/
theorem exists_regularTorusSliceParameter_open [Infinite k] (hT : IsTorus T.toGrp) :
    ∃ p : MvPolynomial (Fin (finrank k (torusCentralizerCoordinates c j))) k,
      p ≠ 0 ∧ ∀ t, MvPolynomial.eval t p ≠ 0 → IsRegularTorusSliceParameter c j t := by
  obtain ⟨K, _, _, _, hsplit⟩ := hT.exists_infinite_isSplitTorus
  let S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T
  let jK : S.toGrp ⟶ (GroupScheme.baseChange (algebraBaseMap k K)).obj G :=
    (GroupScheme.baseChange (algebraBaseMap k K)).map j
  have hS : IsSplitTorus S.toGrp := hsplit
  have : IsAffineHom S.toGrp.X.hom := hS.isAffineHom
  let cK := c.baseChange k K
  let e := cK.equiv (.of (CommRingCat.of K) K)
  let B := torusCentralizerMatrix c j
  let BK := B.map (algebraMap k K)
  obtain ⟨Y, hY, hspan⟩ := exists_regular_targetMap cK jK hS
  obtain ⟨t, ht⟩ := exists_torusCentralizerMatrix_map_mulVec c j _ hY
  have hsurj : Function.Surjective
      ((sliceDifferentialMatrix c B).map (MvPolynomial.eval₂Hom (algebraMap k K) t)).mulVec := by
    intro v
    obtain ⟨X, z, hz, hX⟩ := hspan v
    obtain ⟨s, hs⟩ := exists_torusCentralizerMatrix_map_mulVec c j z hz
    refine ⟨Sum.elim (e (Additive.ofMul X)) s, ?_⟩
    rw [sliceDifferentialMatrix_eval₂, Matrix.fromCols_mulVec_sumElim,
      Matrix.neg_mulVec, ht, hs]
    change -adjointDifferentialFamily cK (e.symm (e (Additive.ofMul (targetMap jK K Y))))
      (e (Additive.ofMul X)) + z = _
    rw [LinearEquiv.symm_apply_apply, ← adjointDifferentialFamily_antisymm]
    exact hX
  obtain ⟨p, hp, h⟩ := exists_polynomial_surjective_locus _ _ hsurj
  refine ⟨p, hp, fun t ht v => ?_⟩
  obtain ⟨w, hw⟩ := h t ht v
  rw [sliceDifferentialMatrix_eval, Matrix.fromCols_mulVec, Matrix.neg_mulVec] at hw
  let ξ := ((c.equiv (.of (CommRingCat.of k) k)).symm (w ∘ Sum.inl)).toMul
  refine ⟨ξ, w ∘ Sum.inr, ?_⟩
  rw [adjointRepresentation_tangentMatrix_mulVec, ofMul_toMul,
    LinearEquiv.apply_symm_apply]
  exact hw

omit [Field K] [Algebra k K] in
/-- The Lie element specified by a slice coordinate vector. -/
def torusSliceElement (t : Fin (finrank k (torusCentralizerCoordinates c j)) → k) :
    lieKernel G k :=
  ((c.equiv (.of (CommRingCat.of k) k)).symm (torusCentralizerMatrix c j *ᵥ t)).toMul

omit [Field K] [Algebra k K] [LocallyOfFiniteType G.X.hom] in
theorem range_le_elementCentralizer_torusSliceElement [CharZero k] [Smooth G.X.hom]
    (hT : IsTorus T.toGrp) (t : Fin (finrank k (torusCentralizerCoordinates c j)) → k) :
    SubgroupFunctor.range j ≤ elementCentralizer G (torusSliceElement c j t) := by
  apply charZeroTorusLieCentralizer k G T j hT
  intro Y
  rw [mem_elementCentralizerLie_iff_adjointDifferential c]
  change adjointDifferentialFamily c (Additive.ofMul (targetMap j k Y))
    ((c.equiv (.of (CommRingCat.of k) k)) ((c.equiv (.of (CommRingCat.of k) k)).symm
      (torusCentralizerMatrix c j *ᵥ t))) = 0
  rw [LinearEquiv.apply_symm_apply, adjointDifferentialFamily_apply, Matrix.toLin'_apply,
    Matrix.mulVec_mulVec, tangentMatrix_targetMap_mul_eq_zero c j _
      (fun i Z => targetMap_mem_elementCentralizerLie_torusCentralizerMatrix c j Z i)]
  simp

omit [Field K] [Algebra k K] [LocallyOfFiniteType G.X.hom] in
/-- The common kernel of the adjoint operators of a maximal torus consists of its tangent
vectors. Cartier's theorem upgrades Lie containment to containment on every test scheme. -/
theorem range_torusCentralizerMatrix_eq [CharZero k] [Smooth G.X.hom]
    [IsAffineHom T.toGrp.X.hom] (hG : IsConnectedReductive G) (hj : IsMaximalTorus j) :
    LinearMap.range (Matrix.toLin' (torusCentralizerMatrix c j)) =
      (LinearMap.range (targetMapLinear j k)).map (c.equiv (.of (CommRingCat.of k) k)).toLinearMap := by
  let e := c.equiv (.of (CommRingCat.of k) k)
  let B := torusCentralizerMatrix c j
  have : IsClosedImmersion j.hom.hom.left := hj.2.1
  have hrep : (torusCentralizer j).IsRepresentedBy j :=
    ⟨Over.mono_of_mono_left _, (maximalTorusCentralizer k G hG T j hj).symm⟩
  ext v
  constructor
  · rintro ⟨t, rfl⟩
    let X := torusSliceElement c j t
    have hX := range_le_elementCentralizer_torusSliceElement c j hj.1 t
    let Y := torusCentralizerTangentFactor j j hrep X hX
    refine ⟨Additive.ofMul X, ⟨Additive.ofMul Y, ?_⟩, ?_⟩
    · exact congrArg Additive.ofMul (targetMap_torusCentralizerTangentFactor j j hrep X hX)
    · change e (e.symm (B *ᵥ t)) = B *ᵥ t
      exact e.apply_symm_apply _
  · rintro ⟨_, ⟨Y, rfl⟩, rfl⟩
    exact exists_torusCentralizerMatrix_mulVec c j _ fun Z =>
      adjointDifferentialFamily_targetMap_targetMap c j Y.toMul Z

omit [Field K] [Algebra k K] in
/-- A regular slice element has tangent centralizer exactly the tangent space of the torus. -/
theorem elementCentralizerLie_eq_range_of_regularTorusSliceParameter
    [CharZero k] [Smooth G.X.hom] [IsAffineHom T.toGrp.X.hom]
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j)
    {t : Fin (finrank k (torusCentralizerCoordinates c j)) → k}
    (ht : IsRegularTorusSliceParameter c j t) :
    elementCentralizerLie G (torusSliceElement c j t) = LinearMap.range (targetMapLinear j k) := by
  let X := torusSliceElement c j t
  let e := c.equiv (.of (CommRingCat.of k) k)
  let A := adjointDifferentialFamily c (Additive.ofMul X)
  let B := torusCentralizerMatrix c j
  let P := LinearMap.range (Matrix.toLin' B)
  have hP : P = (LinearMap.range (targetMapLinear j k)).map e.toLinearMap :=
    range_torusCentralizerMatrix_eq c j hG hj
  have hle : P ≤ LinearMap.ker A := by
    rw [hP]
    rintro _ ⟨_, ⟨Y, rfl⟩, rfl⟩
    apply (mem_elementCentralizerLie_iff_adjointDifferential_self c X
      (targetMap j k Y.toMul)).mp
    apply SubgroupFunctor.lie_mono _ (range_le_elementCentralizer_torusSliceElement c j hj.1 t)
    exact SubgroupFunctor.mem_range.mpr ⟨Y.toMul.val, rfl⟩
  have hspan : LinearMap.range A ⊔ P = ⊤ := by
    apply Submodule.eq_top_iff'.mpr
    intro v
    obtain ⟨Y, s, hs⟩ := ht v
    rw [adjointRepresentation_tangentMatrix_mulVec] at hs
    exact Submodule.mem_sup.mpr ⟨A (-e (Additive.ofMul Y)), ⟨_, rfl⟩,
      B *ᵥ s, ⟨s, rfl⟩, by rwa [map_neg]⟩
  have hdim : finrank k (LinearMap.range A ⊔ P : Submodule k (Fin d → k)) +
      finrank k (LinearMap.range A ⊓ P : Submodule k (Fin d → k)) =
      finrank k (LinearMap.range A) + finrank k P :=
    Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range A) P
  rw [hspan, finrank_top] at hdim
  have hker : P = LinearMap.ker A := by
    have hr : finrank k (LinearMap.range A) + finrank k (LinearMap.ker A) =
        finrank k (Fin d → k) := A.finrank_range_add_finrank_ker
    have hle' : finrank k (Fin d → k) ≤ finrank k (LinearMap.range A) + finrank k P :=
      le_trans (Nat.le_add_right _ _) hdim.le
    exact Submodule.eq_of_le_of_finrank_le hle (Nat.le_of_add_le_add_left (hr.le.trans hle'))
  ext Y
  have hmem := mem_elementCentralizerLie_iff_adjointDifferential_self c X Y.toMul
  change (Y ∈ elementCentralizerLie G X) ↔ _
  rw [ofMul_toMul] at hmem
  rw [hmem]
  change e Y ∈ LinearMap.ker A ↔ _
  rw [← hker, hP]
  exact ⟨fun ⟨Z, hZ, hYZ⟩ => e.injective hYZ ▸ hZ, fun hY => ⟨Y, hY, rfl⟩⟩

end Slice

/-- The adjoint slice of a maximal torus has a nonempty polynomial open of parameters
where the conjugation differential is surjective and the tangent centralizer is the torus
tangent space. -/
def RegularMaximalTorusSliceStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [Smooth G.X.hom] (T : CommGroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom T.toGrp.X.hom] (j : T.toGrp ⟶ G) {d : ℕ} (c : FiniteCoordinates G d),
    IsConnectedReductive G → IsMaximalTorus j →
      ∃ p : MvPolynomial (Fin (finrank k (torusCentralizerCoordinates c j))) k,
        p ≠ 0 ∧ ∀ t, MvPolynomial.eval t p ≠ 0 →
          IsRegularTorusSliceParameter c j t ∧
            elementCentralizerLie G (torusSliceElement c j t) = LinearMap.range (targetMapLinear j k)

theorem regularMaximalTorusSlice : RegularMaximalTorusSliceStatement.{u} := by
  intro k _ _ G _ _ T _ j d c hG hj
  obtain ⟨p, hp, hreg⟩ := exists_regularTorusSliceParameter_open c j hj.1
  exact ⟨p, hp, fun t ht => ⟨hreg t ht,
    elementCentralizerLie_eq_range_of_regularTorusSliceParameter c j hG hj (hreg t ht)⟩⟩

end Langlands.GroupScheme.Lie
