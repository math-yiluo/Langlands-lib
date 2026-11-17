import Langlands.GroupScheme.Reductive.InvariantIdealLift
import Langlands.GroupScheme.MatrixRepresentation.DirectSum

/-! # Finite covariant coefficient families -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Module
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.InvariantPowerLift

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
  {J H : GroupScheme (Spec (CommRingCat.of k))}
  {I : Type} [Fintype I] [DecidableEq I]
  {n : I → Type} [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]

/-- A row family supported on one summand of a finite direct sum. -/
def blockFamily (f : ∀ i, n i → ((algΓ (CommRingCat.of k)).obj J.X).unop)
    (i : I) (j : Σ i, n i) : ((algΓ (CommRingCat.of k)).obj J.X).unop :=
  if j.1 = i then f j.1 j.2 else 0

omit [∀ i, DecidableEq (n i)] in
/-- The linear combination in each block recovers its original family. -/
theorem familyLinearMap_blockFamily (f : ∀ i, n i → ((algΓ (CommRingCat.of k)).obj J.X).unop)
    (v : ∀ i, n i → k) (i : I) :
    familyLinearMap (blockFamily f i) (fun j => v j.1 j.2) =
      familyLinearMap (f i) (v i) := by
  classical
  change (∑ j : Σ i, n i, v j.1 j.2 • blockFamily f i j) =
    ∑ j, v i j • f i j
  simp [Fintype.sum_sigma, blockFamily]

/-- Each supported row is covariant for the direct-sum representation. -/
theorem isRightCovariantFamily_blockFamily
    (iH : H ⟶ J) (ρ : ∀ i, MatrixRepresentation H (n i))
    (f : ∀ i, n i → ((algΓ (CommRingCat.of k)).obj J.X).unop)
    (hf : ∀ i, IsRightCovariantFamily iH (ρ i) (f i)) (i : I) :
    IsRightCovariantFamily iH (MatrixRepresentation.directSum ρ) (blockFamily f i) := by
  intro T g h
  rw [MatrixRepresentation.directSum_pointMatrix_val]
  ext ⟨a, j⟩
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Fintype.sum_sigma]
  have hblock (b : I) :
      (∑ r, Matrix.blockDiagonal' (fun a =>
        (ρ a).pointMatrix T h) ⟨b, r⟩ ⟨a, j⟩ *
          g.left.appTop (blockFamily f i ⟨b, r⟩)) =
        if b = a then
          ∑ r, (ρ a).pointMatrix T h r j * g.left.appTop (blockFamily f i ⟨a, r⟩)
        else 0 := by
    by_cases hb : b = a
    · subst b
      simp only [Matrix.blockDiagonal'_apply_eq, ↓reduceIte]
    · simp only [ite_eq_right hb, Matrix.blockDiagonal'_apply_ne _ _ _ hb,
        zero_mul, Finset.sum_const_zero]
  simp only [hblock, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  by_cases hai : a = i
  · subst a
    simpa only [blockFamily, ↓reduceIte, Matrix.mulVec, dotProduct, Matrix.transpose_apply] using congrFun (hf i T g h) j
  · simp only [blockFamily, ite_eq_right hai, map_zero, mul_zero, Finset.sum_const_zero]

section Weighted

variable {r : Type} [Fintype r] [DecidableEq r]

omit [DecidableEq I] in
/-- Weighting covariant rows by invariant sections preserves covariance. -/
theorem isRightCovariantFamily_weighted
    (iH : H ⟶ J) (ρ : MatrixRepresentation H r)
    (s : I → ((algΓ (CommRingCat.of k)).obj J.X).unop)
    (hs : ∀ i, HomogeneousQuotientFromEmbedding.IsRightInvariant iH (s i))
    (f : I → r → ((algΓ (CommRingCat.of k)).obj J.X).unop)
    (hf : ∀ i, IsRightCovariantFamily iH ρ (f i)) :
    IsRightCovariantFamily iH ρ (fun j => ∑ i, s i * f i j) := by
  intro T g h
  ext j
  simp only [map_sum, map_mul, congrFun (hf _ T g h), Matrix.mulVec,
    dotProduct, Matrix.transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro i _
  rw [hs i T g h]
  ring

omit [DecidableEq I] [DecidableEq r] in
/-- Linear combination of a weighted family is the weighted sum of row combinations. -/
theorem familyLinearMap_weighted
    (s : I → ((algΓ (CommRingCat.of k)).obj J.X).unop)
    (f : I → r → ((algΓ (CommRingCat.of k)).obj J.X).unop) (v : r → k) :
    familyLinearMap (fun j => ∑ i, s i * f i j) v =
      ∑ i, s i * familyLinearMap (f i) v := by
  simp only [familyLinearMap_apply, Finset.mul_sum,
    Algebra.smul_def]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [DecidableEq I] in
/-- Covariant rows with an invariant weighted combination equal to one can be
restricted so that their weighted columns are nonzero dual-fixed scalars. -/
theorem exists_scalar_covariant_rows
    [IsAlgClosed k] [Smooth H.X.hom]
    [Nontrivial ((algΓ (CommRingCat.of k)).obj J.X).unop]
    (iH : H ⟶ J) (ρ : MatrixRepresentation H r)
    (s : I → ((algΓ (CommRingCat.of k)).obj J.X).unop)
    (hs : ∀ i, HomogeneousQuotientFromEmbedding.IsRightInvariant iH (s i))
    (f : I → r → ((algΓ (CommRingCat.of k)).obj J.X).unop)
    (hf : ∀ i, IsRightCovariantFamily iH ρ (f i)) (v : r → k)
    (hv : ∑ i, s i * familyLinearMap (f i) v = 1) :
    ∃ (d : ℕ) (σ : MatrixRepresentation H (Fin d))
      (g : I → Fin d → ((algΓ (CommRingCat.of k)).obj J.X).unop) (c : Fin d → k),
      (∀ i, IsRightCovariantFamily iH σ (g i)) ∧
      (∀ j, ∑ i, s i * g i j = algebraMap k _ (c j)) ∧
      c ≠ 0 ∧ σ.dual.IsFixedVector c := by
  classical
  let := Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
    k H.X.left H.X.hom
  let A := ((algΓ (CommRingCat.of k)).obj J.X).unop
  let w : r → A := fun j => ∑ i, s i * f i j
  have hw : IsRightCovariantFamily iH ρ w :=
    isRightCovariantFamily_weighted iH ρ s hs f hf
  let W := scalarPreimage (AlgHom.id k A)
  have hW : ∀ (h : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X) (a : A),
      a ∈ W → rightTranslation iH h a ∈ W := by
    intro h a ha
    obtain ⟨c, hc⟩ := (mem_scalarPreimage (AlgHom.id k A) a).1 ha
    change a = algebraMap k A c at hc
    apply (mem_scalarPreimage (AlgHom.id k A) _).2
    refine ⟨c, ?_⟩
    change rightTranslation iH h a = _
    rw [hc, AlgHom.commutes]
  let U := W.comap (familyLinearMap w)
  obtain ⟨d, B, C, hCB, hcols, hproj⟩ :=
    MatrixRepresentation.exists_subspace_split_coordinates U
  have hstable : ρ.IsStableCoordinates B C :=
    hw.isStableCoordinates_comap W hW B C hcols hproj
  let σ := ρ.restrictCoordinates B C hCB hstable
  let g : I → Fin d → A := fun i => coordinateFamily B (f i)
  let w' : Fin d → A := coordinateFamily B w
  have hw' : IsRightCovariantFamily iH σ w' :=
    hw.restrictCoordinates B C hCB hstable
  have hw'W (j : Fin d) : w' j ∈ W := by
    rw [show w' j = familyLinearMap w (fun a => B a j) from coordinateFamily_apply B w j]
    exact hcols j
  choose c hc using fun j => (mem_scalarPreimage (AlgHom.id k A) (w' j)).1 (hw'W j)
  change ∀ j, w' j = algebraMap k A (c j) at hc
  have hweighted (j : Fin d) : ∑ i, s i * g i j = w' j := by
    simp only [g, w', coordinateFamily_apply]
    exact (familyLinearMap_weighted s f (fun a => B a j)).symm
  have hvw : familyLinearMap w v = 1 :=
    (familyLinearMap_weighted s f v).trans hv
  have hvU : familyLinearMap w v ∈ W := by
    apply (mem_scalarPreimage (AlgHom.id k A) _).2
    exact ⟨1, hvw.trans (map_one _).symm⟩
  have hv' : familyLinearMap w' (C *ᵥ v) = 1 := by
    rw [familyLinearMap_coordinateFamily, Matrix.mulVec_mulVec,
      hproj v hvU, hvw]
  have hc0 : c ≠ 0 := by
    intro hz
    have hwzero (j : Fin d) : w' j = 0 := by
      simpa only [hz, Pi.zero_apply, map_zero] using hc j
    simp only [familyLinearMap_apply, hwzero, smul_zero, Finset.sum_const_zero] at hv'
    exact zero_ne_one hv'
  have hfix : σ.dual.IsFixedVector c :=
    hw'.dual_fixed_of_scalar_images (AlgHom.id k A) c hc (by
      intro h j
      change rightTranslation iH h (w' j) = w' j
      rw [hc j, AlgHom.commutes])
  exact ⟨d, σ, g, c, (fun i => (hf i).restrictCoordinates B C hCB hstable),
    (fun j => (hweighted j).trans (hc j)), hc0, hfix⟩

end Weighted

/-- A unit-ideal relation among invariant sections admits a finite covariant
coefficient family with a nonzero dual-fixed scalar weighted sum. -/
theorem exists_scalar_covariant_coefficients
    [IsAlgClosed k] [Smooth H.X.hom] [IsAffine J.X.left]
    (iH : H ⟶ J)
    (s : I → ((algΓ (CommRingCat.of k)).obj J.X).unop)
    (hs : ∀ i, HomogeneousQuotientFromEmbedding.IsRightInvariant iH (s i))
    (a : I → ((algΓ (CommRingCat.of k)).obj J.X).unop)
    (ha : ∑ i, s i * a i = 1) :
    ∃ (d : ℕ) (σ : MatrixRepresentation H (Fin d))
      (g : I → Fin d → ((algΓ (CommRingCat.of k)).obj J.X).unop) (c : Fin d → k),
      (∀ i, IsRightCovariantFamily iH σ (g i)) ∧
      (∀ j, ∑ i, s i * g i j = algebraMap k _ (c j)) ∧
      c ≠ 0 ∧ σ.dual.IsFixedVector c := by
  classical
  let := Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
    k H.X.left H.X.hom
  have : Nontrivial Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤) := by
    change Nontrivial Γ(Spec (CommRingCat.of k), ⊤)
    exact (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have : Nontrivial ((algΓ (CommRingCat.of k)).obj J.X).unop :=
    (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ J.X).left.appTop.hom.domain_nontrivial
  choose d ρ f v hf _ hv using fun i =>
    exists_covariantFamily_in_submodule iH ⊤
      (fun _ _ _ => Submodule.mem_top) (a i) Submodule.mem_top
  refine exists_scalar_covariant_rows iH (MatrixRepresentation.directSum ρ) s hs
    (blockFamily f) (isRightCovariantFamily_blockFamily iH ρ f hf)
    (fun j => v j.1 j.2) ?_
  simpa only [familyLinearMap_blockFamily, hv] using ha

end Langlands.GroupScheme.InvariantPowerLift
