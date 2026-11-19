import Langlands.GroupScheme.OddOrthogonalForm.QuadraticDescent
import Langlands.GroupScheme.Quaternionic.ScalarNormOnePoints

/-! # The norm-one isometry group of the descended scalar form -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.OddOrthogonalForm

open OddOrthogonalMatrix
open OrthogonalMatrix (IsAlt)
open Quaternionic.FirstKindInvolution
open Quaternionic.ScalarNormOnePoints (matrix matrix_naturality)

section Congruence

variable {i : Type*} [Fintype i] [DecidableEq i] {R : Type*} [CommRing R]

omit [DecidableEq i] in
private theorem congruence_comp (P A D : Matrix i i R) :
    P * (A * D * Aᵀ) * Pᵀ = (P * A) * D * (P * A)ᵀ := by
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]

private theorem isAlt_congruence_iff (P : GL i R) (D : Matrix i i R) :
    IsAlt (P.val * D * P.valᵀ) ↔ IsAlt D := by
  constructor
  · intro h
    have hinv := h.conj P⁻¹.val
    rwa [congruence_comp, Units.inv_mul, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one] at hinv
  · exact fun h => h.conj P.val

omit [DecidableEq i] in
private theorem isAlt_defect_iff {D Q : Matrix i i R} (h : IsAlt (D - Q)) (g : Matrix i i R) :
    IsAlt (g * D * gᵀ - D) ↔ IsAlt (g * Q * gᵀ - Q) := by
  have hdiff : IsAlt ((g * D * gᵀ - D) - (g * Q * gᵀ - Q)) := by
    have h' := (h.conj g).sub h
    simp only [Matrix.mul_sub, Matrix.sub_mul] at h'
    convert h' using 1
    abel
  constructor
  · intro hD
    convert hD.sub hdiff using 1
    abel
  · intro hQ
    convert hdiff.add hQ using 1
    abel

private theorem conj_quadratic_iff (P g : GL i R) {D Q : Matrix i i R}
    (h : IsAlt (P.val * D * P.valᵀ - Q)) :
    IsAlt ((MulAut.conj P g).val * Q * (MulAut.conj P g).valᵀ - Q) ↔
      IsAlt (g.val * D * g.valᵀ - D) := by
  let A := (MulAut.conj P g).val
  have hAP : A * P.val = P.val * g.val := by
    change (P * g * P⁻¹ * P).val = (P * g).val
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  calc
    IsAlt (A * Q * Aᵀ - Q) ↔ IsAlt (A * (P.val * D * P.valᵀ) * Aᵀ - P.val * D * P.valᵀ) :=
      (isAlt_defect_iff h A).symm
    _ ↔ IsAlt (P.val * (g.val * D * g.valᵀ - D) * P.valᵀ) := by
      rw [congruence_comp, hAP, ← congruence_comp, Matrix.mul_sub, Matrix.sub_mul]
    _ ↔ IsAlt (g.val * D * g.valᵀ - D) := isAlt_congruence_iff P _

private theorem det_conj (P g : GL i R) : (MulAut.conj P g).val.det = g.val.det := by
  have h : Matrix.GeneralLinearGroup.det (MulAut.conj P g) = Matrix.GeneralLinearGroup.det g := by
    simp only [MulAut.conj_apply, _root_.map_mul, _root_.map_inv, mul_assoc]
    rw [mul_left_comm, mul_inv_cancel, mul_one]
  exact congrArg Units.val h

end Congruence

variable {K : Type u} [Field K] {N : Type u} [Field N] [Algebra K N] {n : ℕ}
variable {H : GroupScheme (Spec (CommRingCat.of K))}
  (φ : LocalGroupIso H (splitGroup K n) (ringTest K N)) [FiniteDimensional K N] [IsGalois K N]

/-- The full actual norm-one isometry target of the descended form. -/
abbrev descendedGroup (hn : 2 ≤ n) := (scalar K).normOneIsometryGroup (descendedForm φ hn)

private def basisAt (hn : 2 ≤ n) {V : Over (Spec (CommRingCat.of K))}
    (s : V ⟶ ringTest K N) : GL (Index (Fin n)) Γ(V.left, ⊤) :=
  Matrix.GeneralLinearGroup.map (sectionScalars s) (descentBasis φ hn)

private theorem basisAt_congruence (hn : 2 ≤ n) {V : Over (Spec (CommRingCat.of K))}
    (s : V ⟶ ringTest K N) :
    let f : K →+* Γ(V.left, ⊤) := algebraMap K ((algΓ (CommRingCat.of K)).obj V).unop
    IsAlt ((basisAt φ hn s).val * (descendedMatrix φ hn).map f * (basisAt φ hn s).valᵀ -
      (formMatrix (Fin n) K).map f) := by
  let f : K →+* Γ(V.left, ⊤) := algebraMap K ((algΓ (CommRingCat.of K)).obj V).unop
  have h := (descentBasis_congruence φ hn).map (sectionScalars s)
  rw [Matrix.map_sub _ (_root_.map_sub _), Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map,
    Matrix.map_map] at h
  change IsAlt ((basisAt φ hn s).val * (descendedMatrix φ hn).map
    ((sectionScalars s).comp (algebraMap K N)) * (basisAt φ hn s).valᵀ -
      (formMatrix (Fin n) N).map (sectionScalars s)) at h
  rw [SpecialLinearInnerForm.pointScalars_comp_algebraMap, formMatrix_map_compare (sectionScalars s) f] at h
  exact h

private theorem conj_mem_range_iff (hn : 2 ≤ n) {V : Over (Spec (CommRingCat.of K))}
    (s : V ⟶ ringTest K N) (g : GL (Index (Fin n)) Γ(V.left, ⊤)) :
    MulAut.conj (basisAt φ hn s) g ∈ (matrix (form (Fin n) K) V).range ↔
      g ∈ (matrix (descendedForm φ hn) V).range := by
  rw [Quaternionic.ScalarNormOnePoints.mem_range_matrix_iff (form (Fin n) K) (formMatrix (Fin n) K) rfl,
    Quaternionic.ScalarNormOnePoints.mem_range_matrix_iff (descendedForm φ hn) (descendedMatrix φ hn) rfl]
  refine and_congr (conj_quadratic_iff (basisAt φ hn s) g (basisAt_congruence φ hn s)) ?_
  rw [det_conj]

private theorem split_pointMatrix_eq (V : Over (Spec (CommRingCat.of K)))
    (x : V ⟶ (splitGroup K n).X) : pointMatrix K V x = matrix (form (Fin n) K) V x := rfl

private def basisPointsEquiv (hn : 2 ≤ n) {V : Over (Spec (CommRingCat.of K))}
    (s : V ⟶ ringTest K N) : (V ⟶ (descendedGroup φ hn).X) ≃* (V ⟶ (splitGroup K n).X) :=
  Quaternionic.ScalarNormOnePoints.pointsEquiv (descendedForm φ hn)
    (form (Fin n) K) V (MulAut.conj (basisAt φ hn s)) (conj_mem_range_iff φ hn s)

private theorem pointMatrix_basisPointsEquiv (hn : 2 ≤ n) {V : Over (Spec (CommRingCat.of K))}
    (s : V ⟶ ringTest K N) (x : V ⟶ (descendedGroup φ hn).X) :
    pointMatrix K V (basisPointsEquiv φ hn s x) =
      MulAut.conj (basisAt φ hn s) (matrix (descendedForm φ hn) V x) := by
  rw [split_pointMatrix_eq]
  exact Quaternionic.ScalarNormOnePoints.matrix_pointsEquiv _ _ _ _
    (conj_mem_range_iff φ hn s) x

/-- On each relative test, change of basis acts by conjugation by the same Hilbert-90 matrix. -/
def localIso_descendedGroup (hn : 2 ≤ n) :
    LocalGroupIso (descendedGroup φ hn) (splitGroup K n) (ringTest K N) where
  toFun s := basisPointsEquiv φ hn s
  naturality b s x := by
    apply pointMatrix_injective
    simp only [pointMatrix_naturality, pointMatrix_basisPointsEquiv, MulAut.conj_apply,
      _root_.map_mul, _root_.map_inv, matrix_naturality]
    have hb : basisAt φ hn (b ≫ s) =
        Matrix.GeneralLinearGroup.map b.left.appTop.hom (basisAt φ hn s) := by
      have hs : sectionScalars (b ≫ s) = b.left.appTop.hom.comp (sectionScalars s) :=
        SpecialLinearInnerForm.pointScalars_comp b s
      rw [basisAt, hs]
      rfl
    rw [hb]

private theorem pointMatrix_localIso (hn : 2 ≤ n) {V : Over (Spec (CommRingCat.of K))}
    (s : V ⟶ ringTest K N) (x : V ⟶ (descendedGroup φ hn).X) :
    pointMatrix K V ((localIso_descendedGroup φ hn).toFun s x) =
      MulAut.conj (basisAt φ hn s) (matrix (descendedForm φ hn) V x) :=
  pointMatrix_basisPointsEquiv φ hn s x

omit [IsGalois K N] in
private theorem basisAt_galois (hn : 2 ≤ n) (σ : N ≃ₐ[K] N)
    {V : Over (Spec (CommRingCat.of K))} (s : V ⟶ ringTest K N) :
    basisAt φ hn (s ≫ ringTestMap K σ.toAlgHom) =
      Matrix.GeneralLinearGroup.map (sectionScalars s) (galoisConjugator φ hn σ) * basisAt φ hn s := by
  simp only [basisAt, SpecialLinearInnerForm.pointScalars_comp_ringTestMap,
    galoisConjugator_eq_basis, _root_.map_mul, _root_.map_inv, inv_mul_cancel_right]
  rfl

private theorem localIso_galois (hn : 2 ≤ n) (σ : N ≃ₐ[K] N)
    {V : Over (Spec (CommRingCat.of K))} (s : V ⟶ ringTest K N) (x : V ⟶ (descendedGroup φ hn).X) :
    (localIso_descendedGroup φ hn).toFun (s ≫ ringTestMap K σ.toAlgHom) x =
      (galoisTwist φ σ).toFun s ((localIso_descendedGroup φ hn).toFun s x) := by
  apply pointMatrix_injective
  apply Units.ext
  change (pointMatrix K V ((localIso_descendedGroup φ hn).toFun (s ≫ ringTestMap K σ.toAlgHom) x)).val =
    splitMatrix ((galoisTwist φ σ).toFun s ((localIso_descendedGroup φ hn).toFun s x))
  rw [pointMatrix_localIso, basisAt_galois, splitMatrix_localAutomorphism hn]
  simp only [splitMatrix, pointMatrix_localIso, MulAut.conj_apply, mul_inv_rev, Units.val_mul,
    Matrix.mul_assoc]
  rfl

private def compareLocalIso (hn : 2 ≤ n) : LocalGroupIso H (descendedGroup φ hn) (ringTest K N) where
  toFun s := (φ.toFun s).trans ((localIso_descendedGroup φ hn).toFun s).symm
  naturality b s x := by
    change ((localIso_descendedGroup φ hn).toFun (b ≫ s)).symm (φ.toFun (b ≫ s) (b ≫ x)) = _
    rw [φ.naturality]
    exact (localIso_descendedGroup φ hn).symm.naturality b s _

private theorem compareLocalIso_independent (hn : 2 ≤ n) : (compareLocalIso φ hn).IsIndependent := by
  apply LocalGroupIso.isIndependent_of_galois
  intro σ V s x
  let χ := localIso_descendedGroup φ hn
  change (χ.toFun s).symm (φ.toFun s x) =
    (χ.toFun (s ≫ ringTestMap K σ.toAlgHom)).symm (φ.toFun (s ≫ ringTestMap K σ.toAlgHom) x)
  rw [MulEquiv.eq_symm_apply, localIso_galois φ hn, MulEquiv.apply_symm_apply, galoisTwist_toFun,
    MulEquiv.symm_apply_apply]

/-- The original group is isomorphic to the full actual norm-one isometry group
of the descended scalar quadratic form. -/
def descendedGroupIso (hn : 2 ≤ n) : H ≅ descendedGroup φ hn := by
  obtain ⟨hsurj, hflat, hqc⟩ := fieldExtension_fpqc K N
  have : Surjective (ringTest K N).hom := hsurj
  have : Flat (ringTest K N).hom := hflat
  have : QuasiCompact (ringTest K N).hom := hqc
  exact (compareLocalIso φ hn).descend (compareLocalIso_independent φ hn)

end Langlands.GroupScheme.OddOrthogonalForm
