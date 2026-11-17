import Langlands.AlgebraicGeometry.Picard.FiniteLocallyFreeDeterminant
import Langlands.AlgebraicGeometry.Picard.DeterminantFrames

/-! # Fixed-index presentations of the actual finite locally free determinant -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.Picard.DeterminantFrames

open Langlands.Scheme.Modules

variable {X : Scheme.{u}} {M : X.Modules}
    {I J : Type u} [Fintype I] [Fintype J] {U : X.Opens}

/-- Reindex an actual free sheaf frame along an equivalence of finite indices. -/
def relabelFrame
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (r : J ≃ I) :
    SheafOfModules.free (R := X.ringCatSheaf.over U) J ≅ M.over U :=
  (SheafOfModules.freeFunctor (R := X.ringCatSheaf.over U)).mapIso r.toIso ≪≫ e

theorem relabelFrame_basis
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (r : J ≃ I) (W : Over U) (j : J) :
    localSectionBasis (relabelFrame e r) W j = localSectionBasis e W (r j) := by
  simp only [localSectionBasis_apply, localBasisSection, relabelFrame,
    Iso.trans_hom, Functor.mapIso_hom, SheafOfModules.freeFunctor_map,
    SheafOfModules.freeHomEquiv_comp_apply]
  change (SheafOfModules.sectionsMap e.hom
    ((SheafOfModules.free (R := X.ringCatSheaf.over U) I).freeHomEquiv
      (SheafOfModules.freeMap (r : J → I)) j)).val (op W) = _
  rw [SheafOfModules.freeHomEquiv_freeMap, SheafOfModules.freeHomEquiv_apply]
  rfl

variable {ι : Type u} {T : ι → X.Opens}
    (e : ∀ i, SheafOfModules.free (R := X.ringCatSheaf.over (T i)) I ≅ M.over (T i))
    (hT : (⨆ i, T i) = ⊤)

local instance fixedPresentationIndexDecidableEq : DecidableEq I := Classical.decEq I

/-- Normalize fixed finite-index frames to the indices used by the actual
variable-rank determinant construction. -/
def normalizedFrames : FiniteLocalFrames M where
  I := ι
  opens := T
  covers := hT
  rank _ := Fintype.card I
  frame i := relabelFrame (e i) (Equiv.ulift.trans (Fintype.equivFin I).symm)

private theorem normalizedFrames_basis (i : ι) {W : X.Opens} (h : W ≤ T i) :
    VariableDeterminantFrames.basis (normalizedFrames e hT).frame i h =
      (localSectionBasis (e i) (Over.mk (homOfLE h))).reindex (Fintype.equivFin I) := by
  change (localSectionBasis
    (relabelFrame (e i) (Equiv.ulift.trans (Fintype.equivFin I).symm))
    (Over.mk (homOfLE h))).reindex Equiv.ulift = _
  apply DFunLike.ext
  intro j
  calc
    _ = localSectionBasis
        (relabelFrame (e i) (Equiv.ulift.trans (Fintype.equivFin I).symm))
        (Over.mk (homOfLE h)) (Equiv.ulift.symm j) :=
      Module.Basis.reindex_apply _ _ j
    _ = localSectionBasis (e i) (Over.mk (homOfLE h)) ((Fintype.equivFin I).symm j) :=
      relabelFrame_basis (e i) _ _ _
    _ = _ := (Module.Basis.reindex_apply _ _ j).symm

theorem normalizedFrames_cocycle :
    VariableDeterminantFrames.cocycle (normalizedFrames e hT).frame = cocycle e := by
  let f : ∀ i : ι, SheafOfModules.free (R := X.ringCatSheaf.over (T i))
      (ULift.{u} (Fin (Fintype.card I))) ≅ M.over (T i) :=
    (normalizedFrames e hT).frame
  change VariableDeterminantFrames.cocycle f = cocycle e
  funext i j
  apply Units.ext
  let a : Module.Basis (Fin (Fintype.card I)) Γ(X, T i ⊓ T j) Γ(M, T i ⊓ T j) :=
    VariableDeterminantFrames.basis (normalizedFrames e hT).frame i inf_le_left
  let b : Module.Basis (Fin (Fintype.card I)) Γ(X, T i ⊓ T j) Γ(M, T i ⊓ T j) :=
    VariableDeterminantFrames.basis (normalizedFrames e hT).frame j inf_le_right
  change (Langlands.LinearAlgebra.FiniteBasisDeterminant.unit a b).val =
    (matrix e i j inf_le_left inf_le_right).det
  rw [Langlands.LinearAlgebra.FiniteBasisDeterminant.unit_same,
    Langlands.LinearAlgebra.FiniteBasisDeterminant.sameUnit_val]
  dsimp only [a, b]
  rw [normalizedFrames_basis, normalizedFrames_basis]
  let bi : Module.Basis I Γ(X, T i ⊓ T j) Γ(M, T i ⊓ T j) :=
    localSectionBasis (e i) (Over.mk (homOfLE inf_le_left))
  let bj : Module.Basis I Γ(X, T i ⊓ T j) Γ(M, T i ⊓ T j) :=
    localSectionBasis (e j) (Over.mk (homOfLE inf_le_right))
  change ((bi.reindex (Fintype.equivFin I)).toMatrix
    (bj.reindex (Fintype.equivFin I))).det = (bi.toMatrix bj).det
  have hm : (bi.reindex (Fintype.equivFin I)).toMatrix (bj.reindex (Fintype.equivFin I)) =
      (bi.toMatrix bj).submatrix (Fintype.equivFin I).symm (Fintype.equivFin I).symm := by
    ext a b
    simp only [Module.Basis.toMatrix_apply, Module.Basis.repr_reindex_apply,
      Module.Basis.reindex_apply, Matrix.submatrix_apply]
  rw [hm, Matrix.det_submatrix_equiv_self]

/-- Fixed finite-index determinant frames give a presentation of the existing
actual finite locally free determinant line. -/
def finiteDeterminantPresentationIso (hM : HasFiniteLocalBasis M) :
    lineBundle e hT ≅ finiteLocallyFreeDeterminant hM := by
  let E : lineBundle e hT ≅ (normalizedFrames e hT).lineBundle :=
    ObjectProperty.isoMk _ (eqToIso
      (show (lineBundle e hT).obj = (normalizedFrames e hT).lineBundle.obj from
        congrArg CocycleGluing.glued (normalizedFrames_cocycle e hT).symm))
  exact E ≪≫ finiteLocallyFreeDeterminantPresentationIso (normalizedFrames e hT) hM

end Langlands.AlgebraicGeometry.Picard.DeterminantFrames
