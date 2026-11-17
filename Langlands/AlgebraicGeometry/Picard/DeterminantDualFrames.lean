import Langlands.AlgebraicGeometry.Picard.DeterminantFixedPresentation
import Langlands.AlgebraicGeometry.Picard.CocycleLineBundlePower
import Langlands.AlgebraicGeometry.Picard.LineBundleDualPullback

/-! # Actual determinant duality from finite free frames -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules

variable {X : Scheme.{u}}

/-- Every supplied tensor inverse of an actual line is isomorphic to its
actual internal dual. -/
def tensorInverseDualIso (L : LineBundle X) (N : X.Modules)
    (p : tensorObj L.obj N ≅ structureSheaf X) : N ≅ dual L.obj := by
  let ev : tensorObj (dual L.obj) L.obj ≅ structureSheaf X :=
    tensorComm (dual L.obj) L.obj ≪≫
      @asIso _ _ _ _ (dualTensorEval L.obj) (isIso_dualTensorEval L.property)
  exact (tensorLeftUnitor N).symm ≪≫
    (tensorFunctor X).mapIso (ev.symm.prod (Iso.refl N)) ≪≫
    tensorAssociator (dual L.obj) L.obj N ≪≫
    (tensorFunctor X).mapIso ((Iso.refl (dual L.obj)).prod p) ≪≫
    tensorRightUnitor (dual L.obj)

namespace DeterminantFrames

variable {M : X.Modules} {I : Type u} [Fintype I] {U : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)

local instance dualFrameIndexDecidableEq : DecidableEq I := Classical.decEq I

private theorem dualFrame_basis (W : Over U) (i : I) :
    localSectionBasis (dualLocalFreeIso e) W i =
      LocalHom.restrict W.hom (localBasisCoordinate e i) := by
  rw [localSectionBasis_apply]
  change (((dual M).over U).freeHomEquiv (dualLocalFreeIso e).hom i).val (op W) = _
  rw [SheafOfModules.freeHomEquiv_apply]
  exact dualLocalFreeIso_basis e i W

private theorem dualFrame_eval (W : Over U) (i j : I) :
    dualEval M W.left (localSectionBasis (dualLocalFreeIso e) W i)
      (localSectionBasis e W j) = if j = i then 1 else 0 := by
  classical
  rw [dualFrame_basis, localSectionBasis_apply]
  change LocalHom.app (LocalHom.restrict W.hom (localBasisCoordinate e i))
    (𝟙 W.left) ((localBasisSection e j).val (op W)) = _
  rw [LocalHom.restrict_app, Category.id_comp]
  exact localBasisCoordinate_basis e i j W

private theorem dualFrame_repr (W : Over U) (φ : Γ(dual M, W.left)) (i : I) :
    (localSectionBasis (dualLocalFreeIso e) W).repr φ i =
      dualEval M W.left φ (localSectionBasis e W i) := by
  classical
  let b : Module.Basis I Γ(X, W.left) Γ(dual M, W.left) :=
    localSectionBasis (dualLocalFreeIso e) W
  let f : Γ(dual M, W.left) →ₗ[Γ(X, W.left)] Γ(X, W.left) :=
    (Finsupp.lapply i).comp b.repr.toLinearMap
  let g : Γ(dual M, W.left) →ₗ[Γ(X, W.left)] Γ(X, W.left) :=
    (dualEval M W.left).flip (localSectionBasis e W i)
  have hfg : f = g := by
    apply b.ext
    intro j
    change b.repr (b j) i = dualEval M W.left (b j) (localSectionBasis e W i)
    rw [Module.Basis.repr_self, dualFrame_eval]
    simp only [Finsupp.single_apply, eq_comm]
  exact LinearMap.congr_fun hfg φ

variable {ι : Type u} {T : ι → X.Opens}
    (e : ∀ i, SheafOfModules.free (R := X.ringCatSheaf.over (T i)) I ≅ M.over (T i))

/-- Dualize every actual frame without changing its index type or open. -/
def dualFrames :
    ∀ i, SheafOfModules.free (R := X.ringCatSheaf.over (T i)) I ≅ (dual M).over (T i) :=
  fun i => dualLocalFreeIso (e i)

theorem dualFrames_matrix (i j : ι) {W : X.Opens} (hi : W ≤ T i) (hj : W ≤ T j) :
    matrix (dualFrames e) i j hi hj = (matrix e j i hj hi).transpose := by
  ext k l
  rw [matrix, Module.Basis.toMatrix_apply]
  change (localSectionBasis (dualLocalFreeIso (e i)) (Over.mk (homOfLE hi))).repr
      (localSectionBasis (dualLocalFreeIso (e j)) (Over.mk (homOfLE hj)) l) k = _
  rw [dualFrame_repr, dualFrame_basis]
  change LocalHom.app
      (LocalHom.restrict (homOfLE hj) (localBasisCoordinate (e j) l)) (𝟙 W)
        (localSectionBasis (e i) (Over.mk (homOfLE hi)) k) = _
  rw [LocalHom.restrict_app]
  rfl

theorem dualFrames_unit (i j : ι) {W : X.Opens} (hi : W ≤ T i) (hj : W ≤ T j) :
    unit (dualFrames e) i j hi hj = (unit e i j hi hj)⁻¹ := by
  apply Units.ext
  change (matrix (dualFrames e) i j hi hj).det = (matrix e j i hj hi).det
  rw [dualFrames_matrix, Matrix.det_transpose]

theorem dualFrames_cocycle : cocycle (dualFrames e) = (cocycle e)⁻¹ := by
  funext i j
  exact dualFrames_unit e i j inf_le_left inf_le_right

variable (hT : (⨆ i, T i) = ⊤)

/-- The actual two frame determinant lines are tensor inverses. -/
def dualFramesTensorIso :
    tensorObj (lineBundle e hT).obj (lineBundle (dualFrames e) hT).obj ≅ structureSheaf X := by
  have hp : cocycle e * cocycle (dualFrames e) = 1 := by
    rw [dualFrames_cocycle, mul_inv_cancel]
  exact CocycleGluing.tensorIso (isCocycle e) (isCocycle (dualFrames e)) hT ≪≫
    eqToIso (congrArg CocycleGluing.glued hp) ≪≫ (CocycleGluing.oneIso hT).symm

/-- On a fixed-index frame cover, the existing actual determinant of a module
is isomorphic to the dual of the existing actual determinant of its dual. -/
def finiteDeterminantDualIsoOfFrames
    (hM : HasFiniteLocalBasis M) (hD : HasFiniteLocalBasis (dual M)) :
    finiteLocallyFreeDeterminant hM ≅ (finiteLocallyFreeDeterminant hD).dual := by
  let E := tensorInverseDualIso (lineBundle (dualFrames e) hT) (lineBundle e hT).obj
    (tensorComm _ _ ≪≫ dualFramesTensorIso e hT)
  exact (finiteDeterminantPresentationIso e hT hM).symm ≪≫
    ObjectProperty.isoMk _ E ≪≫
    LineBundle.dualIso (finiteDeterminantPresentationIso (dualFrames e) hT hD)

end DeterminantFrames

end Langlands.AlgebraicGeometry.Picard
