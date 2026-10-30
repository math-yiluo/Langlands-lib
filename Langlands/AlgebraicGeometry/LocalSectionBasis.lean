import Langlands.AlgebraicGeometry.ModuleDualLocalFree
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Actual bases and endomorphisms on sections of a finite free sheaf -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

namespace Langlands.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}} {U : X.Opens}
    {I : Type u} [Fintype I] {M : X.Modules}

local instance : DecidableEq I := Classical.decEq I

/-- Coordinates of actual module sections in a sheaf trivialization. -/
def localSectionCoordinates
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (V : Over U) : Γ(M, V.left) ≃ₗ[Γ(X, V.left)] (I → Γ(X, V.left)) where
  toFun x i := LocalHom.app (localBasisCoordinate e i) V.hom x
  map_add' x y := by ext i; exact map_add _ x y
  map_smul' r x := by ext i; exact (LocalHom.app (localBasisCoordinate e i) V.hom).hom.map_smul r x
  invFun c := ∑ i, c i • (show Γ(M, V.left) from (localBasisSection e i).val (op V))
  left_inv x := localBasis_expansion e V x
  right_inv c := by
    ext i
    change LocalHom.app (localBasisCoordinate e i) V.hom
      (∑ j, c j • (show Γ(M, V.left) from (localBasisSection e j).val (op V))) = c i
    simp only [map_sum]
    change (∑ j, (LocalHom.app (localBasisCoordinate e i) V.hom).hom
      (c j • (show Γ(M, V.left) from (localBasisSection e j).val (op V)))) = c i
    simp only [map_smul, localBasisCoordinate_basis]
    simp

/-- A genuine finite basis of sections on every smaller open of a trivialization. -/
def localSectionBasis
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (V : Over U) : Module.Basis I Γ(X, V.left) Γ(M, V.left) :=
  Module.Basis.ofEquivFun (localSectionCoordinates e V)

@[simp]
lemma localSectionBasis_repr
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (V : Over U) (x : Γ(M, V.left)) (i : I) :
    (localSectionBasis e V).repr x i = LocalHom.app (localBasisCoordinate e i) V.hom x :=
  Module.Basis.ofEquivFun_repr_apply _ _ _

@[simp]
lemma localSectionBasis_apply
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (V : Over U) (i : I) :
    localSectionBasis e V i = (localBasisSection e i).val (op V) := by
  simp [localSectionBasis, Module.Basis.coe_ofEquivFun, localSectionCoordinates]

/-- Restricting the basis sections gives the basis on the smaller open. -/
lemma localSectionBasis_restrict
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    {V W : Over U} (j : V ⟶ W) (i : I) :
    M.presheaf.map j.left.op (localSectionBasis e W i) = localSectionBasis e V i := by
  simp only [localSectionBasis_apply]
  exact PresheafOfModules.sections_property (localBasisSection e i) j.op

/-- Coordinates commute with restriction of both sections and scalars. -/
lemma localSectionBasis_repr_restrict
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    {V W : Over U} (j : V ⟶ W) (x : Γ(M, W.left)) (i : I) :
    (localSectionBasis e V).repr (M.presheaf.map j.left.op x) i =
      X.presheaf.map j.left.op ((localSectionBasis e W).repr x i) := by
  simp only [localSectionBasis_repr]
  exact PresheafOfModules.naturality_apply (localBasisCoordinate e i).val j.op x

/-- Evaluate an actual sheaf endomorphism on sections of a smaller open. -/
def localSectionEndomorphism (M : X.Modules) (V : Over U) :
    End (M.over U) →+* Module.End Γ(X, V.left) Γ(M, V.left) where
  toFun f := (f.val.app (op V)).hom
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

@[simp]
lemma localSectionEndomorphism_apply (V : Over U) (f : End (M.over U))
    (x : Γ(M, V.left)) : localSectionEndomorphism M V f x = f.val.app (op V) x := rfl

/-- Restriction intertwines the section actions on actual sheaf sections. -/
lemma localSectionEndomorphism_restrict {V W : Over U} (j : V ⟶ W)
    (f : End (M.over U)) (x : Γ(M, W.left)) :
    localSectionEndomorphism M V f (M.presheaf.map j.left.op x) =
      M.presheaf.map j.left.op (localSectionEndomorphism M W f x) :=
  PresheafOfModules.naturality_apply f.val j.op x

/-- Matrices of the section endomorphism restrict entry by entry. -/
lemma localSectionEndomorphism_toMatrix_restrict
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    {V W : Over U} (j : V ⟶ W) (f : End (M.over U)) (i k : I) :
    LinearMap.toMatrix (localSectionBasis e V) (localSectionBasis e V)
        (localSectionEndomorphism M V f) i k =
      X.presheaf.map j.left.op
        (LinearMap.toMatrix (localSectionBasis e W) (localSectionBasis e W)
          (localSectionEndomorphism M W f) i k) := by
  simp only [LinearMap.toMatrix_apply]
  rw [← localSectionBasis_restrict e j k, localSectionEndomorphism_restrict,
    localSectionBasis_repr_restrict]

end Langlands.Scheme.Modules
