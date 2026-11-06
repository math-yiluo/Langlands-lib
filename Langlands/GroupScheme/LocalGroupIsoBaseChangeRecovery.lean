import Langlands.GroupScheme.LocalGroupIso
import Langlands.AbelianScheme.KernelBaseChange

/-! # Recovering a base-change isomorphism from natural local isomorphisms -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LocalGroupIso

variable {S : Scheme.{u}} {G H : GroupScheme S} {U : Over S}

/-- A test over the cover has a canonical cover point after forgetting to the base. -/
def baseChangeTestPoint (T : Over U.left) : (Over.map U.hom).obj T ⟶ U :=
  Over.homMk T.hom rfl

@[simp] theorem map_comp_baseChangeTestPoint {T T' : Over U.left} (t : T' ⟶ T) :
    (Over.map U.hom).map t ≫ baseChangeTestPoint T = baseChangeTestPoint T' := by
  apply Over.OverMorphism.ext
  exact Over.w t

variable (e : LocalGroupIso G H U)

/-- The local family acts on pullback points at every test over the cover. -/
def baseChangePoints (T : Over U.left) :
    (T ⟶ ((baseChange U.hom).obj G).X) ≃*
      (T ⟶ ((baseChange U.hom).obj H).X) :=
  (baseChangePointsEquiv U.hom G T).trans
    ((e.toFun (baseChangeTestPoint T)).trans (baseChangePointsEquiv U.hom H T).symm)

@[simp] theorem baseChangePoints_project (T : Over U.left)
    (x : T ⟶ ((baseChange U.hom).obj G).X) :
    baseChangePointsEquiv U.hom H T (e.baseChangePoints T x) =
      e.toFun (baseChangeTestPoint T) (baseChangePointsEquiv U.hom G T x) :=
  (baseChangePointsEquiv U.hom H T).apply_symm_apply _

/-- The recovered equivalences commute with all maps of tests over the cover. -/
theorem baseChangePoints_naturality {T T' : Over U.left} (t : T' ⟶ T)
    (x : T ⟶ ((baseChange U.hom).obj G).X) :
    e.baseChangePoints T' (t ≫ x) = t ≫ e.baseChangePoints T x := by
  apply (baseChangePointsEquiv U.hom H T').injective
  change baseChangePointsEquiv U.hom H T'
      ((baseChangePointsEquiv U.hom H T').symm
        (e.toFun (baseChangeTestPoint T')
          (baseChangePointsEquiv U.hom G T' (t ≫ x)))) =
    baseChangePointsEquiv U.hom H T' (t ≫ e.baseChangePoints T x)
  rw [MulEquiv.apply_symm_apply, baseChangePointsEquiv_naturality,
    baseChangePointsEquiv_naturality, baseChangePoints_project,
    ← e.naturality, map_comp_baseChangeTestPoint]

/-- Yoneda recovers an actual base-change isomorphism from the natural local family. -/
def toBaseChangeIso : (baseChange U.hom).obj G ≅ (baseChange U.hom).obj H :=
  isoOfPoints e.baseChangePoints e.baseChangePoints_naturality

/-- The recovered isomorphism has exactly the original local effect on projected points. -/
theorem toBaseChangeIso_hom_points (T : Over U.left)
    (x : T ⟶ ((baseChange U.hom).obj G).X) :
    baseChangePointsEquiv U.hom H T (x ≫ e.toBaseChangeIso.hom.hom.hom) =
      e.toFun (baseChangeTestPoint T) (baseChangePointsEquiv U.hom G T x) := by
  rw [toBaseChangeIso, comp_isoOfPoints_hom]
  exact (baseChangePointsEquiv U.hom H T).apply_symm_apply _

/-- The inverse has the inverse local effect on every test over the cover. -/
theorem toBaseChangeIso_inv_points (T : Over U.left)
    (y : T ⟶ ((baseChange U.hom).obj H).X) :
    baseChangePointsEquiv U.hom G T (y ≫ e.toBaseChangeIso.inv.hom.hom) =
      (e.toFun (baseChangeTestPoint T)).symm (baseChangePointsEquiv U.hom H T y) := by
  rw [toBaseChangeIso, comp_isoOfPoints_inv]
  change baseChangePointsEquiv U.hom G T
      ((baseChangePointsEquiv U.hom G T).symm
        ((e.toFun (baseChangeTestPoint T)).symm
          (baseChangePointsEquiv U.hom H T y))) = _
  exact (baseChangePointsEquiv U.hom G T).apply_symm_apply _

/-- The original local values determine the recovered actual isomorphism uniquely. -/
theorem toBaseChangeIso_unique
    (f : (baseChange U.hom).obj G ≅ (baseChange U.hom).obj H)
    (hf : ∀ (T : Over U.left) (x : T ⟶ ((baseChange U.hom).obj G).X),
      baseChangePointsEquiv U.hom H T (x ≫ f.hom.hom.hom) =
        e.toFun (baseChangeTestPoint T) (baseChangePointsEquiv U.hom G T x)) :
    f = e.toBaseChangeIso := by
  apply Iso.ext
  apply hom_ext_points
  intro T x
  apply (baseChangePointsEquiv U.hom H T).injective
  exact (hf T x).trans (e.toBaseChangeIso_hom_points T x).symm

end Langlands.GroupScheme.LocalGroupIso
