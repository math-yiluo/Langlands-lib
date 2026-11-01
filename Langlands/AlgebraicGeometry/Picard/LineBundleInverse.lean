import Langlands.AlgebraicGeometry.Picard.Basic
import Langlands.AlgebraicGeometry.Picard.LocalComparisonProof
import Langlands.AlgebraicGeometry.Picard.LineBundleTensor

/-! # Ordinary line-bundle inverses and Picard representatives -/

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry

universe u

namespace Langlands.AlgebraicGeometry.Picard

variable {X : Scheme.{u}}

/-- A tensor-invertible module sheaf is an actual locally free rank-one sheaf. -/
def InvertibleSheaf.toLineBundle (L : InvertibleSheaf X) : LineBundle X :=
  ⟨L.obj, (locallyFreeRankOneIffTensorInvertible X L.obj).mp L.property⟩

/-- A locally free rank-one sheaf is tensor-invertible. -/
def LineBundle.toInvertibleSheaf (L : LineBundle X) : InvertibleSheaf X :=
  ⟨L.obj, (locallyFreeRankOneIffTensorInvertible X L.obj).mpr L.property⟩

namespace LineBundle

/-- A chosen ordinary tensor inverse, with its proved local rank-one property. -/
def inverse (L : LineBundle X) : LineBundle X :=
  L.toInvertibleSheaf.inverse.toLineBundle

/-- Evaluation against the chosen inverse, for the explicit sheaf tensor. -/
def tensorInverseIso (L : LineBundle X) :
    Langlands.Scheme.Modules.tensorObj L.obj L.inverse.obj ≅
      SheafOfModules.unit X.ringCatSheaf :=
  (Langlands.Scheme.Modules.localizedTensorIso X L.obj L.inverse.obj).symm ≪≫
    L.toInvertibleSheaf.tensorInverseIso

/-- The class of an actual locally free rank-one sheaf in the scheme Picard group. -/
def classOf (L : LineBundle X) : Group X :=
  Picard.classOf X L.toInvertibleSheaf

lemma classOf_eq_iff (L M : LineBundle X) :
    L.classOf = M.classOf ↔ Nonempty (L.obj ≅ M.obj) :=
  Picard.classOf_eq_iff X L.toInvertibleSheaf M.toInvertibleSheaf

lemma classOf_eq_iff_iso (L M : LineBundle X) :
    L.classOf = M.classOf ↔ Nonempty (L ≅ M) := by
  rw [classOf_eq_iff]
  exact ⟨fun ⟨e⟩ => ⟨ObjectProperty.isoMk _ e⟩,
    fun ⟨e⟩ => ⟨(forget X).mapIso e⟩⟩

@[simp] lemma classOf_trivial (X : Scheme.{u}) :
    (trivial X).classOf = 0 :=
  Picard.classOf_trivial X

lemma classOf_tensor
    (preservation : Langlands.Scheme.Modules.pullbackTensorComparisonIsIsoStatement.{u})
    (L M : LineBundle X) :
    (tensor preservation L M).classOf = L.classOf + M.classOf := by
  calc
    (tensor preservation L M).classOf =
        Picard.classOf X (L.toInvertibleSheaf.tensor M.toInvertibleSheaf) :=
      (Picard.classOf_eq_iff X _ _).mpr
        ⟨(Langlands.Scheme.Modules.localizedTensorIso X L.obj M.obj).symm⟩
    _ = L.classOf + M.classOf :=
      Picard.classOf_tensor X L.toInvertibleSheaf M.toInvertibleSheaf

@[simp] lemma classOf_inverse (L : LineBundle X) :
    L.inverse.classOf = -L.classOf :=
  Picard.classOf_inverse X L.toInvertibleSheaf

end LineBundle

namespace Group

/-- A locally free rank-one representative of every Picard class. -/
def lineBundleRepresentative (X : Scheme.{u}) (x : Group X) : LineBundle X :=
  (representative X x).toLineBundle

@[simp] lemma classOf_lineBundleRepresentative (X : Scheme.{u}) (x : Group X) :
    (lineBundleRepresentative X x).classOf = x :=
  classOf_representative X x

/-- The Picard homomorphism agrees with actual line-bundle pullback. -/
lemma pullback_lineBundle_classOf {Y : Scheme.{u}} (f : X ⟶ Y) (L : LineBundle Y) :
    pullback f L.classOf = ((LineBundle.pullback f).obj L).classOf :=
  pullback_classOf f L.toInvertibleSheaf

end Group

end Langlands.AlgebraicGeometry.Picard
