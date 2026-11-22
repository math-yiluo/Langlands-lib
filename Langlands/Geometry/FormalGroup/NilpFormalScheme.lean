import Langlands.Geometry.FormalGroup.AdicAffineNilpPoints
import Langlands.Geometry.FormalGroup.DeligneNilpFunctor
import Langlands.Geometry.FormalGroup.PrimalAtlasPadicHeight

/-! # Formal-scheme presentations on affine Nilp tests -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory _root_.AlgebraicGeometry

namespace Langlands.FormalGroup.Nilp

variable {R : Type u} [CommRing R] {π : R}
variable (B : Nilp.{u, u} R π)

/-- Restriction from the first principal open to the product overlap. -/
def toLocalizationOverlapLeft (a b : B.obj) :
    B.localizationAway a ⟶ B.localizationAway (a * b) :=
  ObjectProperty.homMk (CommAlgCat.ofHom
    { __ := IsLocalization.Away.awayToAwayRight
        (S := Localization.Away a) (P := Localization.Away (a * b)) a b
      commutes' r := by
        change IsLocalization.Away.awayToAwayRight
            (S := Localization.Away a) (P := Localization.Away (a * b)) a b
            (algebraMap R (Localization.Away a) r) =
          algebraMap R (Localization.Away (a * b)) r
        rw [IsScalarTower.algebraMap_apply R B.obj (Localization.Away a),
          IsLocalization.Away.awayToAwayRight_eq,
          IsScalarTower.algebraMap_apply R B.obj (Localization.Away (a * b))] })

/-- Restriction from the second principal open to the same product overlap. -/
def toLocalizationOverlapRight (a b : B.obj) :
    B.localizationAway b ⟶ B.localizationAway (a * b) :=
  ObjectProperty.homMk (CommAlgCat.ofHom
    { __ := IsLocalization.Away.awayToAwayLeft
        (S := Localization.Away b) (P := Localization.Away (a * b)) b a
      commutes' r := by
        change IsLocalization.Away.awayToAwayLeft
            (S := Localization.Away b) (P := Localization.Away (a * b)) b a
            (algebraMap R (Localization.Away b) r) =
          algebraMap R (Localization.Away (a * b)) r
        rw [IsScalarTower.algebraMap_apply R B.obj (Localization.Away b),
          IsLocalization.Away.awayToAwayLeft_eq,
          IsScalarTower.algebraMap_apply R B.obj (Localization.Away (a * b))] })

/-- The Zariski gluing condition for principal covers of affine Nilp tests. -/
def IsZariskiLocal (F : Nilp.{u, u} R π ⥤ Type v) : Prop :=
  ∀ (B : Nilp.{u, u} R π) (s : Set B.obj), Ideal.span s = ⊤ →
    ∀ x : (a : s) → F.obj (B.localizationAway a.val),
      (∀ a b : s, F.map (B.toLocalizationOverlapLeft a.val b.val) (x a) =
        F.map (B.toLocalizationOverlapRight a.val b.val) (x b)) →
      ∃! y : F.obj B, ∀ a : s, F.map (B.toLocalizationAway a.val) y = x a

variable {F G : Nilp.{u, u} R π ⥤ Type v}

/-- An inclusion whose image after pullback to each affine point is an open subscheme. -/
structure OpenOnAffineTests (α : F ⟶ G) where
  injective (B : Nilp.{u, u} R π) : Function.Injective (α.app B)
  image (B : Nilp.{u, u} R π) (y : G.obj B) : (Spec (CommRingCat.of B.obj)).Opens
  factors_iff {B B' : Nilp.{u, u} R π} (f : B ⟶ B') (y : G.obj B) :
    Set.range (DeligneFormalSpace.nilpSpecMap f) ⊆ (image B y : Set _) ↔
      ∃ x : F.obj B', α.app B' x = G.map f y

/-- A formal scheme on affine Nilp tests, exhibited by open affine formal charts. -/
structure FormalSchemePresentation (F : Nilp.{u, u} R π ⥤ Type (max u v)) where
  isZariskiLocal : IsZariskiLocal F
  Index : Type (max u v)
  chart : Index → AdicAffineChart π
  includeChart (i : Index) : (chart i).nilpPointsFunctor ⋙ uliftFunctor.{v, u} ⟶ F
  openChart (i : Index) : OpenOnAffineTests (includeChart i)
  covers (B : Nilp.{u, u} R π) (y : F.obj B) (x : Spec (CommRingCat.of B.obj)) :
    ∃ i : Index, x ∈ (openChart i).image B y

/-- Existence of an open affine formal-scheme presentation of the actual point functor. -/
def IsFormalScheme (F : Nilp.{u, u} R π ⥤ Type (max u v)) : Prop :=
  Nonempty (FormalSchemePresentation F)

end Langlands.FormalGroup.Nilp
