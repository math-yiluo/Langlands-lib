import Langlands.GroupScheme.RelativeLevi.ModuliSimpleTransitivity
import Langlands.GroupScheme.RelativeLevi.ModuliConjugation
import Langlands.GroupScheme.RelativeLevi.ParabolicBaseChange

/-! # Trivializing the actual Levi moduli at a supplied stable Levi -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.RelativeLevi

variable {S : Scheme.{u}} {G P U L : GroupScheme S} {M T : Over S}

/-- The point comparison used by the moduli target is an actual equivalence. -/
def pulledBackPointEquiv (P : GroupScheme S) (T : Over S) :
    (T ⟶ P.X) ≃ (Over.mk (𝟙 T.left) ⟶ ((baseChange T.hom).obj P).X) where
  toFun := pulledBackPoint P T
  invFun := baseChangeBasePointsEquiv T.hom P
  left_inv := baseChangeBasePointsEquiv_pulledBackPoint P T
  right_inv x := by
    apply (baseChangeBasePointsEquiv T.hom P).injective
    exact baseChangeBasePointsEquiv_pulledBackPoint P T _

/-- Pulling a point into the base-changed group commutes with a homomorphism. -/
theorem pulledBackPoint_comp (r : U ⟶ P) (g : T ⟶ U.X) :
    pulledBackPoint U T g ≫ ((baseChange T.hom).map r).hom.hom =
      pulledBackPoint P T (g ≫ r.hom.hom) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change (pullback.lift g.left (𝟙 T.left) _ ≫
      ((Over.pullback T.hom).map r.hom.hom).left) ≫ _ =
        pullback.lift (g.left ≫ r.hom.hom.left) (𝟙 T.left) _ ≫ _
    simp only [Over.pullback_map_left, Category.assoc, pullback.lift_fst,
      pullback.lift_fst_assoc]
  · exact (Over.w _).trans (Over.w _).symm

/-- Restricting the image of a literal pullback gives the direct pullback image. -/
theorem restrictImage_baseChange_range (l : L ⟶ P) (a : T ⟶ M) :
    restrictImage a (SubgroupFunctor.range ((baseChange M.hom).map l)) =
      SubgroupFunctor.range ((baseChange T.hom).map l) := by
  rw [restrictImage_range]
  change SubgroupFunctor.range
      ((baseChange a.left).map ((baseChange M.hom).map l) ≫
        (Descent.pullbackComparison M.hom a.left T.hom (Over.w a) P).hom) = _
  rw [Descent.pullbackComparison_naturality, SubgroupFunctor.range_iso_comp]

variable (i : P ⟶ G) (r : U ⟶ P) (l : L ⟶ P)
    (hG : IsReductive G) (hi : IsRelativeParabolicSubgroup i)
    (hU : ∀ {B : Scheme.{u}} (b : B ⟶ S),
      IsRelativeUnipotentRadical ((baseChange b).map r))
    (hL : ∀ {B : Scheme.{u}} (b : B ⟶ S),
      IsRelativeLeviSubgroup ((baseChange b).map l))

/-- On every test, a stable supplied Levi identifies radical points with
actual Levi images. -/
def stableLeviOrbitEquiv (T : Over S) :
    (T ⟶ U.X) ≃ LeviImage ((baseChange T.hom).obj P) :=
  (pulledBackPointEquiv U T).trans
    (LeviImage.conjugationEquiv ((baseChange T.hom).map i)
      ((baseChange T.hom).map r) (hG.baseChange T.hom)
      (hi.baseChange hG T.hom) (hU T.hom)
      (LeviImage.ofHom ((baseChange T.hom).map l) (hL T.hom)))

@[simp]
theorem stableLeviOrbitEquiv_val (T : Over S) (g : T ⟶ U.X) :
    (stableLeviOrbitEquiv i r l hG hi hU hL T g).val =
      conjugateAt P T (g ≫ r.hom.hom)
        (SubgroupFunctor.range ((baseChange T.hom).map l)) := by
  change conjugateImage
      (pulledBackPoint U T g ≫ ((baseChange T.hom).map r).hom.hom) _ = _
  rw [pulledBackPoint_comp]
  rfl

/-- The orbit correspondence respects the literal all-test restriction map. -/
theorem stableLeviOrbitEquiv_naturality (a : T ⟶ M) (g : M ⟶ U.X) :
    (stableLeviOrbitEquiv i r l hG hi hU hL T (a ≫ g)).val =
      restrictImage a (stableLeviOrbitEquiv i r l hG hi hU hL M g).val := by
  simp only [stableLeviOrbitEquiv_val, restrictImage_conjugateAt,
    restrictImage_baseChange_range, Category.assoc]

/-- A supplied Levi whose literal pullbacks remain Levi trivializes the actual
moduli scheme over the radical, assuming the same stability for that radical. -/
def moduliRepresentationOfStableLevi : ModuliRepresentation P U.X where
  pointsEquiv := stableLeviOrbitEquiv i r l hG hi hU hL
  naturality a g := stableLeviOrbitEquiv_naturality i r l hG hi hU hL a g

/-- The trivialization intertwines the radical's regular action and actual
conjugation, in the orientation fixed by the target. -/
theorem moduliRepresentationOfStableLevi_isEquivariant :
    letI : ModObj U.X U.X := .regular U.X
    (moduliRepresentationOfStableLevi i r l hG hi hU hL).IsEquivariant r := by
  let : ModObj U.X U.X := .regular U.X
  intro T g x
  apply LeviImage.ext
  change (stableLeviOrbitEquiv i r l hG hi hU hL T (g * x)).val =
    conjugateImage (pulledBackPoint P T (g ≫ r.hom.hom))
      (stableLeviOrbitEquiv i r l hG hi hU hL T x).val
  simp only [stableLeviOrbitEquiv_val, conjugateAt, MonObj.mul_comp]
  change conjugateImage (pulledBackPointHom P T
      ((g ≫ r.hom.hom) * (x ≫ r.hom.hom))) _ = _
  rw [map_mul, conjugateImage_mul]
  rfl

end Langlands.GroupScheme.RelativeLevi
