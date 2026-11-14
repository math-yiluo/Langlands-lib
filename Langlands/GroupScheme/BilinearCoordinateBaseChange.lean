import Langlands.GroupScheme.BilinearCoordinateGroup
import Langlands.AbelianScheme.KernelBaseChange

/-! # Base change of bilinear coordinate groups and linear homomorphisms -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.BilinearCoordinate

namespace Coordinates

variable {I : Type u} [Fintype I] {S : Type u} [CommRing S]
  {c d : I → I → S}

/-- Identical bilinear coefficients give identical coordinate groups. -/
def coefficientEquiv (h : ∀ i j, c i j = d i j) : Coordinates c ≃* Coordinates d where
  toFun x := ⟨x.vec, x.scalar⟩
  invFun x := ⟨x.vec, x.scalar⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' x y := by
    apply Coordinates.ext
    · rfl
    · change x.scalar + y.scalar + form c x.vec y.vec =
        x.scalar + y.scalar + form d x.vec y.vec
      simp only [form, h]

end Coordinates

variable {R A : CommRingCat.{u}} (ρ : R ⟶ A) {I : Type u} [Fintype I]
  (c : I → I → R)

/-- The cocycle after the given change of base ring. -/
abbrev mappedCoefficients : I → I → A := fun i j => ρ.hom (c i j)

/-- The relative global-section algebra uses the composite coefficient map. -/
theorem algebraMap_baseChange (T : Over (Spec A)) (r : R) :
    algebraMap R (((algΓ R).obj ((Over.map (Spec.map ρ)).obj T)).unop) r =
      algebraMap A (((algΓ A).obj T).unop) (ρ.hom r) := by
  change ((Scheme.ΓSpecIso R).inv ≫ (T.hom ≫ Spec.map ρ).appTop) r =
    ((Scheme.ΓSpecIso A).inv ≫ T.hom.appTop) (ρ.hom r)
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- Natural bilinear coordinates on every test of the base-changed group. -/
def baseChangeCoordinates (T : Over (Spec A)) :
    (T ⟶ ((GroupScheme.baseChange (Spec.map ρ)).obj (groupScheme R c)).X) ≃*
      Coordinates (algebraCoefficients A (mappedCoefficients ρ c) ((algΓ A).obj T).unop) :=
  ((baseChangePointsEquiv (Spec.map ρ) (groupScheme R c) T).trans
    (pointsEquiv R c ((Over.map (Spec.map ρ)).obj T))).trans
    (Coordinates.coefficientEquiv (fun i j => algebraMap_baseChange ρ T (c i j)))

theorem baseChangeCoordinates_naturality {T T' : Over (Spec A)} (a : T' ⟶ T)
    (x : T ⟶ ((GroupScheme.baseChange (Spec.map ρ)).obj (groupScheme R c)).X) :
    baseChangeCoordinates ρ c T' (a ≫ x) =
      (functor A (mappedCoefficients ρ c)).map ((algΓ A).map a).unop
        (baseChangeCoordinates ρ c T x) := by
  simp only [baseChangeCoordinates, MulEquiv.trans_apply,
    baseChangePointsEquiv_naturality, pointsEquiv_naturality]
  apply Coordinates.ext <;> rfl

private def baseChangePointEquiv (T : Over (Spec A)) :
    (T ⟶ ((GroupScheme.baseChange (Spec.map ρ)).obj (groupScheme R c)).X) ≃*
      (T ⟶ (groupScheme A (mappedCoefficients ρ c)).X) :=
  (baseChangeCoordinates ρ c T).trans (pointsEquiv A (mappedCoefficients ρ c) T).symm

private theorem baseChangePointEquiv_naturality {T T' : Over (Spec A)} (a : T' ⟶ T)
    (x : T ⟶ ((GroupScheme.baseChange (Spec.map ρ)).obj (groupScheme R c)).X) :
    baseChangePointEquiv ρ c T' (a ≫ x) = a ≫ baseChangePointEquiv ρ c T x := by
  apply (pointsEquiv A (mappedCoefficients ρ c) T').injective
  simp only [baseChangePointEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
    pointsEquiv_naturality, baseChangeCoordinates_naturality]

/-- Base change is the actual bilinear group with the transported coefficients. -/
def baseChangeIso :
    (GroupScheme.baseChange (Spec.map ρ)).obj (groupScheme R c) ≅
      groupScheme A (mappedCoefficients ρ c) :=
  isoOfPoints (baseChangePointEquiv ρ c) (baseChangePointEquiv_naturality ρ c)

@[simp]
theorem pointsEquiv_baseChangeIso_hom (T : Over (Spec A))
    (x : T ⟶ ((GroupScheme.baseChange (Spec.map ρ)).obj (groupScheme R c)).X) :
    pointsEquiv A (mappedCoefficients ρ c) T (x ≫ (baseChangeIso ρ c).hom.hom.hom) =
      baseChangeCoordinates ρ c T x := by
  rw [baseChangeIso, comp_isoOfPoints_hom]
  exact (pointsEquiv A (mappedCoefficients ρ c) T).apply_symm_apply _

variable {c} {J : Type u} [Fintype J] {d : J → J → R}
  (M : I → J → R) (t : R) (h : IsCompatible c d M t)

/-- The actual linear coordinate map commutes with change of base. -/
theorem linearHom_baseChange :
    (baseChangeIso ρ c).hom ≫
        linearHom A (fun i j => ρ.hom (M i j)) (ρ.hom t) (h.map ρ.hom) =
      (GroupScheme.baseChange (Spec.map ρ)).map (linearHom R M t h) ≫
        (baseChangeIso ρ d).hom := by
  apply hom_ext_points
  intro T x
  apply (pointsEquiv A (mappedCoefficients ρ d) T).injective
  simp only [Grp.comp_hom_hom, ← Category.assoc, pointsEquiv_linearHom,
    pointsEquiv_baseChangeIso_hom]
  change Coordinates.linearMap
      (fun i j => algebraMap A _ (ρ.hom (M i j))) (algebraMap A _ (ρ.hom t)) _
      (baseChangeCoordinates ρ c T x) =
    baseChangeCoordinates ρ d T
      (x ≫ ((GroupScheme.baseChange (Spec.map ρ)).map (linearHom R M t h)).hom.hom)
  simp only [baseChangeCoordinates, MulEquiv.trans_apply,
    baseChangePointsEquiv_comp, pointsEquiv_linearHom]
  apply Coordinates.ext
  · funext j
    change (∑ i, _ * algebraMap A _ (ρ.hom (M i j))) =
      ∑ i, _ * algebraMap R _ (M i j)
    simp only [algebraMap_baseChange]
    rfl
  · change algebraMap A _ (ρ.hom t) * _ = algebraMap R _ t * _
    rw [algebraMap_baseChange]
    rfl

end Langlands.GroupScheme.BilinearCoordinate
