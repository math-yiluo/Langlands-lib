import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

set_option maxHeartbeats 800000

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry
open scoped CategoryTheory.MonObj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

namespace Langlands.GroupScheme
universe u
variable {S : Scheme.{u}} {G H : Grp (Over S)}

/-- The target unit as a homomorphism from the trivial group scheme. -/
def kernelUnit (H : Grp (Over S)) : Grp.trivial (Over S) ⟶ H :=
  Grp.homMk η[H.X]

/-- The group-scheme kernel, constructed as a pullback with the unit. -/
def kernel (f : G ⟶ H) : Grp (Over S) := pullback f (kernelUnit H)

/-- The canonical inclusion into the source group scheme. -/
def kernelι (f : G ⟶ H) : kernel f ⟶ G := pullback.fst f (kernelUnit H)

/-- Forgetting the group structure gives the kernel pullback square. -/
lemma kernel_isPullback (f : G ⟶ H) :
    IsPullback (kernelι f).hom.hom (toUnit (kernel f).X) f.hom.hom η[H.X] := by
  have h := IsPullback.map (Grp.forget (Over S)) (IsPullback.of_hasPullback f (kernelUnit H))
  have e : (Grp.forget (Over S)).map (pullback.snd f (kernelUnit H)) =
      toUnit (kernel f).X := toUnit_unique _ _
  rw [e] at h
  change IsPullback (kernelι f).hom.hom (toUnit (kernel f).X) f.hom.hom η[H.X] at h
  exact h

instance kernelι_mono (f : G ⟶ H) : Mono (kernelι f).hom.hom :=
  (kernel_isPullback f).mono_fst_of_mono

/-- The canonical multiplicative equivalence on points. -/
def kernelPointsEquiv (f : G ⟶ H) (T : Over S) :
    (T ⟶ (kernel f).X) ≃* (((yonedaGrp.map f).app (.op T)).hom.ker) where
  toFun x := ⟨x ≫ (kernelι f).hom.hom, by
    change (x ≫ (kernelι f).hom.hom) ≫ f.hom.hom = 1
    rw [Category.assoc, (kernel_isPullback f).w]
    change x ≫ toUnit (kernel f).X ≫ η[H.X] = toUnit T ≫ η[H.X]
    rw [← Category.assoc, comp_toUnit]⟩
  invFun x := (kernel_isPullback f).lift x.val (toUnit T) x.property
  left_inv x := by
    apply (cancel_mono (kernelι f).hom.hom).mp
    exact (kernel_isPullback f).lift_fst _ _ _
  right_inv x := by
    apply Subtype.ext
    exact (kernel_isPullback f).lift_fst _ _ _
  map_mul' x y := by
    apply Subtype.ext
    exact mul_comp x y (kernelι f).hom.hom

/-- The equivalence sends a kernel point to its image under the inclusion. -/
@[simp]
lemma kernelPointsEquiv_val (f : G ⟶ H) (T : Over S) (x : T ⟶ (kernel f).X) :
    (kernelPointsEquiv f T x).val = x ≫ (kernelι f).hom.hom := rfl

/-- Restriction of pointwise kernel elements along a map of test schemes. -/
def kernelPointsRestrict (f : G ⟶ H) {T T' : Over S} (a : T' ⟶ T) :
    (((yonedaGrp.map f).app (.op T)).hom.ker) →*
      (((yonedaGrp.map f).app (.op T')).hom.ker) where
  toFun x := ⟨a ≫ x.val, by
    change (a ≫ x.val) ≫ f.hom.hom = 1
    have hx : x.val ≫ f.hom.hom = 1 := x.property
    rw [Category.assoc, hx]
    exact comp_one a⟩
  map_one' := Subtype.ext (comp_one a)
  map_mul' x y := Subtype.ext (comp_mul a x.val y.val)

/-- The pointwise identification is natural in every test scheme. -/
lemma kernelPointsEquiv_naturality (f : G ⟶ H) {T T' : Over S} (a : T' ⟶ T)
    (x : T ⟶ (kernel f).X) :
    kernelPointsEquiv f T' (a ≫ x) =
      kernelPointsRestrict f a (kernelPointsEquiv f T x) :=
  Subtype.ext (Category.assoc _ _ _)

/-- A kernel of a homomorphism from a commutative group scheme is commutative. -/
instance kernel_isCommMonObj (f : G ⟶ H) [IsCommMonObj G.X] :
    IsCommMonObj (kernel f).X := by
  apply (isCommMonObj_iff_isMulCommutative _).mpr
  intro T
  refine ⟨⟨fun x y => ?_⟩⟩
  apply (cancel_mono (kernelι f).hom.hom).mp
  rw [mul_comp, mul_comp, mul_comm]

/-- The kernel square is a fibre-product square of actual schemes. -/
lemma kernel_isPullback_scheme (f : G ⟶ H) :
    IsPullback (kernelι f).hom.hom.left (kernel f).X.hom
      f.hom.hom.left η[H.X].left :=
  IsPullback.map (Over.forget S) (kernel_isPullback f)

/-- With separated target the kernel inclusion is a closed immersion. -/
instance kernelι_isClosedImmersion (f : G ⟶ H) [IsSeparated H.X.hom] :
    IsClosedImmersion (kernelι f).hom.hom.left := by
  have he : η[H.X].left ≫ H.X.hom = 𝟙 S := η[H.X].w
  have : IsClosedImmersion (η[H.X].left ≫ H.X.hom) :=
    he.symm ▸ (inferInstance : IsClosedImmersion (𝟙 S))
  have : IsClosedImmersion η[H.X].left := .of_comp _ H.X.hom
  exact MorphismProperty.of_isPullback (kernel_isPullback_scheme f).flip inferInstance

end Langlands.GroupScheme
