import Langlands.AlgebraicGeometry.PointTopology.AffineChartWeilRestrictionCounit
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Intersection lifts and uniqueness for the glued Weil-restriction comparison -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R]
variable (Y : Over (Spec (CommRingCat.of R)))

/-- The actual intersection square of relative open subschemes over the base. -/
theorem relativeOpenIntersection_isPullback (U V : Y.left.Opens) :
    IsPullback (openOverHomOfLE R Y (inf_le_left : U ⊓ V ≤ U))
      (openOverHomOfLE R Y (inf_le_right : U ⊓ V ≤ V))
      (openOverι R Y U) (openOverι R Y V) := by
  apply IsPullback.of_map_of_faithful (Over.forget (Spec (CommRingCat.of R)))
  exact isPullback_opens_inf U V

/-- The actual lift of two relative open-subscheme morphisms with the same
composite in the ambient scheme. -/
def relativeOpenIntersectionLift {T : Over (Spec (CommRingCat.of R))}
    (U V : Y.left.Opens) (p : T ⟶ openOver R Y U) (q : T ⟶ openOver R Y V)
    (h : p ≫ openOverι R Y U = q ≫ openOverι R Y V) :
    T ⟶ openOver R Y (U ⊓ V) :=
  (relativeOpenIntersection_isPullback R Y U V).lift p q h

@[reassoc (attr := simp)]
theorem relativeOpenIntersectionLift_fst {T : Over (Spec (CommRingCat.of R))}
    (U V : Y.left.Opens) (p : T ⟶ openOver R Y U) (q : T ⟶ openOver R Y V)
    (h : p ≫ openOverι R Y U = q ≫ openOverι R Y V) :
    relativeOpenIntersectionLift R Y U V p q h ≫
        openOverHomOfLE R Y (inf_le_left : U ⊓ V ≤ U) = p :=
  (relativeOpenIntersection_isPullback R Y U V).lift_fst p q h

@[reassoc (attr := simp)]
theorem relativeOpenIntersectionLift_snd {T : Over (Spec (CommRingCat.of R))}
    (U V : Y.left.Opens) (p : T ⟶ openOver R Y U) (q : T ⟶ openOver R Y V)
    (h : p ≫ openOverι R Y U = q ≫ openOverι R Y V) :
    relativeOpenIntersectionLift R Y U V p q h ≫
        openOverHomOfLE R Y (inf_le_right : U ⊓ V ≤ V) = q :=
  (relativeOpenIntersection_isPullback R Y U V).lift_snd p q h

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]
variable (Y : Over (Spec (CommRingCat.of B))) [LocallyOfFiniteType Y.hom]

/-- The representing equivalence for an existing affine chart on any test scheme. -/
def affineWeilRestrictionTestEquiv
    (X : Over (Spec (CommRingCat.of B))) [IsAffine X.left]
    [LocallyOfFiniteType X.hom] (T : Over (Spec (CommRingCat.of A))) :
    (T ⟶ affineWeilRestriction A B X) ≃ (ringBaseChange A B T ⟶ X) :=
  Equiv.ofBijective (affineWeilRestrictionComparison A B X T)
    ⟨affineWeilRestrictionComparison_injective A B X T,
      affineWeilRestrictionComparison_surjective A B X T⟩

/-- The common affine-intersection lift of two chart morphisms whose
base-changed comparisons agree in the original scheme. -/
def affineChartWeilRestrictionIntersectionLift
    (T : Over (Spec (CommRingCat.of A))) (U V : Y.left.affineOpens)
    (hUV : IsAffineOpen (U.val ⊓ V.val))
    (p : T ⟶ affineWeilRestriction A B (openOver B Y U.val))
    (q : T ⟶ affineWeilRestriction A B (openOver B Y V.val))
    (h : affineWeilRestrictionComparison A B (openOver B Y U.val) T p ≫
        openOverι B Y U.val =
      affineWeilRestrictionComparison A B (openOver B Y V.val) T q ≫
        openOverι B Y V.val) :
    letI : IsAffine (openOver B Y (U.val ⊓ V.val)).left := hUV
    T ⟶ affineWeilRestriction A B (openOver B Y (U.val ⊓ V.val)) := by
  let : IsAffine (openOver B Y (U.val ⊓ V.val)).left := hUV
  exact (affineWeilRestrictionTestEquiv A B
    (openOver B Y (U.val ⊓ V.val)) T).symm
      (relativeOpenIntersectionLift B Y U.val V.val
        (affineWeilRestrictionComparison A B (openOver B Y U.val) T p)
        (affineWeilRestrictionComparison A B (openOver B Y V.val) T q) h)

@[reassoc (attr := simp)]
theorem affineChartWeilRestrictionIntersectionLift_fst
    (T : Over (Spec (CommRingCat.of A))) (U V : Y.left.affineOpens)
    (hUV : IsAffineOpen (U.val ⊓ V.val))
    (p : T ⟶ affineWeilRestriction A B (openOver B Y U.val))
    (q : T ⟶ affineWeilRestriction A B (openOver B Y V.val))
    (h : affineWeilRestrictionComparison A B (openOver B Y U.val) T p ≫
        openOverι B Y U.val =
      affineWeilRestrictionComparison A B (openOver B Y V.val) T q ≫
        openOverι B Y V.val) :
    letI : IsAffine (openOver B Y (U.val ⊓ V.val)).left := hUV
    affineChartWeilRestrictionIntersectionLift A B Y T U V hUV p q h ≫
        affineWeilRestrictionMap A B
          (openOverHomOfLE B Y (inf_le_left : U.val ⊓ V.val ≤ U.val)) = p := by
  let : IsAffine (openOver B Y (U.val ⊓ V.val)).left := hUV
  apply affineWeilRestrictionComparison_injective A B (openOver B Y U.val) T
  rw [affineWeilRestrictionComparison_postcomp]
  change affineWeilRestrictionTestEquiv A B (openOver B Y (U.val ⊓ V.val)) T
      ((affineWeilRestrictionTestEquiv A B (openOver B Y (U.val ⊓ V.val)) T).symm _) ≫
        openOverHomOfLE B Y (inf_le_left : U.val ⊓ V.val ≤ U.val) = _
  rw [Equiv.apply_symm_apply, relativeOpenIntersectionLift_fst]

@[reassoc (attr := simp)]
theorem affineChartWeilRestrictionIntersectionLift_snd
    (T : Over (Spec (CommRingCat.of A))) (U V : Y.left.affineOpens)
    (hUV : IsAffineOpen (U.val ⊓ V.val))
    (p : T ⟶ affineWeilRestriction A B (openOver B Y U.val))
    (q : T ⟶ affineWeilRestriction A B (openOver B Y V.val))
    (h : affineWeilRestrictionComparison A B (openOver B Y U.val) T p ≫
        openOverι B Y U.val =
      affineWeilRestrictionComparison A B (openOver B Y V.val) T q ≫
        openOverι B Y V.val) :
    letI : IsAffine (openOver B Y (U.val ⊓ V.val)).left := hUV
    affineChartWeilRestrictionIntersectionLift A B Y T U V hUV p q h ≫
        affineWeilRestrictionMap A B
          (openOverHomOfLE B Y (inf_le_right : U.val ⊓ V.val ≤ V.val)) = q := by
  let : IsAffine (openOver B Y (U.val ⊓ V.val)).left := hUV
  apply affineWeilRestrictionComparison_injective A B (openOver B Y V.val) T
  rw [affineWeilRestrictionComparison_postcomp]
  change affineWeilRestrictionTestEquiv A B (openOver B Y (U.val ⊓ V.val)) T
      ((affineWeilRestrictionTestEquiv A B (openOver B Y (U.val ⊓ V.val)) T).symm _) ≫
        openOverHomOfLE B Y (inf_le_right : U.val ⊓ V.val ≤ V.val) = _
  rw [Equiv.apply_symm_apply, relativeOpenIntersectionLift_snd]

/-- Compatible chart morphisms have exactly the same composite in the actual
glued scheme whenever their intersection is affine. -/
theorem affineChartWeilRestriction_chart_eq
    (T : Over (Spec (CommRingCat.of A))) (U V : Y.left.affineOpens)
    (hUV : IsAffineOpen (U.val ⊓ V.val))
    (p : T ⟶ affineWeilRestriction A B (openOver B Y U.val))
    (q : T ⟶ affineWeilRestriction A B (openOver B Y V.val))
    (h : affineWeilRestrictionComparison A B (openOver B Y U.val) T p ≫
        openOverι B Y U.val =
      affineWeilRestrictionComparison A B (openOver B Y V.val) T q ≫
        openOverι B Y V.val) :
    p ≫ affineChartWeilRestrictionι A B Y U =
      q ≫ affineChartWeilRestrictionι A B Y V := by
  let W : Y.left.affineOpens := ⟨U.val ⊓ V.val, hUV⟩
  let : IsAffine (openOver B Y (U.val ⊓ V.val)).left := hUV
  let r := affineChartWeilRestrictionIntersectionLift A B Y T U V hUV p q h
  calc
    p ≫ affineChartWeilRestrictionι A B Y U =
        (r ≫ affineWeilRestrictionMap A B
          (openOverHomOfLE B Y (inf_le_left : W.val ≤ U.val))) ≫
          affineChartWeilRestrictionι A B Y U :=
      congrArg (fun f => f ≫ affineChartWeilRestrictionι A B Y U)
        (affineChartWeilRestrictionIntersectionLift_fst A B Y T U V hUV p q h).symm
    _ = r ≫ affineChartWeilRestrictionι A B Y W := by
      rw [Category.assoc,
        affineChartWeilRestrictionι_naturality A B Y (show W ≤ U from (inf_le_left : U.val ⊓ V.val ≤ U.val))]
    _ = (r ≫ affineWeilRestrictionMap A B
          (openOverHomOfLE B Y (inf_le_right : W.val ≤ V.val))) ≫
          affineChartWeilRestrictionι A B Y V := by
      rw [Category.assoc,
        affineChartWeilRestrictionι_naturality A B Y (show W ≤ V from (inf_le_right : U.val ⊓ V.val ≤ V.val))]
    _ = q ≫ affineChartWeilRestrictionι A B Y V :=
      congrArg (fun f => f ≫ affineChartWeilRestrictionι A B Y V)
        (affineChartWeilRestrictionIntersectionLift_snd A B Y T U V hUV p q h)

/-- The actual pullback of the glued chart cover to a test scheme. -/
def affineChartWeilRestrictionTestCover
    (T : Over (Spec (CommRingCat.of A))) (p : T ⟶ affineChartWeilRestriction A B Y) :
    T.left.OpenCover :=
  (affineChartWeilRestrictionOpenCover A B Y).pullback₁ p.left

/-- A component of the pulled-back test cover, over the original base. -/
def affineChartWeilRestrictionTestChart
    (T : Over (Spec (CommRingCat.of A))) (p : T ⟶ affineChartWeilRestriction A B Y)
    (U : Y.left.affineOpens) : Over (Spec (CommRingCat.of A)) :=
  Over.mk ((affineChartWeilRestrictionTestCover A B Y T p).f U ≫ T.hom)

/-- The actual cover map of a test-chart component, over the base. -/
def affineChartWeilRestrictionTestChartι
    (T : Over (Spec (CommRingCat.of A))) (p : T ⟶ affineChartWeilRestriction A B Y)
    (U : Y.left.affineOpens) :
    affineChartWeilRestrictionTestChart A B Y T p U ⟶ T :=
  Over.homMk ((affineChartWeilRestrictionTestCover A B Y T p).f U)

/-- The actual morphism from a pulled-back test chart to its affine
Weil-restriction chart. -/
def affineChartWeilRestrictionTestChartMap
    (T : Over (Spec (CommRingCat.of A))) (p : T ⟶ affineChartWeilRestriction A B Y)
    (U : Y.left.affineOpens) :
    affineChartWeilRestrictionTestChart A B Y T p U ⟶
      affineWeilRestriction A B (openOver B Y U.val) :=
  Over.homMk (pullback.snd p.left (affineChartWeilRestrictionι A B Y U).left) (by
    change pullback.snd _ _ ≫ _ = pullback.fst _ _ ≫ T.hom
    rw [← Over.w p, ← Category.assoc, pullback.condition, Category.assoc, Over.w])

@[simp]
theorem affineChartWeilRestrictionTestChartMap_fac
    (T : Over (Spec (CommRingCat.of A))) (p : T ⟶ affineChartWeilRestriction A B Y)
    (U : Y.left.affineOpens) :
    affineChartWeilRestrictionTestChartMap A B Y T p U ≫
        affineChartWeilRestrictionι A B Y U =
      affineChartWeilRestrictionTestChartι A B Y T p U ≫ p := by
  apply Over.OverMorphism.ext
  exact pullback.condition.symm

/-- The actual global comparison is injective on every test scheme if affine
opens of the target have affine intersections. -/
theorem affineChartWeilRestrictionComparison_injective_of_affineIntersections
    (hinter : ∀ U V : Y.left.affineOpens, IsAffineOpen (U.val ⊓ V.val))
    (T : Over (Spec (CommRingCat.of A))) :
    Function.Injective (affineChartWeilRestrictionComparison A B Y T) := by
  intro p q h
  apply Over.OverMorphism.ext
  apply (affineChartWeilRestrictionTestCover A B Y T p).hom_ext
  intro U
  let S := affineChartWeilRestrictionTestChart A B Y T p U
  let j : S ⟶ T := affineChartWeilRestrictionTestChartι A B Y T p U
  let pU : S ⟶ affineWeilRestriction A B (openOver B Y U.val) :=
    affineChartWeilRestrictionTestChartMap A B Y T p U
  have hp : pU ≫ affineChartWeilRestrictionι A B Y U = j ≫ p :=
    affineChartWeilRestrictionTestChartMap_fac A B Y T p U
  have hj : j ≫ p = j ≫ q := by
    apply Over.OverMorphism.ext
    apply (affineChartWeilRestrictionTestCover A B Y S (j ≫ q)).hom_ext
    intro V
    let R := affineChartWeilRestrictionTestChart A B Y S (j ≫ q) V
    let k : R ⟶ S := affineChartWeilRestrictionTestChartι A B Y S (j ≫ q) V
    let qV : R ⟶ affineWeilRestriction A B (openOver B Y V.val) :=
      affineChartWeilRestrictionTestChartMap A B Y S (j ≫ q) V
    have hq : qV ≫ affineChartWeilRestrictionι A B Y V = k ≫ (j ≫ q) :=
      affineChartWeilRestrictionTestChartMap_fac A B Y S (j ≫ q) V
    have hc :
        affineWeilRestrictionComparison A B (openOver B Y U.val) R (k ≫ pU) ≫
            openOverι B Y U.val =
          affineWeilRestrictionComparison A B (openOver B Y V.val) R qV ≫
            openOverι B Y V.val := by
      calc
        _ = affineChartWeilRestrictionComparison A B Y R
            ((k ≫ pU) ≫ affineChartWeilRestrictionι A B Y U) :=
          (affineChartWeilRestrictionComparison_chart A B Y R U (k ≫ pU)).symm
        _ = affineChartWeilRestrictionComparison A B Y R ((k ≫ j) ≫ p) := by
          rw [Category.assoc, hp, ← Category.assoc]
        _ = affineChartWeilRestrictionComparison A B Y R ((k ≫ j) ≫ q) := by
          rw [affineChartWeilRestrictionComparison_natural,
            affineChartWeilRestrictionComparison_natural, h]
        _ = affineChartWeilRestrictionComparison A B Y R
            (qV ≫ affineChartWeilRestrictionι A B Y V) := by
          rw [hq, Category.assoc]
        _ = _ := affineChartWeilRestrictionComparison_chart A B Y R V qV
    have he := affineChartWeilRestriction_chart_eq A B Y R U V (hinter U V)
      (k ≫ pU) qV hc
    have hk : k ≫ (j ≫ p) = k ≫ (j ≫ q) := by
      calc
        _ = (k ≫ pU) ≫ affineChartWeilRestrictionι A B Y U := by
          rw [Category.assoc, hp]
        _ = qV ≫ affineChartWeilRestrictionι A B Y V := he
        _ = _ := hq
    exact congrArg (fun f => f.left) hk
  exact congrArg (fun f => f.left) hj

/-- For a separated target over `Spec B`, the constructed global comparison
is injective on every actual test scheme. -/
theorem affineChartWeilRestrictionComparison_injective [IsSeparated Y.hom]
    (T : Over (Spec (CommRingCat.of A))) :
    Function.Injective (affineChartWeilRestrictionComparison A B Y T) := by
  let : Y.left.IsSeparated := ⟨by
    rw [← terminal.comp_from Y.hom]
    infer_instance⟩
  exact affineChartWeilRestrictionComparison_injective_of_affineIntersections A B Y
    (fun U V => U.property.inf V.property) T

end Langlands.AlgebraicGeometry.PointTopology
