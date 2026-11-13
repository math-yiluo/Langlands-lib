import Langlands.GroupScheme.Rational.SteinbergRootMapUniqueness
import Langlands.GroupScheme.Rational.SteinbergModifiedRootProduct

/-! # Scalar comparison of arbitrary root parametrizations -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitPinning.RootParametrization

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {p : SplitPinning G} {α : p.rootIndex}
    (x y : p.RootParametrization α)

local notation "V" => VectorGroup.groupScheme (CommRingCat.of k) 1
local notation "coords" => VectorGroup.coordinates (CommRingCat.of k) 1
local notation "U" => Over.mk (𝟙 (Spec (CommRingCat.of k)))

/-- The comparison of two parametrizations of the same intrinsic root subgroup. -/
def comparisonIso : V ≅ V :=
  x.represents.isoOfIsRepresentedBy y.represents

/-- The comparison preserves the actual map to the ambient group. -/
theorem comparisonIso_hom_comp : (comparisonIso x y).hom ≫ y.hom = x.hom :=
  x.represents.isoOfIsRepresentedBy_hom_comp y.represents

/-- The torus law expressed as equivariance of the whole additive-group map. -/
theorem weightAction_comp (T : Over (Spec (CommRingCat.of k)))
    (t : T ⟶ p.torus.X) (v : T ⟶ (V).X) :
    (VectorGroup.weightAction (p.rootDatum.root α)).act t v ≫ x.hom.hom.hom =
      (t ≫ p.inclusion.hom.hom) * (v ≫ x.hom.hom.hom) *
        (t ≫ p.inclusion.hom.hom)⁻¹ := by
  have hw : (VectorGroup.weightAction (p.rootDatum.root α)).act t v =
      VectorGroup.scalarPoint (CommRingCat.of k) T
        (VectorGroup.charValue (p.rootDatum.root α) T t * (coords T v).toAdd 0) := by
    apply VectorGroup.points_ext
    intro j
    rw [VectorGroup.coordinates_weightAction_act, VectorGroup.coordinates_scalarPoint]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Subsingleton.elim j 0]
  rw [hw, ← x.torus_equivariant, VectorGroup.scalarPoint_coordinate]

/-- The comparison commutes with the action of the full split torus. -/
theorem comparisonIso_equivariant (T : Over (Spec (CommRingCat.of k)))
    (t : T ⟶ p.torus.X) (v : T ⟶ (V).X) :
    (VectorGroup.weightAction (p.rootDatum.root α)).act t v ≫
        (comparisonIso x y).hom.hom.hom =
      (VectorGroup.weightAction (p.rootDatum.root α)).act t
        (v ≫ (comparisonIso x y).hom.hom.hom) := by
  let : Mono y.hom.hom.hom := y.represents.1
  have hc (w : T ⟶ (V).X) :
      (w ≫ (comparisonIso x y).hom.hom.hom) ≫ y.hom.hom.hom =
        w ≫ x.hom.hom.hom := by
    rw [Category.assoc, ← Grp.comp_hom_hom, comparisonIso_hom_comp]
  apply (cancel_mono y.hom.hom.hom).mp
  rw [hc, x.weightAction_comp, y.weightAction_comp, hc]

/-- The comparison is scalar-linear on every scheme test. -/
theorem comparisonIso_coordinateLinear :
    RelativeRoot.IsCoordinateLinear coords (comparisonIso x y).hom :=
  RelativeRoot.isCoordinateLinear_of_weightCoordinates
    p.isSplitTorus (p.rootDatum.ne_zero α)
    (VectorGroup.isWeightVectorCoordinates_weightAction (n := 1) (p.rootDatum.root α))
    (comparisonIso_equivariant x y)

/-- Scalar linearity computes the comparison on every additive coordinate. -/
theorem comparisonIso_scalarPoint (T : Over (Spec (CommRingCat.of k)))
    (c : Γ(T.left, ⊤)) :
    VectorGroup.scalarPoint (CommRingCat.of k) T c ≫ (comparisonIso x y).hom.hom.hom =
      VectorGroup.scalarPoint (CommRingCat.of k) T
        (c * (coords T (VectorGroup.scalarPoint (CommRingCat.of k) T 1 ≫
          (comparisonIso x y).hom.hom.hom)).toAdd 0) := by
  have hs : RelativeRoot.coordinateSmul coords T c
      (VectorGroup.scalarPoint (CommRingCat.of k) T 1) =
        VectorGroup.scalarPoint (CommRingCat.of k) T c := by
    apply VectorGroup.points_ext
    intro j
    rw [RelativeRoot.coordinateSmul_coord]
    simp only [Pi.smul_apply, smul_eq_mul, VectorGroup.coordinates_scalarPoint, mul_one]
  have hlin := comparisonIso_coordinateLinear x y T c
    (VectorGroup.scalarPoint (CommRingCat.of k) T 1)
  rw [hs] at hlin
  apply VectorGroup.points_ext
  intro j
  rw [hlin, VectorGroup.coordinates_scalarPoint]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Subsingleton.elim j 0]

/-- The scalar of the comparison is defined intrinsically in the original field. -/
def comparisonScalar : k :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).hom
    ((coords U (VectorGroup.scalarPoint (CommRingCat.of k) U 1 ≫
      (comparisonIso x y).hom.hom.hom)).toAdd 0)

/-- Two supplied root parametrizations differ on rational points by this field scalar. -/
theorem rationalPoint_eq_comparisonScalar (c : k) :
    x.rationalPoint c = y.rationalPoint (c * comparisonScalar x y) := by
  let r := Scheme.ΓSpecIso (CommRingCat.of k)
  let s : Γ(Spec (CommRingCat.of k), ⊤) :=
    (coords U (VectorGroup.scalarPoint (CommRingCat.of k) U 1 ≫
      (comparisonIso x y).hom.hom.hom)).toAdd 0
  have hs : r.inv (c * comparisonScalar x y) =
      r.inv c * s := by
    change r.inv (c * r.hom s) = _
    rw [r.inv.hom.map_mul, r.hom_inv_id_apply]
  unfold rationalPoint point
  rw [← comparisonIso_hom_comp x y, Grp.comp_hom_hom, ← Category.assoc,
    comparisonIso_scalarPoint, ← hs]

/-- The scalar is nonzero because both parametrizations are injective. -/
theorem comparisonScalar_ne_zero : comparisonScalar x y ≠ 0 := by
  intro h
  have he := rationalPoint_eq_comparisonScalar x y 1
  rw [h, mul_zero] at he
  have hz : y.rationalPoint 0 = 1 := by simp [rationalPoint]
  rw [hz] at he
  exact x.rationalPoint_ne_one one_ne_zero he

end Langlands.GroupScheme.SplitPinning.RootParametrization
