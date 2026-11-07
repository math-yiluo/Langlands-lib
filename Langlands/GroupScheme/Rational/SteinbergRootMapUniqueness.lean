import Langlands.GroupScheme.Rational.SteinbergRootProduct
import Langlands.GroupScheme.Rational.RootSubgroupAutomorphismRigidity

/-! # Uniqueness of the supplied normalized simple-root parametrizations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace VectorGroup

variable {R : CommRingCat.{u}}

/-- A point of the standard additive group is recovered from its single coordinate. -/
theorem scalarPoint_coordinate (T : Over (Spec R))
    (v : T ⟶ (groupScheme R 1).X) :
    scalarPoint R T ((coordinates R 1 T v).toAdd 0) = v := by
  apply points_ext
  intro j
  rw [coordinates_scalarPoint]
  exact congrArg (fun i => (coordinates R 1 T v).toAdd i) (Subsingleton.elim 0 j)

end VectorGroup

namespace SplitPinning.NormalizedRootParametrization

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {p : SplitPinning G} {a : p.base.support}
    (x y : p.NormalizedRootParametrization a)

local notation "V" => VectorGroup.groupScheme (CommRingCat.of k) 1
local notation "coords" => VectorGroup.coordinates (CommRingCat.of k) 1

local instance : IsAffineHom (VectorGroup.groupScheme (CommRingCat.of k) 1).X.hom :=
  VectorGroup.isAffineHom_groupScheme (CommRingCat.of k) 1

/-- The comparison between two parametrizations of the same whole root subgroup. -/
def comparisonIso : V ≅ V :=
  x.represents.isoOfIsRepresentedBy y.represents

/-- The comparison preserves the actual map to the ambient group. -/
theorem comparisonIso_hom_comp : (comparisonIso x y).hom ≫ y.hom = x.hom :=
  x.represents.isoOfIsRepresentedBy_hom_comp y.represents

/-- The supplied torus law is equivariance of the actual additive-group map. -/
theorem weightAction_comp (T : Over (Spec (CommRingCat.of k)))
    (t : T ⟶ p.torus.X) (v : T ⟶ (V).X) :
    (VectorGroup.weightAction (p.rootDatum.root a)).act t v ≫ x.hom.hom.hom =
      (t ≫ p.inclusion.hom.hom) * (v ≫ x.hom.hom.hom) *
        (t ≫ p.inclusion.hom.hom)⁻¹ := by
  have hw : (VectorGroup.weightAction (p.rootDatum.root a)).act t v =
      VectorGroup.scalarPoint (CommRingCat.of k) T
        (VectorGroup.charValue (p.rootDatum.root a) T t * (coords T v).toAdd 0) := by
    apply VectorGroup.points_ext
    intro j
    rw [VectorGroup.coordinates_weightAction_act, VectorGroup.coordinates_scalarPoint]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Subsingleton.elim j 0]
  rw [hw, ← x.torus_equivariant]
  rw [VectorGroup.scalarPoint_coordinate]

/-- The comparison commutes with the weight action of the full split torus. -/
theorem comparisonIso_equivariant (T : Over (Spec (CommRingCat.of k)))
    (t : T ⟶ p.torus.X) (v : T ⟶ (V).X) :
    (VectorGroup.weightAction (p.rootDatum.root a)).act t v ≫
        (comparisonIso x y).hom.hom.hom =
      (VectorGroup.weightAction (p.rootDatum.root a)).act t
        (v ≫ (comparisonIso x y).hom.hom.hom) := by
  let : Mono y.hom.hom.hom := y.represents.1
  have hc (w : T ⟶ (V).X) :
      (w ≫ (comparisonIso x y).hom.hom.hom) ≫ y.hom.hom.hom =
        w ≫ x.hom.hom.hom := by
    rw [Category.assoc, ← Grp.comp_hom_hom, comparisonIso_hom_comp]
  apply (cancel_mono y.hom.hom.hom).mp
  rw [hc, x.weightAction_comp, y.weightAction_comp, hc]

/-- The standard epsilon vector spans the actual Lie algebra of the additive line. -/
private theorem exists_smul_standardEpsilon
    (z : Additive (lieKernel V (CommRingCat.of k))) :
    ∃ c : k, c • VectorGroup.standardEpsilon k = z := by
  let E := RelativeRoot.vectorLieCoordinates coords VectorGroup.isNaturalVectorCoordinates
    (CommAlgCat.of k k)
  have he : E (VectorGroup.standardEpsilon k) = fun _ => 1 := by
    change E (E.symm (fun _ => 1)) = _
    exact E.apply_symm_apply _
  refine ⟨E z 0, E.injective ?_⟩
  rw [map_smul, he]
  funext j
  simp only [Pi.smul_apply, smul_eq_mul, mul_one]
  exact congrArg (E z) (Subsingleton.elim 0 j)

/-- Pinning normalization makes the comparison differential the identity. -/
theorem comparisonIso_targetMap_eq_self
    (z : Additive (lieKernel V (CommRingCat.of k))) :
    Lie.targetMapLinear (comparisonIso x y).hom (CommRingCat.of k) z = z := by
  let : Mono y.hom.hom.hom := y.represents.1
  have he : Lie.targetMapLinear (comparisonIso x y).hom (CommRingCat.of k)
      (VectorGroup.standardEpsilon k) = VectorGroup.standardEpsilon k := by
    apply Lie.targetMapLinear_injective y.hom (CommRingCat.of k)
    have hc : Lie.targetMapLinear y.hom (CommRingCat.of k)
        (Lie.targetMapLinear (comparisonIso x y).hom (CommRingCat.of k)
          (VectorGroup.standardEpsilon k)) =
        Lie.targetMapLinear x.hom (CommRingCat.of k) (VectorGroup.standardEpsilon k) := by
      apply Additive.toMul.injective
      apply Subtype.ext
      simp only [lieKernelTargetLinear_val, Category.assoc, ← Grp.comp_hom_hom,
        comparisonIso_hom_comp]
    rw [hc, x.derivative, y.derivative]
  obtain ⟨c, rfl⟩ := exists_smul_standardEpsilon z
  rw [map_smul, he]

/-- Two supplied normalized parametrizations of one simple root have the same homomorphism. -/
theorem hom_eq : x.hom = y.hom := by
  have hlin := RelativeRoot.isCoordinateLinear_of_weightCoordinates
    (q := comparisonIso x y) p.isSplitTorus (p.rootDatum.ne_zero a)
    (VectorGroup.isWeightVectorCoordinates_weightAction (n := 1) (p.rootDatum.root a))
    (comparisonIso_equivariant x y)
  have hid : (comparisonIso x y).hom = 𝟙 V :=
    RelativeRoot.eq_id_of_coordinateLinear_of_targetMapLinear_eq_self
      VectorGroup.isNaturalVectorCoordinates hlin (comparisonIso_targetMap_eq_self x y)
  have hc := comparisonIso_hom_comp x y
  rw [hid, Category.id_comp] at hc
  exact hc.symm

/-- A normalized simple-root parametrization is unique for the fixed pinning. -/
instance : Subsingleton (p.NormalizedRootParametrization a) where
  allEq x y := by
    cases x with
    | mk x xr xc xe xd =>
      cases y with
      | mk y yr yc ye yd =>
        have h : x = y := hom_eq ⟨x, xr, xc, xe, xd⟩ ⟨y, yr, yc, ye, yd⟩
        cases h
        rfl

end SplitPinning.NormalizedRootParametrization

namespace SplitPinning

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {p : SplitPinning G}

/-- The full normalized simple-root family is unique whenever it exists. -/
instance : Subsingleton p.NormalizedSimpleRootParametrizations :=
  inferInstanceAs (Subsingleton (∀ a : p.base.support, p.NormalizedRootParametrization a))

/-- The actual ordered Steinberg morphism is independent of the supplied normalized root maps. -/
theorem steinbergProduct_eq_of_normalizedRootMaps {r : ℕ}
    (e : Fin r ≃ p.base.support) (x y : p.NormalizedSimpleRootParametrizations)
    (n : p.SimpleReflectionRepresentatives) :
    steinbergProduct e x n = steinbergProduct e y n := by
  rw [Subsingleton.elim x y]

end SplitPinning

end Langlands.GroupScheme
