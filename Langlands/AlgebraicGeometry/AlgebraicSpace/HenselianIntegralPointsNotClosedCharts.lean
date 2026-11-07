import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianIntegralPointsOpenProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartTopology
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeTopologyFamily
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.Topology.Algebra.Polynomial

/-!
# Charts and affine-line points for the counterexamples to Corollary 5.7 closedness

Helpers shared by the two counterexamples to the closedness assertion of Conrad's
Corollary 5.7: points of the affine line over a ring with a given coordinate, the
continuity of the coordinate parametrization of the `K`-points of the affine line over `O`,
and the base change to `Spec K` of an étale chart over `Spec O` as an étale chart of finite
type of the generic fibre.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Topology Polynomial
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
  (RingPoint ringTest ringTestMap schemePointTopology schemePointTopology_eq_affine
    ringBaseChange ringPointBaseChangeEquiv affineRingPointEquiv spectrumAlgebraPointHomeomorph
    AlgPoint)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace HenselianIntegralPointsNotClosed

section AffineLine

variable (R : Type u) [CommRing R]

set_option backward.isDefEq.respectTransparency false in
instance : LocallyOfFiniteType (ringTest R R[X]).hom :=
  (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    (RingHom.finiteType_algebraMap.mpr inferInstance)

instance : QuasiCompact (ringTest R R[X]).hom := by
  change QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap R R[X])))
  infer_instance

/-- The point with coordinate `s` of the affine line over `R`. -/
def linePoint {T : Type u} [CommRing T] [Algebra R T] (s : T) : RingPoint R (ringTest R R[X]) T :=
  ringTestMap R (aeval s)

variable {R}

/-- The algebra maps out of `R[X]` are the points of the affine line. -/
theorem affineRingPointEquiv_ringTestMap {T : Type u} [CommRing T] [Algebra R T]
    (φ : R[X] →ₐ[R] T) : affineRingPointEquiv R R[X] T (ringTestMap R φ) = φ := by
  apply AlgHom.coe_ringHom_injective
  change (Spec.preimage (Spec.map (CommRingCat.ofHom φ.toRingHom))).hom = φ.toRingHom
  rw [Spec.preimage_map]
  rfl

/-- Every point of the affine line is the point of its coordinate. -/
theorem eq_linePoint {T : Type u} [CommRing T] [Algebra R T] (a : RingPoint R (ringTest R R[X]) T) :
    a = linePoint R (affineRingPointEquiv R R[X] T a X) := by
  apply (affineRingPointEquiv R R[X] T).injective
  rw [linePoint, affineRingPointEquiv_ringTestMap]
  apply Polynomial.algHom_ext
  rw [aeval_X]

end AffineLine

section BaseChangeChart

variable {O : Type u} [CommRing O] (K : Type u) [NontriviallyNormedField K] [Algebra O K]
  {X : AlgebraicSpace (Spec (CommRingCat.of O))}

/-- The base change to `Spec K` of an étale chart of finite type over `Spec O`. -/
abbrev baseChangeChart (U : Over (Spec (CommRingCat.of O))) [LocallyOfFiniteType U.hom]
    [QuasiCompact U.hom] (f : (schemeToSpace _).obj U ⟶ X) (hf : IsEtale (hom f)) :
    EtaleFiniteTypeChart K (baseChange (Spec.algebraMap O K) X) where
  scheme := ringBaseChange O K U
  hom := homMk (restrictAtlas (Spec.algebraMap O K) (hom f))
  isEtale := by
    have : MorphismProperty.RespectsIso (@Etale.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    have h := hf
    unfold IsEtale at h ⊢
    exact relative_restrictAtlas (g := Spec.algebraMap O K) (@Etale.{u}) h
  locallyOfFiniteType := by
    change LocallyOfFiniteType (pullback.snd U.hom (Spec.algebraMap O K))
    infer_instance
  quasiCompact := by
    change QuasiCompact (pullback.snd U.hom (Spec.algebraMap O K))
    infer_instance

/-- The chart map of the base-changed chart, read on `K`-valued points of `X`. -/
theorem baseChangeRingPointsEquiv_baseChangeChart_pointMap (U : Over (Spec (CommRingCat.of O)))
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] (f : (schemeToSpace _).obj U ⟶ X)
    (hf : IsEtale (hom f)) (q : RingPoint K (ringBaseChange O K U) K) :
    baseChangeRingPointsEquiv O K K X ((baseChangeChart K U f hf).pointMap q) =
      RingPoints.map f ((schemeRingPointsEquiv O U K).symm
        ((ringPointBaseChangeEquiv O K K U).symm q)) :=
  HenselianIntegralPointsOpen.baseChangeRingPointsEquiv_schemePointsMap f q

end BaseChangeChart

/-- The points of the affine line over `O` depend continuously on the coordinate. -/
theorem continuous_linePoint {O : Type u} [CommRing O] (K : Type u)
    [NontriviallyNormedField K] [Algebra O K] :
    Continuous[_, schemePointTopology O (ringTest O O[X]) K] (fun s : K => linePoint O s) := by
  rw [schemePointTopology_eq_affine]
  rw [← (spectrumAlgebraPointHomeomorph O K O[X]).comp_continuous_iff, AlgPoint.continuous_iff]
  intro q
  change Continuous fun s : K => affineRingPointEquiv O O[X] K (ringTestMap O (aeval s)) q
  simp only [affineRingPointEquiv_ringTestMap]
  exact Polynomial.continuous_aeval q

end HenselianIntegralPointsNotClosed

end Langlands.AlgebraicGeometry.AlgebraicSpace
