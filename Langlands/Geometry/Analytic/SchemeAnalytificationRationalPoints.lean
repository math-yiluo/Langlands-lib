import Langlands.Geometry.Analytic.SchemeAnalytificationSpace
import Langlands.Geometry.Analytic.AffineAnalytificationRationalPoints
import Langlands.AlgebraicGeometry.PointTopology.SchemePoints

/-! # Rational points of the glued analytification of a scheme -/

noncomputable section

universe u

namespace Langlands.Analytic.SchemeAnalytification

open CategoryTheory _root_.AlgebraicGeometry Topology
open Langlands.Analytic.AffineSchemeAnalytification Langlands.AlgebraicGeometry.PointTopology

section Algebraic

variable {K : Type u} [CommRing K]

/-- An affine scheme over `Spec K`, viewed as an object of the over category, still has
an affine underlying scheme. -/
instance isAffine_overMk_left {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of K))
    [IsAffine Y] : IsAffine (Over.mk g).left :=
  ‹IsAffine Y›

/-- On an affine scheme over `Spec K`, the scalar action on global sections used by
`AffineSchemeAnalytification` agrees with the one used by the point-topology Library. -/
theorem algebraMap_coordinateRing_eq {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of K))
    [IsAffine Y] (k : K) :
    algebraMap K (CoordinateRing g) k = algebraMap K (AffineCoordinateRing K (Over.mk g)) k := by
  have h1 : Spec.algebraMap K (CoordinateRing g) = Y.isoSpec.inv ≫ g :=
    (Iso.eq_inv_comp (coordinateIso g)).mpr (coordinateIso_hom_over g)
  have h2 : Spec.algebraMap K (AffineCoordinateRing K (Over.mk g)) = Y.isoSpec.inv ≫ g :=
    affineCoordinateSpecMap K (Over.mk g)
  have h := Spec.map_injective (h1.trans h2.symm)
  exact congrArg (fun φ => φ.hom k) h

/-- The identity of global sections, as a `K`-algebra equivalence between the
coordinate algebra of `AffineSchemeAnalytification` and that of the point-topology
Library. -/
def coordinateAlgEquiv {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of K)) [IsAffine Y] :
    CoordinateRing g ≃ₐ[K] AffineCoordinateRing K (Over.mk g) :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.refl Γ(Y, ⊤)) (algebraMap_coordinateRing_eq g)

@[simp] theorem coordinateAlgEquiv_apply {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of K))
    [IsAffine Y] (a : CoordinateRing g) :
    (coordinateAlgEquiv g a : Γ(Y, ⊤)) = (a : Γ(Y, ⊤)) := rfl

end Algebraic

section Normed

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f]

/-- The algebraic `K`-point of the global sections of an affine open defined by an
actual relative `K`-point of that open subscheme. -/
def affineAlgPoint (U : X.affineOpens) (q : RingPoint K (openOver K (Over.mk f) U.val) K) :
    AlgPoint K (CoordinateRing (structureMap f U)) K :=
  letI : IsAffine (openOver K (Over.mk f) U.val).left := U.property
  AlgPoint.precomp (coordinateAlgEquiv (structureMap f U)).toAlgHom
    (affineSchemePointEquiv K (openOver K (Over.mk f) U.val) K q)

/-- The point of the analytification of an affine open defined by an actual relative
`K`-point of that open subscheme. -/
def localAnalyticPoint (U : X.affineOpens)
    (q : RingPoint K (openOver K (Over.mk f) U.val) K) : LocalSpace K f U :=
  AffineAnalytification.analyticPoint K (chartPresentation K f U) (affineAlgPoint K f U q)

/-- A chosen affine open through which an actual `K`-point of `X` factors. -/
def pointAffine (p : RingPoint K (Over.mk f) K) : X.affineOpens :=
  Classical.choose (exists_affineOpenPoint K (Over.mk f) K p)

/-- The chosen factorization of an actual `K`-point through `pointAffine`. -/
def pointLift (p : RingPoint K (Over.mk f) K) :
    RingPoint K (openOver K (Over.mk f) (pointAffine K f p).val) K :=
  Classical.choose (Classical.choose_spec (exists_affineOpenPoint K (Over.mk f) K p))

omit [IsUltrametricDist K] [CompleteSpace K] [LocallyOfFiniteType f] in
/-- The chosen factorization recovers the given point. -/
theorem openPointMap_pointLift (p : RingPoint K (Over.mk f) K) :
    openPointMap K (Over.mk f) K (pointAffine K f p).val (pointLift K f p) = p :=
  Classical.choose_spec (Classical.choose_spec (exists_affineOpenPoint K (Over.mk f) K p))

/-- The point of the glued analytification defined by an actual `K`-point of `X`:
the analytic point of its factorization through a chosen affine open, sent into the
glued space. -/
def analyticRationalPoint (p : RingPoint K (Over.mk f) K) : Space K f :=
  ι K f (pointAffine K f p) (localAnalyticPoint K f (pointAffine K f p) (pointLift K f p))

theorem analyticRationalPoint_def (p : RingPoint K (Over.mk f) K) :
    analyticRationalPoint K f p =
      ι K f (pointAffine K f p) (localAnalyticPoint K f (pointAffine K f p) (pointLift K f p)) :=
  rfl

/-- The point of the glued space lies in the image of the chosen affine open. -/
theorem analyticRationalPoint_mem_range (p : RingPoint K (Over.mk f) K) :
    analyticRationalPoint K f p ∈ Set.range (ι K f (pointAffine K f p)) :=
  ⟨_, rfl⟩

end Normed

end Langlands.Analytic.SchemeAnalytification
