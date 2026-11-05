import Langlands.GroupScheme.Rational.PositiveTorusTriangularCoordinates
import Langlands.GroupScheme.Rational.TorusUnipotence.StandardUnipotentAction
import Langlands.GroupScheme.Rational.TorusUnipotence.PositiveWeightCoordinates
import Langlands.GroupScheme.Rational.TorusUnipotence.LieWeightMultiplicity
import Langlands.GroupScheme.GaloisPointDescent

/-! # Proof of the torus-weighted triangular coordinates

The chosen coordinate algebra `CharacterUnits.Coord H` of an affine group `H` and its ring of
global sections `AffineCoordinateRing k H.X` are identified compatibly with point evaluation.
Through this identification, the polynomial eigen-coordinates and the triangular group law of
`TorusUnipotence` on the standard unipotent subgroup `N`, together with the comparison of Lie
weights in `StandardUnipotentAction`, prove `PositiveTorusTriangularCoordinatesStatement`.
See the paired Markdown.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace CharacterUnits

variable {k : Type u} [Field k] (H : GroupScheme (Spec (CommRingCat.of k)))
  [IsAffineHom H.X.hom] [IsAffine H.X.left]

omit [IsAffineHom H.X.hom] in
/-- Global-section coordinates are natural in the coefficient algebra. -/
theorem coordinates_affinePointMap {A B : Type u} [CommRing A] [Algebra k A] [CommRing B]
    [Algebra k B] (f : A →ₐ[k] B) (x : H.affinePoints (CommAlgCat.of k A)) :
    GaloisPoint.coordinates k H B (H.affinePointMap (CommAlgCat.ofHom f) x) =
      f.comp (GaloisPoint.coordinates k H A x) := by
  ext a
  rw [GaloisPoint.coordinates_apply, AlgHom.comp_apply, GaloisPoint.coordinates_apply]
  exact H.affinePointEvaluation_map (CommAlgCat.ofHom f) x a

/-- The point of `H` with coefficients in its ring of global sections whose global-section
coordinates are the identity. -/
def sectionPoint : H.affinePoints (CommAlgCat.of k (AffineCoordinateRing k H.X)) :=
  (GaloisPoint.coordinates k H (AffineCoordinateRing k H.X)).symm (AlgHom.id k _)

omit [IsAffineHom H.X.hom] in
/-- Every point is obtained from `sectionPoint` by extending coefficients along its
global-section coordinates. -/
theorem affinePointMap_sectionPoint {A : Type u} [CommRing A] [Algebra k A]
    (x : H.affinePoints (CommAlgCat.of k A)) :
    H.affinePointMap (CommAlgCat.ofHom (GaloisPoint.coordinates k H A x)) (sectionPoint H) =
      x := by
  apply (GaloisPoint.coordinates k H A).injective
  rw [coordinates_affinePointMap, sectionPoint, Equiv.apply_symm_apply, AlgHom.comp_id]

/-- The chosen coordinate algebra mapped to global sections. -/
def coordToSections : Coord H →ₐ[k] AffineCoordinateRing k H.X :=
  Lie.pointCoordinates H (sectionPoint H)

/-- Global sections mapped to the chosen coordinate algebra. -/
def sectionsToCoord : AffineCoordinateRing k H.X →ₐ[k] Coord H :=
  GaloisPoint.coordinates k H (Coord H) (universalPoint H)

/-- Evaluating the global section attached to `c` at a point gives the coordinate `c` of that
point. -/
theorem affinePointEvaluation_coordToSections {A : Type u} [CommRing A] [Algebra k A]
    (x : H.affinePoints (CommAlgCat.of k A)) (c : Coord H) :
    H.affinePointEvaluation (CommAlgCat.of k A) x (coordToSections H c) =
      Lie.pointCoordinates H x c := by
  rw [← GaloisPoint.coordinates_apply]
  conv_rhs => rw [← affinePointMap_sectionPoint H x]
  change _ = Lie.pointCoordinates H
    (Lie.affineMap H (GaloisPoint.coordinates k H A x) (sectionPoint H)) c
  rw [Lie.pointCoordinates_naturality]
  rfl

/-- The coordinate attached to a global section `a` of a point is the value of `a` at that
point. -/
theorem pointCoordinates_sectionsToCoord {A : Type u} [CommRing A] [Algebra k A]
    (x : H.affinePoints (CommAlgCat.of k A)) (a : AffineCoordinateRing k H.X) :
    Lie.pointCoordinates H x (sectionsToCoord H a) =
      H.affinePointEvaluation (CommAlgCat.of k A) x a := by
  rw [← GaloisPoint.coordinates_apply]
  conv_rhs => rw [← affinePointMap_universalPoint H x]
  rw [coordinates_affinePointMap]
  rfl

theorem coordToSections_sectionsToCoord (a : AffineCoordinateRing k H.X) :
    coordToSections H (sectionsToCoord H a) = a := by
  have h := affinePointEvaluation_coordToSections H (sectionPoint H) (sectionsToCoord H a)
  rw [pointCoordinates_sectionsToCoord, ← GaloisPoint.coordinates_apply,
    ← GaloisPoint.coordinates_apply, sectionPoint, Equiv.apply_symm_apply] at h
  exact h

theorem sectionsToCoord_coordToSections (c : Coord H) :
    sectionsToCoord H (coordToSections H c) = c := by
  have h := pointCoordinates_sectionsToCoord H (universalPoint H) (coordToSections H c)
  have h2 := affinePointEvaluation_coordToSections H (universalPoint H) c
  have h3 : Lie.pointCoordinates H (universalPoint H) c = c := by
    rw [pointCoordinates_universalPoint]; rfl
  rw [pointCoordinates_universalPoint] at h
  exact h.trans (h2.trans h3)

/-- The chosen coordinate algebra is the ring of global sections, compatibly with evaluation
at points. -/
def coordSectionsEquiv : Coord H ≃ₐ[k] AffineCoordinateRing k H.X :=
  AlgEquiv.ofAlgHom (coordToSections H) (sectionsToCoord H)
    (AlgHom.ext (coordToSections_sectionsToCoord H))
    (AlgHom.ext (sectionsToCoord_coordToSections H))

@[simp] theorem coordSectionsEquiv_apply (c : Coord H) :
    coordSectionsEquiv H c = coordToSections H c := rfl

/-- `affinePointEvaluation_coordToSections` for a bundled coefficient algebra. -/
theorem affinePointEvaluation_coordToSections' (A : CommAlgCat.{u} k)
    (x : H.affinePoints A) (c : Coord H) :
    H.affinePointEvaluation A x (coordToSections H c) =
      Lie.pointCoordinates H (A := (A : Type u)) x c :=
  affinePointEvaluation_coordToSections H (A := (A : Type u)) x c

end CharacterUnits

open TorusUnipotence CharacterUnits in
/-- **Torus-weighted triangular coordinates on the standard unipotent subgroup.** For a
connected reductive group over a field of characteristic zero, a maximal split torus `i` and a
cocharacter `ν`, the standard unipotent subgroup `N = U(ν)` has triangular polynomial
coordinates that are `T`-eigenfunctions, with positive relative roots as weights and the Lie
algebra multiplicities. -/
theorem positiveTorusTriangularCoordinates : PositiveTorusTriangularCoordinatesStatement.{u} := by
  intro F _ _ G _ _ hG T i ν hi _
  have : IsAffine (Standard.unipotentScheme i ν ∅).X.left :=
    isAffine_of_isAffineHom (Standard.unipotentScheme i ν ∅).X.hom
  have : Smooth G.X.hom := hG.smooth
  have hT : IsSplitTorus T.toGrp := hi.1.1
  have : Smooth (Standard.unipotentScheme i ν ∅).X.hom :=
    Standard.smooth_unipotentScheme_empty i ν hT
  let b := Standard.unipotentAction i ν hT
  obtain ⟨d, w, t, ht, htw, hε, hw, hmono⟩ :=
    exists_positiveWeight_coordinates hT b ν
      (fun χ hχ => Standard.pairing_pos_of_mem_support i ν hT hχ)
  obtain ⟨P, hP, hmul⟩ := exists_triangular_mul hT b ν ht htw hε hw hmono
  refine ⟨d, fun k => coordToSections (Standard.unipotentScheme i ν ∅) (t k), P, w, ?_, hP, ?_,
    ?_, ?_, ?_⟩
  · have h : (aeval fun k => coordToSections (Standard.unipotentScheme i ν ∅) (t k) :
          MvPolynomial (Fin d) F →ₐ[F] AffineCoordinateRing F (Standard.unipotentScheme i ν ∅).X) =
        (coordToSections _).comp (aeval t) := by
      rw [MvPolynomial.comp_aeval]
    rw [h, AlgHom.coe_comp]
    exact (coordSectionsEquiv _).bijective.comp ht
  · intro A x y k
    simp only [affinePointEvaluation_coordToSections']
    exact hmul A x y k
  · intro A s x y hxy k
    have hy : y = b.act s x := by
      rw [← cancel_mono (Standard.unipotentHom i ν ∅).hom.hom, Standard.unipotentAction_act_comp]
      simpa only [affinePointsTarget_apply] using hxy
    rw [affinePointEvaluation_coordToSections', affinePointEvaluation_coordToSections', hy]
    exact (show CoordinateWeights.IsEigenfunction b (w k) (t k) from htw k) A s x
  · intro k
    refine (Standard.actionWeightSpace_unipotentAction_ne_bot_iff i ν hT (w k)).mp fun hbot => ?_
    have h := finrank_actionWeightSpace hT b ht htw hε (w k)
    rw [hbot, finrank_bot] at h
    have : Nonempty {j // w j = w k} := ⟨⟨k, rfl⟩⟩
    have : 0 < Nat.card {j // w j = w k} := Nat.card_pos
    omega
  · intro β hβ
    rw [← finrank_actionWeightSpace hT b ht htw hε β]
    exact Standard.finrank_actionWeightSpace_unipotentAction i ν hT hβ

end Langlands.GroupScheme
