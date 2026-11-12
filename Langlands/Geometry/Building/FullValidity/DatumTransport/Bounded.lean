import Langlands.Geometry.Building.FullValidity.DatumTransport.Building
import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup
import Langlands.BruhatTits.RationalPoints.BoundedSetOperations

/-!
# Axiom 4.1.2 under based group isomorphisms

An isomorphism `f : G ≅ H` of affine group schemes over `F` maps bounded open subgroups of
`G(F)` onto bounded open subgroups of `H(F)`: the image under `f` is the preimage under the
continuous map `f⁻¹`, and images of algebraically bounded sets are bounded. Since the comparison
`B(G) ≃ B(H)` of `ValuationBuildingData.basedTransport` carries the stabilizers `G(F)^1_y` onto
the stabilizers `H(F)^1_{Φ(y)}`, KP Axiom 4.1.2 is carried along `f`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building

namespace DatumTransport

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G H : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

omit [IsNonarchimedeanLocalField F] in
/-- An isomorphism `f : G ≅ H` carries open bounded subgroups of `G(F)` to open bounded subgroups
of `H(F)`. -/
theorem isOpen_isAlgebraicallyBounded_map (f : G ≅ H) (K : Subgroup (rationalPoints G))
    (hK : letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
      letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
      IsOpen (K : Set (rationalPoints G)) ∧
        IsAlgebraicallyBounded F G.X (K : Set (rationalPoints G))) :
    letI : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
    letI : TopologicalSpace (rationalPoints H) := rationalPointTopology F H.X
    IsOpen ((K.map (rationalPoints.map f.hom) : Subgroup (rationalPoints H)) :
        Set (rationalPoints H)) ∧
      IsAlgebraicallyBounded F H.X
        ((K.map (rationalPoints.map f.hom) : Subgroup (rationalPoints H)) :
          Set (rationalPoints H)) := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : TopologicalSpace (rationalPoints H) := rationalPointTopology F H.X
  have hpre : ((K.map (rationalPoints.map f.hom) : Subgroup (rationalPoints H)) :
      Set (rationalPoints H)) = rationalPoints.map f.inv ⁻¹' (K : Set (rationalPoints G)) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa only [Set.mem_preimage, map_inv_map_hom] using hw
    · intro hz
      exact ⟨rationalPoints.map f.inv z, hz, map_hom_map_inv f z⟩
  refine ⟨?_, ?_⟩
  · rw [hpre]
    exact hK.1.preimage (continuous_rationalPointMap F f.inv.hom.hom)
  · rw [Subgroup.coe_map]
    exact hK.2.image_rationalPointsMap f.hom

end DatumTransport

open DatumTransport

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G H : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  (B : ValuationBuildingData G) {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {j : S.toGrp ⟶ H} (σ : B.S ≅ S) (f : G ≅ H)
  (h : B.i ≫ f.hom = CommGroupScheme.groupHom σ.hom ≫ j)

/-- KP Axiom 4.1.2 for `G` gives Axiom 4.1.2 for `H` with the transported data. -/
theorem HasBoundedOpenStabilizers.basedTransport (hB : B.HasBoundedOpenStabilizers) :
    (B.basedTransport σ f h).HasBoundedOpenStabilizers := by
  intro y
  obtain ⟨y, rfl⟩ := (B.basedBuildingEquiv σ f h).surjective y
  have hK := isOpen_isAlgebraicallyBounded_map f _ (hB y)
  rwa [map_compactStabilizer_basedTransport] at hK

end ValuationBuildingData

end Langlands.Geometry.Building
