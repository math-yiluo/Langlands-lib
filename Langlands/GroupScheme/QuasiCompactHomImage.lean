import Langlands.GroupScheme.HomImage
import Langlands.GroupScheme.GeometricConnectedness

/-! # Affine image factorizations with a possibly nonaffine source -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.QuasiCompactHomImage

open SchematicImage

variable {k : Type u} [Field k]
  {A G : GroupScheme (Spec (CommRingCat.of k))} (φ : A ⟶ G)

/-- A smooth connected affine image, together with the actual factorization and
faithfully flat, quasi-compact projection of locally finite presentation. -/
structure Factorization where
  D : GroupScheme (Spec (CommRingCat.of k))
  inclusion : D ⟶ G
  projection : A ⟶ D
  isClosedSubgroup : IsClosedSubgroup inclusion
  factorization : projection ≫ inclusion = φ
  flat : Flat projection.hom.hom.left
  surjective : Surjective projection.hom.hom.left
  quasiCompact : QuasiCompact projection.hom.hom.left
  locallyOfFinitePresentation : LocallyOfFinitePresentation projection.hom.hom.left
  smooth : Smooth D.X.hom
  connected : ConnectedSpace D.X.left
  affine : IsAffineHom D.X.hom

section Geometric

variable [IsAffineHom G.X.hom] [QuasiCompact φ.hom.hom.left]

local instance : Subsingleton (Spec (CommRingCat.of k)) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum k))

private theorem projection_w :
    (projection φ).hom.hom.left ≫ (image φ).X.hom = A.X.hom :=
  Over.w (projection φ).hom.hom

private instance locallyOfFiniteType_image [LocallyOfFiniteType G.X.hom] :
    LocallyOfFiniteType (image φ).X.hom :=
  inferInstanceAs (LocallyOfFiniteType ((inclusion φ).hom.hom.left ≫ G.X.hom))

private instance geometricallyReduced_image [GeometricallyReduced A.X.hom] :
    GeometricallyReduced (image φ).X.hom := by
  have : GeometricallyReduced ((projection φ).hom.hom.left ≫ (image φ).X.hom) := by
    rw [projection_w]
    infer_instance
  exact ImageGeneration.geometricallyReduced_of_isSchemeTheoreticallyDominant
    (projection φ).hom.hom.left (image φ).X.hom

private instance geometricallyIrreducible_image [GeometricallyIrreducible A.X.hom] :
    GeometricallyIrreducible (image φ).X.hom := by
  have : GeometricallyIrreducible ((projection φ).hom.hom.left ≫ (image φ).X.hom) := by
    rw [projection_w]
    infer_instance
  exact ImageGeneration.geometricallyIrreducible_of_isSchemeTheoreticallyDominant
    (projection φ).hom.hom.left (image φ).X.hom

private instance irreducibleSpace_image [GeometricallyIrreducible A.X.hom] :
    IrreducibleSpace (image φ).X.left :=
  GeometricallyIrreducible.irreducibleSpace_of_subsingleton (image φ).X.hom

private theorem smooth_image [LocallyOfFiniteType G.X.hom] [GeometricallyReduced A.X.hom] :
    Smooth (image φ).X.hom := by
  let : GrpObj (Over.mk (image φ).X.hom) := inferInstanceAs (GrpObj (image φ).X)
  exact smooth_of_grpObj (image φ).X.hom

private instance locallyOfFiniteType_projection [LocallyOfFiniteType A.X.hom] :
    LocallyOfFiniteType (projection φ).hom.hom.left := by
  have : LocallyOfFiniteType ((projection φ).hom.hom.left ≫ (image φ).X.hom) := by
    rw [projection_w]
    infer_instance
  exact locallyOfFiniteType_of_comp _ (image φ).X.hom

private theorem flat_projection [LocallyOfFiniteType A.X.hom] [LocallyOfFiniteType G.X.hom]
    [GeometricallyReduced A.X.hom] : Flat (projection φ).hom.hom.left := by
  have : IsLocallyNoetherian (image φ).X.left :=
    LocallyOfFiniteType.isLocallyNoetherian (image φ).X.hom
  have : IsReduced (image φ).X.left :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian (image φ).X.hom
  exact DominantHomFlat.flat_of_isDominant (projection φ)

private theorem surjective_projection [LocallyOfFiniteType A.X.hom]
    [LocallyOfFiniteType G.X.hom] [GeometricallyReduced A.X.hom]
    [GeometricallyIrreducible A.X.hom] : Surjective (projection φ).hom.hom.left := by
  have := flat_projection φ
  exact DominantHomFlat.surjective_of_flat (projection φ)

private theorem locallyOfFinitePresentation_projection [LocallyOfFiniteType A.X.hom]
    [LocallyOfFiniteType G.X.hom] :
    LocallyOfFinitePresentation (projection φ).hom.hom.left := by
  have : IsLocallyNoetherian (image φ).X.left :=
    LocallyOfFiniteType.isLocallyNoetherian (image φ).X.hom
  infer_instance

/-- The canonical schematic-image factorization for a quasi-compact homomorphism
with geometrically integral, locally finite-type source and affine locally
finite-type target. No affineness assumption is imposed on the source. -/
def ofGeometricallyIntegral [LocallyOfFiniteType A.X.hom] [LocallyOfFiniteType G.X.hom]
    [GeometricallyIntegral A.X.hom] : Factorization φ where
  D := image φ
  inclusion := inclusion φ
  projection := projection φ
  isClosedSubgroup := inferInstanceAs (IsClosedImmersion (inclusion φ).hom.hom.left)
  factorization := projection_inclusion φ
  flat := flat_projection φ
  surjective := surjective_projection φ
  quasiCompact := inferInstance
  locallyOfFinitePresentation := locallyOfFinitePresentation_projection φ
  smooth := smooth_image φ
  connected := inferInstance
  affine := inferInstance

/-- The canonical image factorization for a smooth connected source and a
quasi-compact homomorphism to an affine locally finite-type target. -/
def ofSmoothConnected [Smooth A.X.hom] [ConnectedSpace A.X.left]
    [LocallyOfFiniteType G.X.hom] : Factorization φ := by
  have : QuasiCompact A.X.hom := by
    rw [← Over.w φ.hom.hom]
    infer_instance
  have : GeometricallyConnected A.X.hom := A.geometricallyConnected_of_connected
  have : GeometricallyIntegral A.X.hom :=
    Langlands.AbelianScheme.smoothGeometricIntegrality k A.X.left A.X.hom
      inferInstance inferInstance
  exact ofGeometricallyIntegral φ

end Geometric

end Langlands.GroupScheme.QuasiCompactHomImage
