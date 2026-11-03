import Langlands.GroupScheme.SchematicImage
import Langlands.GroupScheme.DominantHomFlat
import Langlands.GroupScheme.SmoothConnectedGeometryProof
import Mathlib.AlgebraicGeometry.Group.Smooth

/-! # Images of homomorphisms from geometrically integral groups over a field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.HomImage

open SchematicImage

variable {k : Type u} [Field k] {A G : GroupScheme (Spec (CommRingCat.of k))} (φ : A ⟶ G)

local instance : Subsingleton (Spec (CommRingCat.of k)) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum k))

section Geometric

variable [IsAffineHom A.X.hom] [IsAffineHom G.X.hom]

local instance : IsAffine A.X.left := isAffine_of_isAffineHom A.X.hom
local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- A homomorphism between affine groups over a field is quasi-compact. -/
instance quasiCompact_hom : QuasiCompact φ.hom.hom.left := inferInstance

theorem isClosedSubgroup_inclusion : IsClosedSubgroup (inclusion φ) :=
  inferInstanceAs (IsClosedImmersion (inclusion φ).hom.hom.left)

theorem projection_w : (projection φ).hom.hom.left ≫ (image φ).X.hom = A.X.hom :=
  Over.w (projection φ).hom.hom

instance locallyOfFiniteType_image [LocallyOfFiniteType G.X.hom] :
    LocallyOfFiniteType (image φ).X.hom :=
  inferInstanceAs (LocallyOfFiniteType ((inclusion φ).hom.hom.left ≫ G.X.hom))

instance geometricallyReduced_image [GeometricallyReduced A.X.hom] :
    GeometricallyReduced (image φ).X.hom := by
  have : GeometricallyReduced ((projection φ).hom.hom.left ≫ (image φ).X.hom) := by
    rw [projection_w]
    infer_instance
  exact ImageGeneration.geometricallyReduced_of_isSchemeTheoreticallyDominant
    (projection φ).hom.hom.left (image φ).X.hom

instance geometricallyIrreducible_image [GeometricallyIrreducible A.X.hom] :
    GeometricallyIrreducible (image φ).X.hom := by
  have : GeometricallyIrreducible ((projection φ).hom.hom.left ≫ (image φ).X.hom) := by
    rw [projection_w]
    infer_instance
  exact ImageGeneration.geometricallyIrreducible_of_isSchemeTheoreticallyDominant
    (projection φ).hom.hom.left (image φ).X.hom

instance irreducibleSpace_image [GeometricallyIrreducible A.X.hom] :
    IrreducibleSpace (image φ).X.left :=
  GeometricallyIrreducible.irreducibleSpace_of_subsingleton (image φ).X.hom

instance connectedSpace_image [GeometricallyIrreducible A.X.hom] :
    ConnectedSpace (image φ).X.left := inferInstance

theorem smooth_image [LocallyOfFiniteType G.X.hom] [GeometricallyReduced A.X.hom] :
    Smooth (image φ).X.hom := by
  let : GrpObj (Over.mk (image φ).X.hom) := inferInstanceAs (GrpObj (image φ).X)
  exact smooth_of_grpObj (image φ).X.hom

instance locallyOfFiniteType_projection [LocallyOfFiniteType A.X.hom] :
    LocallyOfFiniteType (projection φ).hom.hom.left := by
  have : LocallyOfFiniteType ((projection φ).hom.hom.left ≫ (image φ).X.hom) := by
    rw [projection_w]
    infer_instance
  exact locallyOfFiniteType_of_comp _ (image φ).X.hom

theorem flat_projection [LocallyOfFiniteType A.X.hom] [LocallyOfFiniteType G.X.hom]
    [GeometricallyReduced A.X.hom] : Flat (projection φ).hom.hom.left := by
  have : IsLocallyNoetherian (image φ).X.left :=
    LocallyOfFiniteType.isLocallyNoetherian (image φ).X.hom
  have : IsReduced (image φ).X.left :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian (image φ).X.hom
  exact DominantHomFlat.flat_of_isDominant (projection φ)

theorem surjective_projection [LocallyOfFiniteType A.X.hom] [LocallyOfFiniteType G.X.hom]
    [GeometricallyReduced A.X.hom] [GeometricallyIrreducible A.X.hom] :
    Surjective (projection φ).hom.hom.left := by
  have := flat_projection φ
  exact DominantHomFlat.surjective_of_flat (projection φ)

theorem locallyOfFinitePresentation_projection [LocallyOfFiniteType A.X.hom]
    [LocallyOfFiniteType G.X.hom] :
    LocallyOfFinitePresentation (projection φ).hom.hom.left := by
  have : IsLocallyNoetherian (image φ).X.left :=
    LocallyOfFiniteType.isLocallyNoetherian (image φ).X.hom
  infer_instance

end Geometric

/-- The schematic image of a homomorphism from a smooth connected affine group to an affine
group locally of finite type is a smooth connected affine closed subgroup, and the
homomorphism factors through it by a flat, surjective, quasi-compact homomorphism of locally
finite presentation. -/
theorem exists_image [Smooth A.X.hom] [ConnectedSpace A.X.left] [IsAffineHom A.X.hom]
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom] :
    ∃ (D : GroupScheme (Spec (CommRingCat.of k))) (inc : D ⟶ G) (fac : A ⟶ D),
      IsClosedSubgroup inc ∧ fac ≫ inc = φ ∧ Flat fac.hom.hom.left ∧
        Surjective fac.hom.hom.left ∧ QuasiCompact fac.hom.hom.left ∧
        LocallyOfFinitePresentation fac.hom.hom.left ∧
        Smooth D.X.hom ∧ ConnectedSpace D.X.left ∧ IsAffineHom D.X.hom := by
  have : GeometricallyIntegral A.X.hom :=
    smoothConnectedAffineGeometry.1 k A inferInstance inferInstance inferInstance
  exact ⟨image φ, inclusion φ, projection φ, isClosedSubgroup_inclusion φ,
    projection_inclusion φ, flat_projection φ, surjective_projection φ, inferInstance,
    locallyOfFinitePresentation_projection φ, smooth_image φ, inferInstance, inferInstance⟩

end Langlands.GroupScheme.HomImage

namespace Langlands.GroupScheme

/-- Over a field, every homomorphism from a smooth connected affine group to an affine group
locally of finite type factors as a flat, surjective, quasi-compact homomorphism of locally
finite presentation onto a smooth connected affine group, followed by a closed subgroup
embedding. -/
def SmoothConnectedHomImageStatement : Prop :=
  ∀ (k : Type u) [Field k] (A G : GroupScheme (Spec (CommRingCat.of k))) (φ : A ⟶ G),
    Smooth A.X.hom → ConnectedSpace A.X.left → IsAffineHom A.X.hom →
    LocallyOfFiniteType G.X.hom → IsAffineHom G.X.hom →
    ∃ (D : GroupScheme (Spec (CommRingCat.of k))) (inc : D ⟶ G) (fac : A ⟶ D),
      IsClosedSubgroup inc ∧ fac ≫ inc = φ ∧ Flat fac.hom.hom.left ∧
        Surjective fac.hom.hom.left ∧ QuasiCompact fac.hom.hom.left ∧
        LocallyOfFinitePresentation fac.hom.hom.left ∧
        Smooth D.X.hom ∧ ConnectedSpace D.X.left ∧ IsAffineHom D.X.hom

theorem smoothConnectedHomImage : SmoothConnectedHomImageStatement.{u} := by
  intro k _ A G φ hA hAc hAa hG hGa
  exact HomImage.exists_image φ

end Langlands.GroupScheme
