import Langlands.GroupScheme.Torus.ImageProof
import Langlands.GroupScheme.Torus.SplitOfDomination
import Langlands.GroupScheme.HomImage
import Langlands.AbelianScheme.Isogeny

/-! # Finite homomorphisms from tori onto their actual images -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {T H : GroupScheme (Spec (CommRingCat.of k))}

/-- A finite homomorphism from a torus induces an isogeny onto its actual
schematic image. No smoothness or connectedness of the ambient target is needed. -/
theorem IsTorus.isIsogeny_schematicImageProjection
    (hT : IsTorus T) [LocallyOfFiniteType H.X.hom] [IsAffineHom H.X.hom]
    (f : T ⟶ H) [IsFinite f.hom.hom.left] :
    IsIsogeny (SchematicImage.projection f) := by
  have : IsAffine T.X.left := SplittingAssembly.isAffine_of_isTorus T hT
  have : IsAffineHom T.X.hom := inferInstance
  have : Smooth T.X.hom := hT.smooth
  have : ConnectedSpace T.X.left := hT.connectedSpace
  have : GeometricallyIntegral T.X.hom :=
    smoothConnectedAffineGeometry.1 k T inferInstance inferInstance inferInstance
  refine ⟨?_, HomImage.flat_projection f, HomImage.surjective_projection f⟩
  have hcomp : IsFinite ((SchematicImage.projection f).hom.hom.left ≫
      (SchematicImage.inclusion f).hom.hom.left) := by
    change IsFinite ((SchematicImage.projection f ≫ SchematicImage.inclusion f).hom.hom.left)
    rw [SchematicImage.projection_inclusion]
    infer_instance
  exact IsFinite.of_comp _ (SchematicImage.inclusion f).hom.hom.left

/-- The actual schematic image of a homomorphism from a split torus is split. -/
theorem IsSplitTorus.isSplitTorus_schematicImage
    (hT : IsSplitTorus T) [IsAffineHom H.X.hom]
    (f : T ⟶ H) [QuasiCompact f.hom.hom.left] :
    IsSplitTorus (SchematicImage.image f) :=
  hT.of_schematicallyDominant_hom (SchematicImage.projection f) inferInstance

/-- Restricting a finite ambient homomorphism to a closed torus gives an
isogeny onto the actual torus image. -/
theorem IsTorus.exists_isogeny_finiteHomImage
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (hT : IsTorus T) [LocallyOfFiniteType H.X.hom] [IsAffineHom H.X.hom]
    (i : T ⟶ G) (hi : IsClosedSubgroup i)
    (q : G ⟶ H) [IsFinite q.hom.hom.left] :
    ∃ (D : CommGroupScheme (Spec (CommRingCat.of k)))
      (j : D.toGrp ⟶ H) (t : T ⟶ D.toGrp),
      IsTorus D.toGrp ∧ IsClosedSubgroup j ∧ IsIsogeny t ∧
      t ≫ j = i ≫ q ∧ (IsSplitTorus T → IsSplitTorus D.toGrp) := by
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsFinite (i ≫ q).hom.hom.left := by
    change IsFinite (i.hom.hom.left ≫ q.hom.hom.left)
    infer_instance
  have hD := hT.isTorus_schematicImage (i ≫ q)
  let D : CommGroupScheme (Spec (CommRingCat.of k)) :=
    { SchematicImage.image (i ≫ q) with comm := hD.isCommMonObj }
  exact ⟨D, SchematicImage.inclusion (i ≫ q), SchematicImage.projection (i ≫ q),
    hD, inferInstanceAs (IsClosedImmersion (SchematicImage.inclusion (i ≫ q)).hom.hom.left),
    hT.isIsogeny_schematicImageProjection (i ≫ q),
    SchematicImage.projection_inclusion (i ≫ q),
    fun hs => hs.isSplitTorus_schematicImage (i ≫ q)⟩

/-- Over every field, a finite homomorphism from a torus has actual closed
torus image, induces an isogeny onto it, and preserves splitness of the image. -/
def FiniteTorusImageStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (T H : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType H.X.hom] [IsAffineHom H.X.hom],
    IsTorus T → ∀ (f : T ⟶ H) [IsFinite f.hom.hom.left],
      IsTorus (SchematicImage.image f) ∧
      IsClosedSubgroup (SchematicImage.inclusion f) ∧
      IsIsogeny (SchematicImage.projection f) ∧
      SchematicImage.projection f ≫ SchematicImage.inclusion f = f ∧
      (IsSplitTorus T → IsSplitTorus (SchematicImage.image f))

theorem finiteTorusImageStatement : FiniteTorusImageStatement.{u} := by
  intro k _ T H _ _ hT f _
  exact ⟨hT.isTorus_schematicImage f,
    inferInstanceAs (IsClosedImmersion (SchematicImage.inclusion f).hom.hom.left),
    hT.isIsogeny_schematicImageProjection f, SchematicImage.projection_inclusion f,
    fun hs => hs.isSplitTorus_schematicImage f⟩

end Langlands.GroupScheme
