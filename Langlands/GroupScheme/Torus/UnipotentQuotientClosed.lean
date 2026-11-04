import Langlands.GroupScheme.HomImageEmbedding
import Langlands.GroupScheme.Torus.Geometry
import Langlands.GroupScheme.Torus.UnipotentQuotientMono
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-! # Closed torus images in quotients with unipotent kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace HomImage

variable {k : Type u} [Field k]
  {A G : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth A.X.hom] [ConnectedSpace A.X.left] [IsAffineHom A.X.hom]
  [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom]
  (f : A ⟶ G) [Mono f.hom.hom]

/-- For a monomorphism from a smooth connected affine group, the canonical
projection onto its schematic image is an isomorphism. -/
theorem isIso_projection_of_mono : IsIso (SchematicImage.projection f) := by
  have : GeometricallyIntegral A.X.hom :=
    smoothConnectedAffineGeometry.1 k A inferInstance inferInstance inferInstance
  have : Mono f.hom.hom.left := Over.mono_left_of_mono _
  have : Mono (SchematicImage.projection f).hom.hom.left :=
    mono_of_mono_fac (congrArg (fun a => a.hom.hom.left)
      (SchematicImage.projection_inclusion f))
  have : Flat (SchematicImage.projection f).hom.hom.left := flat_projection f
  have : Surjective (SchematicImage.projection f).hom.hom.left := surjective_projection f
  have : IsIso (SchematicImage.projection f).hom.hom.left :=
    Flat.isIso_of_surjective_of_mono _
  have : IsIso ((Over.forget _).map (SchematicImage.projection f).hom.hom) := by
    change IsIso (SchematicImage.projection f).hom.hom.left
    infer_instance
  have : IsIso (SchematicImage.projection f).hom.hom :=
    isIso_of_reflects_iso _ (Over.forget _)
  let e : A ≅ SchematicImage.image f := Grp.mkIso' (asIso (SchematicImage.projection f).hom.hom)
  change IsIso e.hom
  infer_instance

/-- The actual source-to-schematic-image isomorphism of a smooth connected
affine monomorphism. -/
def sourceImageIsoOfMono : A ≅ SchematicImage.image f :=
  letI := isIso_projection_of_mono f
  asIso (SchematicImage.projection f)

@[simp]
theorem sourceImageIsoOfMono_hom :
    (sourceImageIsoOfMono f).hom = SchematicImage.projection f :=
  rfl

end HomImage

section Torus

variable {k : Type u} [Field k]
  {T G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom T.X.hom] [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom]

/-- An affine torus mapping monomorphically into an affine group locally of
finite type is a closed torus. -/
theorem IsTorus.isClosedSubgroup_of_mono (hT : IsTorus T)
    (f : T ⟶ G) [Mono f.hom.hom] : IsClosedSubgroup f := by
  have := hT.smooth
  have := hT.connectedSpace
  exact HomImage.isClosedSubgroup_of_mono f

end Torus

section Quotient

variable {k : Type u} [Field k]
  {N T G Q : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom N.X.hom] [LocallyOfFiniteType N.X.hom]
  [IsAffineHom G.X.hom] [IsAffineHom Q.X.hom] [LocallyOfFiniteType Q.X.hom]

/-- A closed torus stays closed through an affine finite-type target map whose
full kernel lies in an affine finite-type unipotent range. Closed-subgroup
unipotence remains an explicit premise. -/
theorem IsUnipotent.closed_torus_quotient
    (hsub : UnipotentClosedSubgroupStatement.{u})
    (hN : IsUnipotent N) (hT : IsTorus T)
    (n : N ⟶ G) (i : T ⟶ G) (hi : IsClosedSubgroup i)
    (q : G ⟶ Q)
    (hker : SubgroupFunctor.range (kernelι q) ≤ SubgroupFunctor.range n) :
    IsClosedSubgroup (i ≫ q) := by
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsAffineHom T.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have := hN.mono_torus_quotient hsub hT n i hi q hker
  exact hT.isClosedSubgroup_of_mono (i ≫ q)

/-- The source torus is isomorphic to the actual schematic image of its map
through the quotient, conditional on closed-subgroup unipotence. -/
def IsUnipotent.torusQuotientImageIso [IsAffineHom T.X.hom]
    (hsub : UnipotentClosedSubgroupStatement.{u})
    (hN : IsUnipotent N) (hT : IsTorus T)
    (n : N ⟶ G) (i : T ⟶ G) (hi : IsClosedSubgroup i)
    (q : G ⟶ Q)
    (hker : SubgroupFunctor.range (kernelι q) ≤ SubgroupFunctor.range n) :
    T ≅ SchematicImage.image (i ≫ q) := by
  letI := hT.smooth
  letI := hT.connectedSpace
  letI := hN.mono_torus_quotient hsub hT n i hi q hker
  exact HomImage.sourceImageIsoOfMono (i ≫ q)

omit [IsAffineHom G.X.hom] in
@[simp]
theorem IsUnipotent.torusQuotientImageIso_hom [IsAffineHom T.X.hom]
    (hsub : UnipotentClosedSubgroupStatement.{u})
    (hN : IsUnipotent N) (hT : IsTorus T)
    (n : N ⟶ G) (i : T ⟶ G) (hi : IsClosedSubgroup i)
    (q : G ⟶ Q)
    (hker : SubgroupFunctor.range (kernelι q) ≤ SubgroupFunctor.range n) :
    (hN.torusQuotientImageIso hsub hT n i hi q hker).hom =
      SchematicImage.projection (i ≫ q) :=
  rfl

end Quotient

end Langlands.GroupScheme
