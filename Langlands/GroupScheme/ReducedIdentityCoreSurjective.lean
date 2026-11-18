import Langlands.GroupScheme.KernelCoreQuotientDimension
import Langlands.GroupScheme.DominantHomFaithfullyFlat

/-! # Faithful flatness of a reduced identity-core restriction -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ReducedSubgroup

variable {k : Type u} [Field k] [PerfectField k]
    {E G : GroupScheme (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType E.X.hom] [IsAffineHom E.X.hom]
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]

/-- The homomorphism obtained by restricting a group homomorphism to the smooth
connected reduced identity core of its source. -/
def identityCoreRestriction (q : E ⟶ G) : identityCore E ⟶ G :=
  identityCoreι E ≫ q

/-- A flat map onto a connected smooth affine group remains faithfully flat after
restriction to the smooth connected reduced identity core of its source. -/
theorem identityCore_comp_flat_surjective (q : E ⟶ G) [Flat q.hom.hom.left] :
    Flat (identityCoreι E ≫ q).hom.hom.left ∧
      Surjective (identityCoreι E ≫ q).hom.hom.left := by
  let f := identityCoreι E ≫ q
  have : LocallyOfFiniteType q.hom.hom.left := by
    have : LocallyOfFiniteType (q.hom.hom.left ≫ G.X.hom) := by
      rw [Over.w]
      infer_instance
    exact locallyOfFiniteType_of_comp q.hom.hom.left G.X.hom
  have : IsLocallyNoetherian G.X.left := LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  have : LocallyOfFinitePresentation q.hom.hom.left := inferInstance
  have hopen : IsOpen (Set.range f.hom.hom.left) := by
    change IsOpen (Set.range ((identityCoreι E).hom.hom.left ≫ q.hom.hom.left))
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    exact q.hom.hom.left.isOpenMap _ (isOpen_range_identityCoreι E)
  obtain ⟨_, _, hsurj, _, _⟩ := AffineHomImage.projection_geometry f
  have : Surjective (AffineHomImage.projection f).hom.hom.left := hsurj
  have hrange : Set.range f.hom.hom.left =
      Set.range (AffineHomImage.inclusion f).hom.hom.left := by
    calc
      _ = Set.range (AffineHomImage.projection f ≫ AffineHomImage.inclusion f).hom.hom.left :=
        congrArg (fun g => Set.range g.hom.hom.left)
          (AffineHomImage.projection_inclusion f).symm
      _ = _ := by
        rw [Grp.comp_hom_hom, Over.comp_left, Scheme.Hom.comp_base, TopCat.coe_comp,
          Set.range_comp,
          Set.range_eq_univ.mpr (AffineHomImage.projection f).hom.hom.left.surjective,
          Set.image_univ]
  have hclosed : IsClosed (Set.range f.hom.hom.left) := by
    rw [hrange]
    exact (AffineHomImage.inclusion f).hom.hom.left.isClosedEmbedding.isClosed_range
  have huniv : Set.range f.hom.hom.left = Set.univ :=
    (show IsClopen (Set.range f.hom.hom.left) from ⟨hclosed, hopen⟩).eq_univ
      ⟨f.hom.hom.left (IdentityComponent.identityPoint (identityCore E)), Set.mem_range_self _⟩
  have : Surjective f.hom.hom.left := ⟨Set.range_eq_univ.mp huniv⟩
  have : IsReduced G.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k G.X.left G.X.hom
  have : IsSchemeTheoreticallyDominant f.hom.hom.left :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  exact DominantHom.flat_surjective f

/-- The defined core restriction is faithfully flat under the flatness hypothesis
on the original homomorphism. -/
theorem identityCoreRestriction_flat_surjective (q : E ⟶ G) [Flat q.hom.hom.left] :
    Flat (identityCoreRestriction q).hom.hom.left ∧
      Surjective (identityCoreRestriction q).hom.hom.left :=
  identityCore_comp_flat_surjective q

end Langlands.GroupScheme.ReducedSubgroup
