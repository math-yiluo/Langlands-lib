import Langlands.GroupScheme.HomImage
import Langlands.GroupScheme.Lie.SubgroupCellDimension
import Langlands.GroupScheme.Rational.SplitUnipotentProductGeometry

/-! # Finite homomorphisms of equal-dimensional smooth groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    [Smooth G.X.hom] [Smooth H.X.hom]
    [ConnectedSpace G.X.left] [ConnectedSpace H.X.left]

/-- A finite homomorphism of smooth connected affine groups of the same
actual Lie dimension is finite, flat and surjective. No separability or
smoothness of the kernel is assumed. -/
theorem isIsogeny_of_isFinite_of_finrank_eq
    (q : G ⟶ H) [IsFinite q.hom.hom.left]
    (hdim : Module.finrank k (Additive (lieKernel G k)) =
      Module.finrank k (Additive (lieKernel H k))) : IsIsogeny q := by
  obtain ⟨D, inc, fac, hinc, hfac, hflat, hsurj, hqc, hfp, hsm, hconn, haff⟩ :=
    HomImage.exists_image q
  let : IsAffineHom D.X.hom := haff
  let : Smooth D.X.hom := hsm
  let : Flat fac.hom.hom.left := hflat
  let : Surjective fac.hom.hom.left := hsurj
  let : IsClosedImmersion inc.hom.hom.left := hinc
  have hfac' : fac.hom.hom.left ≫ inc.hom.hom.left = q.hom.hom.left :=
    congrArg (fun f => f.hom.hom.left) hfac
  have : IsFinite (fac.hom.hom.left ≫ inc.hom.hom.left) :=
    hfac'.symm ▸ inferInstance
  have : IsFinite fac.hom.hom.left :=
    IsFinite.of_comp fac.hom.hom.left inc.hom.hom.left
  have hDdim := Lie.finrank_kernel_eq_of_flat_locallyQuasiFinite fac
  let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  obtain ⟨d, hd⟩ := Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension
    H.X.left (Spec (CommRingCat.of k)) H.X.hom inferInstance inferInstance
  have hHdim : Module.finrank k (Additive (lieKernel H k)) = d :=
    Lie.dimension_eq_of_smoothOfRelativeDimension H hd
  have hdim' : Module.finrank k (Additive (lieKernel D k)) = d :=
    hDdim.symm.trans (hdim.trans hHdim)
  have hbound : (d : WithBot ℕ∞) ≤ topologicalKrullDim D.X.left := by
    rw [← hdim']
    exact Lie.finrank_kernel_cast_le_topologicalKrullDim D
  have : Surjective inc.hom.hom.left :=
    RelativeRoot.ProductGeometry.surjective_of_closedImmersion_of_fullDimension
      H.X.hom hd inc.hom.hom.left hbound
  have : IsReduced H.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k H.X.left H.X.hom
  have : IsIso inc.hom.hom.left :=
    isIso_of_isClosedImmersion_of_surjective inc.hom.hom.left
  exact ⟨inferInstance, hfac' ▸ inferInstance, hfac' ▸ inferInstance⟩

/-- The canonical schematic-image inclusion is an isomorphism for a finite
homomorphism of equal-dimensional smooth connected affine groups. -/
def imageIsoOfFiniteFinrankEq
    (q : G ⟶ H) [IsFinite q.hom.hom.left]
    (hdim : Module.finrank k (Additive (lieKernel G k)) =
      Module.finrank k (Additive (lieKernel H k))) : SchematicImage.image q ≅ H := by
  have hq := isIsogeny_of_isFinite_of_finrank_eq q hdim
  have hfac : (SchematicImage.projection q).hom.hom.left ≫
      (SchematicImage.inclusion q).hom.hom.left = q.hom.hom.left :=
    congrArg (fun f => f.hom.hom.left) (SchematicImage.projection_inclusion q)
  have : Surjective ((SchematicImage.projection q).hom.hom.left ≫
      (SchematicImage.inclusion q).hom.hom.left) := hfac.symm ▸ hq.2.2
  have : Surjective (SchematicImage.inclusion q).hom.hom.left :=
    Surjective.of_comp (SchematicImage.projection q).hom.hom.left
      (SchematicImage.inclusion q).hom.hom.left
  have : IsReduced H.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k H.X.left H.X.hom
  have : IsIso (SchematicImage.inclusion q).hom.hom.left :=
    isIso_of_isClosedImmersion_of_surjective (SchematicImage.inclusion q).hom.hom.left
  have : IsIso ((Over.forget _).map (SchematicImage.inclusion q).hom.hom) := by
    change IsIso (SchematicImage.inclusion q).hom.hom.left
    infer_instance
  have : IsIso (SchematicImage.inclusion q).hom.hom :=
    isIso_of_reflects_iso _ (Over.forget _)
  exact Grp.mkIso' (asIso (SchematicImage.inclusion q).hom.hom)

@[simp] theorem imageIsoOfFiniteFinrankEq_hom
    (q : G ⟶ H) [IsFinite q.hom.hom.left]
    (hdim : Module.finrank k (Additive (lieKernel G k)) =
      Module.finrank k (Additive (lieKernel H k))) :
    (imageIsoOfFiniteFinrankEq q hdim).hom = SchematicImage.inclusion q := rfl

end Langlands.GroupScheme
