import Langlands.GroupScheme.HomImage
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-! # Monic homomorphisms from smooth connected affine groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.HomImage

variable {k : Type u} [Field k]
    {A G : GroupScheme (Spec (CommRingCat.of k))}

/-- A monic homomorphism from a smooth connected affine group to an affine
group locally of finite type is a closed subgroup embedding. -/
theorem isClosedSubgroup_of_mono (f : A ⟶ G) [Mono f.hom.hom]
    [Smooth A.X.hom] [ConnectedSpace A.X.left] [IsAffineHom A.X.hom]
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom] :
    IsClosedSubgroup f := by
  obtain ⟨D, inc, fac, hinc, hfac, hflat, hsurj, hqc, _⟩ := exists_image f
  have hfac' : fac.hom.hom.left ≫ inc.hom.hom.left = f.hom.hom.left :=
    congrArg (fun g => g.hom.hom.left) hfac
  have : Mono fac.hom.hom.left := mono_of_mono_fac hfac'
  have : IsIso fac.hom.hom.left := Flat.isIso_of_surjective_of_mono _
  have : IsClosedImmersion inc.hom.hom.left := hinc
  change IsClosedImmersion f.hom.hom.left
  rw [← hfac']
  infer_instance

end Langlands.GroupScheme.HomImage
