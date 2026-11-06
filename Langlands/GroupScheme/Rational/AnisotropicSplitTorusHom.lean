import Langlands.GroupScheme.Rational.SplitTorusImage

/-! # Homomorphisms from split tori to anisotropic affine groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom]

/-- Every homomorphism from a split torus to an anisotropic affine group is
the trivial homomorphism. -/
theorem IsAnisotropic.hom_eq_zero_of_isSplitTorus
    (hG : IsAnisotropic G) (hT : IsSplitTorus T.toGrp) (f : T.toGrp ⟶ G) :
    f = 0 := by
  obtain ⟨D, p, j, hj, hfac, _⟩ := hT.exists_factor_isSplitSubtorus f
  have : Subsingleton (D.toGrp ⟶ G) :=
    hG.subsingleton_hom_of_isSplitSubtorus hj G
  have hj0 : j = 0 := Subsingleton.elim _ _
  rw [← hfac, hj0, Limits.comp_zero]

/-- The homomorphism is trivial on every test scheme, including nonreduced
tests. -/
theorem IsAnisotropic.comp_hom_eq_one_of_isSplitTorus
    (hG : IsAnisotropic G) (hT : IsSplitTorus T.toGrp) (f : T.toGrp ⟶ G)
    {U : Over (Spec (CommRingCat.of k))} (t : U ⟶ T.X) :
    t ≫ f.hom.hom = 1 := by
  rw [hG.hom_eq_zero_of_isSplitTorus hT f]
  exact MonObj.comp_one t

/-- The canonical unique homomorphism from a split torus to an anisotropic
affine group scheme. Its value is the trivial homomorphism. -/
@[instance_reducible]
def IsAnisotropic.uniqueHomFromSplitTorus
    (hG : IsAnisotropic G) (hT : IsSplitTorus T.toGrp) :
    Unique (T.toGrp ⟶ G) where
  default := 0
  uniq f := hG.hom_eq_zero_of_isSplitTorus hT f

end Langlands.GroupScheme
