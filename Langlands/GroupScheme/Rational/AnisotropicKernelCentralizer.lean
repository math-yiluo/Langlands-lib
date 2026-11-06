import Langlands.GroupScheme.Rational.AnisotropicSplitTorusHom
import Langlands.GroupScheme.Rational.TorusCentralizer

/-! # A kernel criterion for centralizing a split torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- If a homomorphism kills the torus and its kernel commutes with the image
of `a` on every test scheme, that image lies in the torus centralizer. -/
theorem range_le_torusCentralizer_of_trivial_composite
    {B : Scheme.{u}} {A H G : GroupScheme B}
    {T : CommGroupScheme B} (a : A ⟶ G) (i : T.toGrp ⟶ G) (p : G ⟶ H)
    (hip : i ≫ p = 0)
    (hker : ∀ (U : Over B) (x : U ⟶ A.X) (y : U ⟶ G.X),
      y ≫ p.hom.hom = 1 → Commute (x ≫ a.hom.hom) y) :
    SubgroupFunctor.range a ≤ torusCentralizer i := by
  intro U g hg
  obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hg
  intro V b t
  rw [← Category.assoc]
  apply hker V (b ≫ x) (t ≫ i.hom.hom)
  rw [Category.assoc, ← Grp.comp_hom_hom, hip]
  exact MonObj.comp_one t

/-- An anisotropic affine target kills every map from a split torus, so
commutation with the kernel is enough to centralize that torus. -/
theorem IsAnisotropic.range_le_torusCentralizer_of_kernel_commutes
    {k : Type u} [Field k]
    {A H G : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom]
    (hH : IsAnisotropic H) (hT : IsSplitTorus T.toGrp)
    (a : A ⟶ G) (i : T.toGrp ⟶ G) (p : G ⟶ H)
    (hker : ∀ (U : Over (Spec (CommRingCat.of k))) (x : U ⟶ A.X)
      (y : U ⟶ G.X),
      y ≫ p.hom.hom = 1 → Commute (x ≫ a.hom.hom) y) :
    SubgroupFunctor.range a ≤ torusCentralizer i :=
  range_le_torusCentralizer_of_trivial_composite a i p
    (hH.hom_eq_zero_of_isSplitTorus hT (i ≫ p)) hker

end Langlands.GroupScheme
