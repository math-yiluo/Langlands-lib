import Langlands.GroupScheme.Dynamic.StableIntersection
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Rational.SemistandardIntersection
import Langlands.GroupScheme.Rational.PointDecomposition

/-! # All-test intersection products for a common commutative acting group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.GroupScheme

namespace AutomorphicAction

variable {S : Scheme.{u}} {H K G : GroupScheme S}

/-- Restricting the acting group preserves all-test stability. -/
theorem IsStable.restrict {a : AutomorphicAction H G} {F : SubgroupFunctor G}
    (hF : a.IsStable F) (f : K ⟶ H) : (a.restrict f).IsStable F := by
  intro T h g hg
  simpa only [restrict_act] using hF T (h ≫ f.hom.hom) g hg

end AutomorphicAction

namespace Dynamic

section Affine

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} [IsAffine G.X.left]
    [IsSeparated G.X.hom] {A : CommGroupScheme (Spec R)} (i : A.toGrp ⟶ G)
    (α β : (Gm (Spec R)).toGrp ⟶ A.toGrp)

/-- The first ordered intersection product for two cocharacters of a common
commutative acting group, over every test scheme. -/
theorem centralizer_inf_parabolic_eq_mul (T : Over (Spec R)) :
    (↑((centralizer (α ≫ i) ⊓ parabolic (β ≫ i)).carrier T) : Set (T ⟶ G.X)) =
      (↑((centralizer (α ≫ i) ⊓ centralizer (β ≫ i)).carrier T) : Set (T ⟶ G.X)) *
        (↑((centralizer (α ≫ i) ⊓ unipotent (β ≫ i)).carrier T) : Set (T ⟶ G.X)) := by
  have hF := (centralizer_isStable_conjugation i α).restrict β
  rw [AutomorphicAction.restrict_conjugation] at hF
  exact inf_parabolic_eq_mul_of_isStable (β ≫ i)
    (Affine.isRepresentedBy_centralizerHom (α ≫ i))
    (Affine.isClosedSubgroup_centralizerHom (α ≫ i)) hF T

/-- The second ordered intersection product, retaining every original test
scheme and requiring no nesting of the two dynamic parabolics. -/
theorem unipotent_inf_parabolic_eq_mul (T : Over (Spec R)) :
    (↑((unipotent (α ≫ i) ⊓ parabolic (β ≫ i)).carrier T) : Set (T ⟶ G.X)) =
      (↑((unipotent (α ≫ i) ⊓ centralizer (β ≫ i)).carrier T) : Set (T ⟶ G.X)) *
        (↑((unipotent (α ≫ i) ⊓ unipotent (β ≫ i)).carrier T) : Set (T ⟶ G.X)) := by
  have hF := (unipotent_isStable_conjugation i α).restrict β
  rw [AutomorphicAction.restrict_conjugation] at hF
  exact inf_parabolic_eq_mul_of_isStable (β ≫ i)
    (Affine.isRepresentedBy_unipotentHom (α ≫ i))
    (Affine.isClosedSubgroup_unipotentHom (α ≫ i)) hF T

end Affine

/-- The two all-test products required by the general semistandard target.
The common acting group need only be commutative. -/
theorem semistandardIntersectionProducts
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) {A : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : A.toGrp ⟶ G) (α β : cocharacterLattice A) :
    SubgroupFunctor.SemistandardIntersectionProducts
      (centralizer (CommGroupScheme.groupHom α ≫ i))
      (unipotent (CommGroupScheme.groupHom α ≫ i))
      (parabolic (CommGroupScheme.groupHom β ≫ i))
      (centralizer (CommGroupScheme.groupHom β ≫ i))
      (unipotent (CommGroupScheme.groupHom β ≫ i)) := by
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.isSeparated
  intro T
  exact ⟨centralizer_inf_parabolic_eq_mul i (CommGroupScheme.groupHom α)
      (CommGroupScheme.groupHom β) T,
    unipotent_inf_parabolic_eq_mul i (CommGroupScheme.groupHom α)
      (CommGroupScheme.groupHom β) T⟩

end Dynamic

end Langlands.GroupScheme
