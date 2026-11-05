import Langlands.GroupScheme.Rational.MinimalStandardDynamicComparison
import Langlands.GroupScheme.Rational.LeviMultiplication

/-! # Actual multiplication for the canonical empty-index standard subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)

include hG hi hν

/-- The empty-index standard Levi is the dynamic centralizer of the generic
cocharacter, as a subgroup functor on every test scheme. -/
theorem standardLevi_empty_eq_dynamic_of_generic :
    standardLevi i ν ∅ = Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) := by
  rw [standardLevi_empty_eq_torusCentralizer_of_generic i ν hG hi hν,
    genericCentralizer k G hG T i hi ν hν]

namespace Standard

/-- The actual Levi-first multiplication for the canonical empty-index standard
subgroups is an isomorphism of schemes over the ground field. -/
theorem isIso_emptySubgroupMultiplication :
    IsIso (subgroupMultiplication (leviToParabolic i ν ∅)
      (unipotentToParabolic i ν ∅)) := by
  have hP : (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy
      (parabolicHom i ν ∅) := by
    rw [← standardParabolic_empty_eq_dynamic_of_generic i ν hG hi hν]
    exact isRepresentedBy_parabolicHom i ν ∅
  have hL : (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy
      (leviHom i ν ∅) := by
    rw [← standardLevi_empty_eq_dynamic_of_generic i ν hG hi hν]
    exact isRepresentedBy_leviHom i ν ∅
  have hU : (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy
      (unipotentHom i ν ∅) := by
    rw [← standardUnipotent_empty_eq_dynamic i ν hG hi]
    exact isRepresentedBy_unipotentHom i ν ∅
  exact Dynamic.isIso_subgroupMultiplication hP hL hU
    (leviToParabolic i ν ∅) (unipotentToParabolic i ν ∅)
    (leviToParabolic_comp i ν ∅) (unipotentToParabolic_comp i ν ∅)

/-- The scheme isomorphism whose forward morphism is exactly the existing
canonical Levi-first subgroup multiplication. -/
def emptyLeviMultiplicationIso :
    (leviScheme i ν ∅).X ⊗ (unipotentScheme i ν ∅).X ≅
      (parabolicScheme i ν ∅).X :=
  haveI := isIso_emptySubgroupMultiplication i ν hG hi hν
  asIso (subgroupMultiplication (leviToParabolic i ν ∅)
    (unipotentToParabolic i ν ∅))

@[simp]
theorem emptyLeviMultiplicationIso_hom :
    (emptyLeviMultiplicationIso i ν hG hi hν).hom =
      subgroupMultiplication (leviToParabolic i ν ∅)
        (unipotentToParabolic i ν ∅) := rfl

/-- On every test scheme the isomorphism multiplies the original canonical
Levi and unipotent images, with the Levi factor first. -/
theorem comp_emptyLeviMultiplicationIso_hom
    {V : Over (Spec (CommRingCat.of k))}
    (l : V ⟶ (leviScheme i ν ∅).X) (n : V ⟶ (unipotentScheme i ν ∅).X) :
    lift l n ≫ (emptyLeviMultiplicationIso i ν hG hi hν).hom =
      (l ≫ (leviToParabolic i ν ∅).hom.hom) *
        (n ≫ (unipotentToParabolic i ν ∅).hom.hom) :=
  comp_subgroupMultiplication _ _ l n

end Standard

end Langlands.GroupScheme
