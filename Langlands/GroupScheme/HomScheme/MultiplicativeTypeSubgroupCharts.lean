import Langlands.GroupScheme.HomScheme.MultiplicativeTypeSubgroupModuli
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Open charts of the functor of closed multiplicative-type subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.MultiplicativeTypeSubgroupModuli

open TorusSubgroupModuli

variable {S : Scheme.{u}} {G : GroupScheme S}

/-- An open chart of the functor of closed multiplicative-type subgroups of `G`: a smooth
scheme `U/S` with a closed multiplicative-type family `j` over `U`, whose evaluation map is
injective and whose pullback along every closed multiplicative-type family over every `T/S`
is represented by an open subscheme of `T`. -/
structure IsOpenChart {U : Over S} {K : GroupScheme U.left}
    (j : K ⟶ (GroupScheme.baseChange U.hom).obj G) : Prop where
  isClosedSubgroup : IsClosedSubgroup j
  isMultiplicativeType : RelativeMultiplicativeType.IsMultiplicativeType K
  smooth : Smooth U.hom
  injective : ∀ (T : Over S) (a b : T ⟶ U), evaluate j a = evaluate j b → a = b
  isOpen : ∀ (T : Over S) (L : GroupScheme T.left)
    (i : L ⟶ (GroupScheme.baseChange T.hom).obj G),
    IsClosedSubgroup i → RelativeMultiplicativeType.IsMultiplicativeType L →
    ∃ V : T.left.Opens, ∀ (T' : Over S) (b : T' ⟶ T),
      (∃ a : T' ⟶ U, evaluate j a = evaluate i b) ↔ Set.range b.left.base ⊆ V

/-- A family of subgroup families covers the field points when every closed
torus subgroup over every field point of `S` is an evaluation of a member. -/
def CoversFieldPoints {ι : Type u} {U : ι → Over S}
    {K : ∀ k, GroupScheme (U k).left}
    (j : ∀ k, K k ⟶ (GroupScheme.baseChange (U k).hom).obj G) : Prop :=
  ∀ (F : Type u) [Field F] (x : Spec (CommRingCat.of F) ⟶ S)
    (L : GroupScheme (Spec (CommRingCat.of F)))
    (i : L ⟶ (GroupScheme.baseChange (Over.mk x).hom).obj G),
    IsClosedSubgroup i → RelativeMultiplicativeType.IsMultiplicativeType L →
    ∃ (k : ι) (a : Over.mk x ⟶ U k), evaluate (j k) a = SubgroupFunctor.range i

end Langlands.GroupScheme.MultiplicativeTypeSubgroupModuli
