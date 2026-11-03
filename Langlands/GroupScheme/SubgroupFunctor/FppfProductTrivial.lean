import Langlands.GroupScheme.SubgroupFunctor.FppfProduct
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent

/-! # Trivial factors in represented fppf-local subgroup products -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor

variable {S : Scheme.{u}} {G H P : GroupScheme S}

/-- Membership in a subgroup functor can be checked after a flat surjective
morphism of test schemes locally of finite presentation. -/
def IsFppfSaturated (F : SubgroupFunctor G) : Prop :=
  ∀ {T V : Over S} (v : V ⟶ T), Flat v.left → Surjective v.left →
    LocallyOfFinitePresentation v.left → ∀ x : T ⟶ G.X,
      v ≫ x ∈ F.carrier V → x ∈ F.carrier T

/-- A subgroup represented by a monomorphism has fppf-local membership. -/
theorem IsRepresentedBy.isFppfSaturated {F : SubgroupFunctor G} {i : H ⟶ G}
    (hi : F.IsRepresentedBy i) : F.IsFppfSaturated := by
  have : Mono i.hom.hom := hi.1
  rw [← hi.2]
  intro T V v hf hs hl x hx
  have : Flat v.left := hf
  have : Surjective v.left := hs
  have : LocallyOfFinitePresentation v.left := hl
  exact mem_range_of_comp_mem_range i v hx

namespace FppfLocallyInProduct

/-- A functor with fppf-local membership is unchanged by a trivial right
factor in the local product. -/
theorem right_bot_iff {F : SubgroupFunctor G} (hF : F.IsFppfSaturated)
    {T : Over S} {x : T ⟶ G.X} :
    FppfLocallyInProduct F ⊥ x ↔ x ∈ F.carrier T := by
  constructor
  · rintro ⟨V, v, hf, hs, hl, p, n, hp, hn, he⟩
    have hn' : n = 1 := by simpa only [bot_carrier, Subgroup.mem_bot] using hn
    exact hF v hf hs hl x (by simpa only [he, hn', mul_one] using hp)
  · exact of_left

/-- The same membership law with the trivial factor on the left. -/
theorem left_bot_iff {F : SubgroupFunctor G} (hF : F.IsFppfSaturated)
    {T : Over S} {x : T ⟶ G.X} :
    FppfLocallyInProduct ⊥ F x ↔ x ∈ F.carrier T := by
  constructor
  · rintro ⟨V, v, hf, hs, hl, p, n, hp, hn, he⟩
    have hp' : p = 1 := by simpa only [bot_carrier, Subgroup.mem_bot] using hp
    exact hF v hf hs hl x (by simpa only [he, hp', one_mul] using hn)
  · exact of_right

/-- Fppf-local multiplication by the trivial subgroup does not enlarge a
subgroup represented by a monomorphism. -/
theorem range_bot_iff (i : H ⟶ G) [Mono i.hom.hom]
    {T : Over S} {x : T ⟶ G.X} :
    FppfLocallyInProduct (range i) ⊥ x ↔ x ∈ (range i).carrier T :=
  right_bot_iff (IsRepresentedBy.isFppfSaturated ⟨inferInstance, rfl⟩)

/-- The trivial left factor likewise does not enlarge a represented subgroup. -/
theorem bot_range_iff (i : H ⟶ G) [Mono i.hom.hom]
    {T : Over S} {x : T ⟶ G.X} :
    FppfLocallyInProduct ⊥ (range i) x ↔ x ∈ (range i).carrier T :=
  left_bot_iff (IsRepresentedBy.isFppfSaturated ⟨inferInstance, rfl⟩)

end FppfLocallyInProduct

namespace IsFppfProduct

/-- A closed subgroup represents its product with the trivial right factor. -/
theorem range_bot (i : H ⟶ G) (hi : IsClosedSubgroup i) :
    IsFppfProduct (range i) ⊥ i := by
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  exact ⟨hi, fun _ _ => (FppfLocallyInProduct.range_bot_iff i).symm⟩

/-- A closed subgroup represents its product with the trivial left factor. -/
theorem bot_range (i : H ⟶ G) (hi : IsClosedSubgroup i) :
    IsFppfProduct ⊥ (range i) i := by
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  exact ⟨hi, fun _ _ => (FppfLocallyInProduct.bot_range_iff i).symm⟩

/-- The all-test image of a represented product with the trivial right factor
is its left factor, when that factor is represented by a monomorphism. -/
theorem range_eq_left_of_right_eq_bot {F N : SubgroupFunctor G} {i : H ⟶ G}
    {j : P ⟶ G} (hprod : IsFppfProduct F N j)
    (hi : F.IsRepresentedBy i) (hN : N = ⊥) : range j = F := by
  have : Mono i.hom.hom := hi.1
  apply ext
  intro T
  apply Subgroup.ext
  intro x
  rw [hprod.mem_range_iff, hN, ← hi.2]
  exact FppfLocallyInProduct.range_bot_iff i

/-- The corresponding image equality for a trivial left factor. -/
theorem range_eq_right_of_left_eq_bot {F N : SubgroupFunctor G} {i : H ⟶ G}
    {j : P ⟶ G} (hprod : IsFppfProduct F N j)
    (hi : N.IsRepresentedBy i) (hF : F = ⊥) : range j = N := by
  have : Mono i.hom.hom := hi.1
  apply ext
  intro T
  apply Subgroup.ext
  intro x
  rw [hprod.mem_range_iff, hF, ← hi.2]
  exact FppfLocallyInProduct.bot_range_iff i

end IsFppfProduct

end Langlands.GroupScheme.SubgroupFunctor
