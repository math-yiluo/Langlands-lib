import Langlands.Cohomology.AcyclicResolution.DerivedCompositeComparison

/-! # Isomorphism criterion for the actual derived composite comparison -/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Cohomology.AcyclicResolution

universe w w' w'' v v' v'' u u' u''

/-- The actual derived composite comparison is an isomorphism when the second
functor is left exact and the first sends injectives to acyclic objects. -/
def DerivedCompositeIsomorphismStatement : Prop :=
  ∀ (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] [EnoughInjectives C]
    (D : Type u') [Category.{v'} D] [Abelian D]
    [HasDerivedCategory.{w'} D] [EnoughInjectives D]
    (E : Type u'') [Category.{v''} E] [Abelian E] [HasDerivedCategory.{w''} E]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (G : D ⥤ E) [G.Additive] [PreservesFiniteLimits G]
    (H : C ⥤ E) [H.Additive] (e : F ⋙ G ≅ H)
    (A : C) (hA : ∀ q : ℕ, IsZero ((F.rightDerived (q + 1)).obj A)),
    (∀ J : C, Injective J → ∀ q : ℕ,
      IsZero ((G.rightDerived (q + 1)).obj (F.obj J))) →
    IsIso (derivedCompComparison G e A hA)

end Langlands.Cohomology.AcyclicResolution
