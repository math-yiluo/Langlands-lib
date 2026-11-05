import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import Langlands.Cohomology.RightDerivedSequence

/-! # Cohomology of successive quotients in a filtration -/

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Cohomology.QuotientFiltration

variable {C : Type u} [Category.{v} C] [Abelian C]
  {A B M : C} (a : A ⟶ B) (b : B ⟶ M)

/-- The canonical sequence `B/A ⟶ M/A ⟶ M/B`, using categorical cokernels. -/
abbrev quotientSequence : ShortComplex C :=
  (kernelCokernelCompSequence_exact a b).sc 3

@[reassoc (attr := simp)]
lemma quotientSequence_f :
    cokernel.π a ≫ (quotientSequence a b).f = b ≫ cokernel.π (a ≫ b) := by
  exact cokernel.π_desc _ _ _

@[reassoc (attr := simp)]
lemma quotientSequence_g :
    cokernel.π (a ≫ b) ≫ (quotientSequence a b).g = cokernel.π b := by
  simpa using cokernel.π_desc (a ≫ b) _ _

/-- If `B ⟶ M` is monic, the quotient sequence is short exact. -/
lemma quotientSequence_shortExact [Mono b] : (quotientSequence a b).ShortExact := by
  have hm : Mono (quotientSequence a b).f := by
    exact ((kernelCokernelCompSequence_exact a b).exact 2).mono_g
      ((isZero_kernel_of_mono b).eq_of_src _ _)
  have he : Epi (quotientSequence a b).g :=
    epi_of_epi_fac (quotientSequence_g a b)
  exact ShortComplex.ShortExact.mk'
    ((kernelCokernelCompSequence_exact a b).exact 3) hm he

section Derived

universe w w' v' u'

variable [HasDerivedCategory.{w} C] [EnoughInjectives C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]

/-- Vanishing of the first cohomology of the layer makes the quotient map
epimorphic after applying a left exact functor. -/
lemma epi_map_quotientSequence_g [Mono b]
    (h : IsZero ((F.rightDerived 1).obj (cokernel a))) :
    Epi (F.map (quotientSequence a b).g) := by
  exact (DerivedPlus.shortExact_map_of_isZero_rightDerived_one F
    (quotientSequence_shortExact a b) h).epi_g

/-- Vanishing in a fixed degree passes from a layer and the previous quotient
to the next quotient. -/
lemma isZero_quotient_middle [Mono b] (i : ℕ)
    (hlayer : IsZero ((F.rightDerived i).obj (cokernel a)))
    (hquotient : IsZero ((F.rightDerived i).obj (cokernel b))) :
    IsZero ((F.rightDerived i).obj (cokernel (a ≫ b))) := by
  exact (DerivedPlus.rightDerived_exact₂ F
    (quotientSequence_shortExact a b) i).isZero_X₂_iff.2
      ⟨hlayer.eq_of_src _ _, hquotient.eq_of_tgt _ _⟩

end Derived

end Langlands.Cohomology.QuotientFiltration
