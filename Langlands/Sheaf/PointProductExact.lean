import Langlands.Sheaf.PointProductSetSections
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-! # Exactness and injective preservation for actual point products -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Sheaf.PointProduct

open CategoryTheory CategoryTheory.Limits Opposite

universe wI w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {I : Type wI} (points : I → J.Point.{max wI w})
variable (R : Type (max wI w)) [CommRing R]

private local instance : HasProducts.{wI} (ModuleCat.{max wI w} R) := by
  let := hasLimitsOfSizeShrink.{wI, wI} (ModuleCat.{max wI w} R)
  infer_instance

/-- Actual point products, with independent coefficients presented as discrete diagrams. -/
def coefficientProductFunctor :
    (Discrete I ⥤ ModuleCat.{max wI w} R) ⥤ Sheaf J (ModuleCat.{max wI w} R) :=
  (piEquivalenceFunctorDiscrete I (ModuleCat.{max wI w} R)).inverse ⋙
    productFunctor points (ModuleCat.{max wI w} R)

/-- The actual site fibers, collected as a discrete coefficient diagram. -/
def coefficientFiberFunctor :
    Sheaf J (ModuleCat.{max wI w} R) ⥤ (Discrete I ⥤ ModuleCat.{max wI w} R) :=
  fiberFunctor points (ModuleCat.{max wI w} R) ⋙
    (piEquivalenceFunctorDiscrete I (ModuleCat.{max wI w} R)).functor

/-- Reindexing independent coefficient families retains the actual fiber adjunction. -/
def coefficientAdjunction :
    coefficientFiberFunctor points R ⊣ coefficientProductFunctor points R :=
  (adjunction points (ModuleCat.{max wI w} R)).comp
    (piEquivalenceFunctorDiscrete I (ModuleCat.{max wI w} R)).toAdjunction

instance coefficientProductFunctor_isRightAdjoint :
    (coefficientProductFunctor points R).IsRightAdjoint :=
  (coefficientAdjunction points R).isRightAdjoint

variable [HasSheafify J (ModuleCat.{max wI w} R)]

/-- The coefficient product functor is additive, as a functor preserving finite limits. -/
instance coefficientProductFunctor_additive : (coefficientProductFunctor points R).Additive :=
  Functor.additive_of_preserves_binary_products _

omit [HasSheafify J (ModuleCat.{max wI w} R)] in
/-- Coefficientwise surjections are surjective on every section of the actual product sheaf. -/
theorem coefficientProductFunctor_map_surjective
    {M N : Discrete I ⥤ ModuleCat.{max wI w} R} (f : M ⟶ N) [Epi f] (U : Cᵒᵖ) :
    Function.Surjective (((coefficientProductFunctor points R).map f).hom.app U) := by
  have hf : ∀ i, Function.Surjective (f.app ⟨i⟩) :=
    fun i => (ModuleCat.epi_iff_surjective (f.app ⟨i⟩)).mp inferInstance
  intro s
  refine ⟨(setSection points (fun i => f.app ⟨i⟩) hf).app U s, ?_⟩
  exact productFunctor_map_setSection points (fun i => f.app ⟨i⟩) hf U s

/-- Products of skyscrapers preserve epimorphisms of coefficient diagrams. -/
instance coefficientProductFunctor_preservesEpimorphisms :
    (coefficientProductFunctor points R).PreservesEpimorphisms where
  preserves f _ := by
    apply (sheafToPresheaf J (ModuleCat.{max wI w} R)).epi_of_epi_map
    change Epi (((coefficientProductFunctor points R).map f).hom)
    have : ∀ U, Epi (((coefficientProductFunctor points R).map f).hom.app U) :=
      fun U => (ModuleCat.epi_iff_surjective _).mpr
        (coefficientProductFunctor_map_surjective points R f U)
    exact NatTrans.epi_of_epi_app _

/-- The actual product functor on coefficient diagrams is exact. -/
instance coefficientProductFunctor_preservesHomology :
    (coefficientProductFunctor points R).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

variable [LocallySmall.{max wI w} C]

/-- Left exactness of actual site fibers gives preservation of monomorphisms. -/
instance coefficientFiberFunctor_preservesMonomorphisms :
    (coefficientFiberFunctor points R).PreservesMonomorphisms where
  preserves f _ := by
    have : ∀ i, Mono (((coefficientFiberFunctor points R).map f).app i) := by
      intro i
      change Mono ((points i.as).sheafFiber.map f)
      infer_instance
    exact NatTrans.mono_of_mono_app _

/-- Products of skyscrapers of an injective coefficient diagram are injective sheaves. -/
instance coefficientProductFunctor_preservesInjectiveObjects :
    (coefficientProductFunctor points R).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (coefficientAdjunction points R)

variable [TopologicalSpace I]

/-- The actual compact-sections composite preserves epimorphisms of coefficients. -/
instance coefficientProductFunctor_compactSections_preservesEpimorphisms (X : C) :
    (coefficientProductFunctor points R ⋙
      PointSupport.sheafCompactSections J points R X).PreservesEpimorphisms where
  preserves f _ := by
    apply (ModuleCat.epi_iff_surjective _).mpr
    exact compactSections_map_surjective_of_coefficients points
      (fun i => f.app ⟨i⟩)
      (fun i => (ModuleCat.epi_iff_surjective (f.app ⟨i⟩)).mp inferInstance) X

/-- Compact sections of actual point products form an exact functor of coefficients. -/
instance coefficientProductFunctor_compactSections_preservesHomology (X : C) :
    (coefficientProductFunctor points R ⋙
      PointSupport.sheafCompactSections J points R X).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

end Langlands.Sheaf.PointProduct
