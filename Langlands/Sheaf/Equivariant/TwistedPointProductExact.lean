import Langlands.Sheaf.Equivariant.TwistedPointProductSetSections
import Langlands.Sheaf.Equivariant.TwistedCompactSupport
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-! # Exactness of actual restricted locally discrete point products -/

noncomputable section

namespace Langlands.Sheaf.Equivariant.TwistedOver

open CategoryTheory CategoryTheory.Limits Opposite LocalActionSystem

universe v u uG w

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C} [P.RespectsIso]
variable {X : C} {G : Type uG} [Group G] [TopologicalSpace G] (ρ : G →* Aut X)
variable (J : GrothendieckTopology (P.Over ⊤ X)) [IsTranslationInvariant (ρ := ρ) J]
variable (L : LocalActionSystem (TwistedOver P ρ) G)
variable [L.HasAdmissibleRefinements (twistedTopology ρ J)]
variable {I : Type w} (points : I → J.Point.{w})
variable (R : Type w) [CommRing R]
variable [∀ F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R,
  (ι P ρ).op.HasPointwiseRightKanExtension F]

/-- The actual restricted smooth point product, with coefficients as discrete diagrams. -/
def coefficientRestrictedSmoothPointProductFunctor :
    (Discrete I ⥤ ModuleCat.{w} R) ⥤ Sheaf J (ModuleCat.{w} R) :=
  (piEquivalenceFunctorDiscrete I (ModuleCat.{w} R)).inverse ⋙
    restrictedSmoothPointProductFunctor ρ J L points R

variable [HasSheafify J (ModuleCat.{w} R)]
variable [HasSheafify (twistedTopology ρ J) (ModuleCat.{w} R)]

/-- Right adjoints and the exact smooth inclusion give left exactness of this composite. -/
instance coefficientRestrictedSmoothPointProductFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (coefficientRestrictedSmoothPointProductFunctor ρ J L points R) := by
  let := (smoothAdjunction L (twistedTopology ρ J) (R := R)).isRightAdjoint
  dsimp [coefficientRestrictedSmoothPointProductFunctor,
    restrictedSmoothPointProductFunctor, smoothPointProductFunctor]
  infer_instance

instance coefficientRestrictedSmoothPointProductFunctor_additive :
    (coefficientRestrictedSmoothPointProductFunctor ρ J L points R).Additive :=
  Functor.additive_of_preserves_binary_products _

omit [HasSheafify J (ModuleCat.{w} R)]
  [HasSheafify (twistedTopology ρ J) (ModuleCat.{w} R)] in
/-- Coefficient epimorphisms lift on every ordinary section module. -/
theorem coefficientRestrictedSmoothPointProductFunctor_map_app_surjective
    {M N : Discrete I ⥤ ModuleCat.{w} R} (f : M ⟶ N) [Epi f]
    (U : (P.Over ⊤ X)ᵒᵖ) :
    Function.Surjective
      (((coefficientRestrictedSmoothPointProductFunctor ρ J L points R).map f).hom.app U) :=
  restrictedSmoothPointProduct_map_app_surjective ρ J L points (fun i => f.app ⟨i⟩)
    (fun i => (ModuleCat.epi_iff_surjective (f.app ⟨i⟩)).mp inferInstance) U

/-- The actual restricted smooth point product preserves coefficient epimorphisms. -/
instance coefficientRestrictedSmoothPointProductFunctor_preservesEpimorphisms :
    (coefficientRestrictedSmoothPointProductFunctor ρ J L points R).PreservesEpimorphisms where
  preserves f _ := by
    apply (sheafToPresheaf J (ModuleCat.{w} R)).epi_of_epi_map
    change Epi (((coefficientRestrictedSmoothPointProductFunctor ρ J L points R).map f).hom)
    have : ∀ U, Epi
        (((coefficientRestrictedSmoothPointProductFunctor ρ J L points R).map f).hom.app U) :=
      fun U => (ModuleCat.epi_iff_surjective _).mpr
        (coefficientRestrictedSmoothPointProductFunctor_map_app_surjective ρ J L points R f U)
    exact NatTrans.epi_of_epi_app _

/-- The actual restricted smooth point product is exact in its coefficient diagram. -/
instance coefficientRestrictedSmoothPointProductFunctor_preservesHomology :
    (coefficientRestrictedSmoothPointProductFunctor ρ J L points R).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

variable {I' : Type*} (supportPoints : I' → J.Point.{w}) [TopologicalSpace I']
variable [LocallySmall.{w} (P.Over ⊤ X)]

/-- Compact sections of the actual restricted smooth point product preserve coefficient epis. -/
instance coefficientRestrictedSmoothPointProductFunctor_compactSections_preservesEpimorphisms
    (U : P.Over ⊤ X) :
    (coefficientRestrictedSmoothPointProductFunctor ρ J L points R ⋙
      PointSupport.sheafCompactSections J supportPoints R U).PreservesEpimorphisms where
  preserves f _ := by
    apply (ModuleCat.epi_iff_surjective _).mpr
    exact restrictedSmoothPointProduct_compactSections_map_surjective ρ J L points supportPoints
      (fun i => f.app ⟨i⟩)
      (fun i => (ModuleCat.epi_iff_surjective (f.app ⟨i⟩)).mp inferInstance) U

/-- The actual compact-section composite is exact in the independent coefficients. -/
instance coefficientRestrictedSmoothPointProductFunctor_compactSections_preservesHomology
    (U : P.Over ⊤ X) :
    (coefficientRestrictedSmoothPointProductFunctor ρ J L points R ⋙
      PointSupport.sheafCompactSections J supportPoints R U).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

end Langlands.Sheaf.Equivariant.TwistedOver
