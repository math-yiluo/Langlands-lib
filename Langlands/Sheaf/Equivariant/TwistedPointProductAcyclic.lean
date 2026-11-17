import Langlands.Sheaf.Equivariant.TwistedPointProductExact
import Langlands.Cohomology.PointProductAcyclic
import Langlands.AlgebraicGeometry.Modules.HigherDirectImageOpenRestriction

/-! # Reducing restricted smooth point-product acyclicity to injective coefficients -/

noncomputable section

namespace Langlands.Sheaf.Equivariant.TwistedOver

open CategoryTheory CategoryTheory.Limits LocalActionSystem
open Langlands.Cohomology.AcyclicResolution
open Langlands.AlgebraicGeometry.Modules.DerivedSections

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
variable [HasSheafify J (ModuleCat.{w} R)]
variable [HasSheafify (twistedTopology ρ J) (ModuleCat.{w} R)]
variable [EnoughInjectives (Sheaf J (ModuleCat.{w} R))]
variable {I' : Type*} (supportPoints : I' → J.Point.{w}) [TopologicalSpace I']
variable [LocallySmall.{w} (P.Over ⊤ X)]

/-- The actual derived-composite comparison, made invertible by the displayed
injective-coefficient compact-acyclicity hypothesis. -/
def compactDerivedCoefficientRestrictedSmoothPointProductIso
    (U : P.Over ⊤ X)
    (hΓ : ∀ N : Discrete I ⥤ ModuleCat.{w} R, Injective N → ∀ q : ℕ,
      IsZero ((PointSupport.compactDerived J supportPoints R U (q + 1)).obj
        ((coefficientRestrictedSmoothPointProductFunctor ρ J L points R).obj N)))
    (M : Discrete I ⥤ ModuleCat.{w} R) (n : ℕ) :
    (((coefficientRestrictedSmoothPointProductFunctor ρ J L points R ⋙
        PointSupport.sheafCompactSections J supportPoints R U).rightDerived n).obj M) ≅
      (PointSupport.compactDerived J supportPoints R U n).obj
        ((coefficientRestrictedSmoothPointProductFunctor ρ J L points R).obj M) := by
  let T := coefficientRestrictedSmoothPointProductFunctor ρ J L points R
  let Γ := PointSupport.sheafCompactSections J supportPoints R U
  have hM : ∀ q : ℕ, IsZero ((T.rightDerived (q + 1)).obj M) :=
    isZero_rightDerived_succ_of_preservesHomology T M
  exact @asIso _ _ _ _ (compComparison Γ (Iso.refl (T ⋙ Γ)) M hM n)
    (isIso_compComparison Γ (Iso.refl (T ⋙ Γ)) M hM hΓ n)

/-- Exactness in coefficients reduces compact acyclicity to injective coefficient diagrams.
The displayed injective-coefficient vanishing is a hypothesis, not a conclusion. -/
theorem isZero_compactDerived_coefficientRestrictedSmoothPointProduct_of_injective
    (U : P.Over ⊤ X)
    (hΓ : ∀ N : Discrete I ⥤ ModuleCat.{w} R, Injective N → ∀ q : ℕ,
      IsZero ((PointSupport.compactDerived J supportPoints R U (q + 1)).obj
        ((coefficientRestrictedSmoothPointProductFunctor ρ J L points R).obj N)))
    (M : Discrete I ⥤ ModuleCat.{w} R) (q : ℕ) :
    IsZero ((PointSupport.compactDerived J supportPoints R U (q + 1)).obj
      ((coefficientRestrictedSmoothPointProductFunctor ρ J L points R).obj M)) := by
  let T := coefficientRestrictedSmoothPointProductFunctor ρ J L points R
  let Γ := PointSupport.sheafCompactSections J supportPoints R U
  exact (isZero_rightDerived_succ_of_preservesHomology (T ⋙ Γ) M q).of_iso
    (compactDerivedCoefficientRestrictedSmoothPointProductIso
      ρ J L points R supportPoints U hΓ M (q + 1)).symm

end Langlands.Sheaf.Equivariant.TwistedOver
