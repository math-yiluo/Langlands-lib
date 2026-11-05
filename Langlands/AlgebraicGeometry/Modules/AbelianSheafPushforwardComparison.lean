import Langlands.Cohomology.AcyclicResolution.ComparisonFactorization
import Langlands.AlgebraicGeometry.Modules.AbelianSheafComparison
import Langlands.AlgebraicGeometry.Modules.ClosedImmersionHigherDirectImageVanishingProof
import Langlands.AlgebraicGeometry.Picard.UnitSheafPushforward

/-! # Actual module/sheaf comparison across a closed-immersion pushforward -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Cohomology Langlands.Cohomology.AcyclicResolution

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.Modules.AbelianSheafComparison

open PushforwardInjectiveAcyclic

variable {X Y : Scheme.{u}} (h : X ⟶ Y)

/-- Forgetting actual module scalars commutes with actual pushforward. -/
def pushforwardForgetIso :
    Scheme.Modules.pushforward h ⋙ toAbSheaf Y ≅
      toAbSheaf X ⋙ TopCat.Sheaf.pushforward AddCommGrpCat.{u} h.base :=
  NatIso.ofComponents (fun _ => Iso.refl _)

/-- Actual abelian global sections of a pushforward are the same global sections. -/
def abelianPushforwardSectionsIso :
    TopCat.Sheaf.pushforward AddCommGrpCat.{u} h.base ⋙
        AbelianSheafDerivedSections.globalSections Y.toTopCat ≅
      AbelianSheafDerivedSections.globalSections X.toTopCat :=
  NatIso.ofComponents (fun _ => Iso.refl _)

/-- The actual global sections comparison after forgetting the different scalar rings. -/
def underlyingPushforwardSectionsIso :
    Scheme.Modules.pushforward h ⋙
        (DerivedSections.globalSections Y ⋙
          forget₂ (ModuleCat.{u} Γ(Y, ⊤)) AddCommGrpCat.{u}) ≅
      DerivedSections.globalSections X ⋙
        forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u} :=
  NatIso.ofComponents (fun _ => Iso.refl _)

variable [IsClosedImmersion h] [IsIso h.base]

local instance :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} h.base).IsEquivalence :=
  (Picard.UnitSheafPushforward.sheafPushforwardEquivalence
    (C := AddCommGrpCat.{u}) (asIso h.base)).isEquivalence_functor

local instance : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} h.base).Additive :=
  Functor.additive_of_preserves_binary_products _

omit [IsClosedImmersion h] in
/-- Abelian pushforward along the underlying homeomorphism has no positive derived functors. -/
lemma isZero_rightDerived_abelianPushforward
    (F : TopCat.Sheaf AddCommGrpCat.{u} X.toTopCat) (q : ℕ) :
    IsZero (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} h.base).rightDerived (q + 1)).obj F) :=
  DerivedSections.isZero_rightDerived_succ_of_preservesHomology
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} h.base) F q

/-- The two actual module-to-abelian-sheaf pushforward routes give the same
canonical degreewise comparison, including the canonical forgetting isomorphism. -/
lemma twoStepComparison_pushforward (M : X.Modules) (n : ℕ) :
    twoStepComparison (F₁ := Scheme.Modules.pushforward h) (F₂ := toAbSheaf Y)
        (AbelianSheafDerivedSections.globalSections Y.toTopCat) (globalSectionsIso Y) (underlyingPushforwardSectionsIso h) M
        (fun q => closedImmersionHigherDirectImageVanishing X Y h inferInstance M q)
        (isZero_rightDerived_toAbSheaf Y ((Scheme.Modules.pushforward h).obj M)) n ≫
      ((AbelianSheafDerivedSections.globalSections Y.toTopCat).rightDerived n).map
        ((pushforwardForgetIso h).hom.app M) =
    twoStepComparison (F₁ := toAbSheaf X)
        (F₂ := TopCat.Sheaf.pushforward AddCommGrpCat.{u} h.base)
        (AbelianSheafDerivedSections.globalSections Y.toTopCat) (abelianPushforwardSectionsIso h) (globalSectionsIso X) M
        (isZero_rightDerived_toAbSheaf X M)
        (isZero_rightDerived_abelianPushforward h ((toAbSheaf X).obj M)) n := by
  have := ClosedImmersionHigherDirectImageVanishing.pushforward_preservesEpimorphisms h
  have : (Scheme.Modules.pushforward h).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  exact twoStepComparison_factorization
    (F₁ := Scheme.Modules.pushforward h) (F₂ := toAbSheaf Y)
    (F₁' := toAbSheaf X) (F₂' := TopCat.Sheaf.pushforward AddCommGrpCat.{u} h.base)
    (AbelianSheafDerivedSections.globalSections Y.toTopCat)
    (globalSectionsIso Y) (underlyingPushforwardSectionsIso h)
    (abelianPushforwardSectionsIso h) (globalSectionsIso X) (pushforwardForgetIso h) M
    (fun q => closedImmersionHigherDirectImageVanishing X Y h inferInstance M q)
    (isZero_rightDerived_toAbSheaf Y ((Scheme.Modules.pushforward h).obj M))
    (isZero_rightDerived_toAbSheaf X M)
    (isZero_rightDerived_abelianPushforward h ((toAbSheaf X).obj M))
    (by intro Q; ext x; rfl) n

end Langlands.AlgebraicGeometry.Modules.AbelianSheafComparison
