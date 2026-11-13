import Langlands.Sheaf.Equivariant.TwistedLeftInduction
import Langlands.Sheaf.Equivariant.TwistedGlobalSections
import Langlands.Cohomology.ExactBaseChange.ResolutionProof

/-!
# The action of `G` on the cohomology of the restriction of a twisted sheaf

Let `F` be a module sheaf on the twisted site of a `G`-object `X`. Its global sections and
its compactly supported global sections are representations of `G`, with underlying modules
the corresponding sections of the restriction `b^*F` to the site over `X`. The right derived
functors of these representation-valued functors are representations of `G`. When
coproducts of modules indexed by `G` exist and are exact, restriction is exact and sends
injective sheaves to injective sheaves, so the underlying modules of these representations
are `H^q(X, b^*F)` and `H^q_c(X, b^*F)`. This defines the action of `G` on `H^q(X, b^*F)` and
on `H^q_c(X, b^*F)`.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.TwistedOver

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Cohomology Langlands.Cohomology.AcyclicResolution Langlands.Sheaf.PointSupport

universe w v u uG uI

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C} [P.RespectsIso] {X : C}
variable {G : Type uG} [Group G] {ρ : G →* Aut X}
variable [P.ContainsIdentities]
variable (J : GrothendieckTopology (P.Over ⊤ X)) [IsTranslationInvariant (ρ := ρ) J]
variable (R : Type w) [CommRing R]

section Global

variable [HasSheafify (twistedTopology ρ J) (ModuleCat.{w} R)]
variable [EnoughInjectives (Sheaf (twistedTopology ρ J) (ModuleCat.{w} R))]

/-- The cohomology of module sheaves on the twisted site with coefficients in global
sections, as representations of `G`: the right derived functors of the global sections
representation. -/
def sheafGlobalRepDerived (q : ℕ) :
    Sheaf (twistedTopology ρ J) (ModuleCat.{w} R) ⥤ Rep.{w} R G :=
  (sheafGlobalSectionsRep J R (ρ := ρ)).rightDerived q

/-- In degree zero, it is the global sections representation. -/
def sheafGlobalRepDerivedZeroIso :
    sheafGlobalRepDerived J R (ρ := ρ) 0 ≅ sheafGlobalSectionsRep J R :=
  (sheafGlobalSectionsRep J R).rightDerivedZeroIsoSelf

/-- It is computed by any injective resolution on the twisted site. -/
def sheafGlobalRepDerivedIso {F : Sheaf (twistedTopology ρ J) (ModuleCat.{w} R)}
    (I : InjectiveResolution F) (q : ℕ) :
    (sheafGlobalRepDerived J R q).obj F ≅
      (HomologicalComplex.homologyFunctor (Rep.{w} R G) (ComplexShape.up ℕ) q).obj
        (((sheafGlobalSectionsRep J R).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          I.cocomplex) :=
  I.isoRightDerivedObj (sheafGlobalSectionsRep J R) q

/-- It vanishes in positive degrees on injective sheaves. -/
theorem isZero_sheafGlobalRepDerived_succ_of_injective
    (F : Sheaf (twistedTopology ρ J) (ModuleCat.{w} R)) [Injective F] (q : ℕ) :
    IsZero ((sheafGlobalRepDerived J R (ρ := ρ) (q + 1)).obj F) :=
  (sheafGlobalSectionsRep J R).isZero_rightDerived_obj_injective_succ q F

variable [HasSheafify J (ModuleCat.{w} R)] [EnoughInjectives (Sheaf J (ModuleCat.{w} R))]
variable [∀ F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R, (ι P ρ).op.HasPointwiseRightKanExtension F]

/-- The comparison from the module underlying the representation `sheafGlobalRepDerived` to
the cohomology `H^q(X, b^*F)` of the restriction over the base object: the base change
transformation of `sheafGlobalSectionsRepForgetIso` along the exact functors `forget₂` and
restriction. -/
def restrictionGlobalComparison (q : ℕ) :
    sheafGlobalRepDerived J R (ρ := ρ) q ⋙ forget₂ (Rep.{w} R G) (ModuleCat.{w} R) ⟶
      restriction ρ J (ModuleCat.{w} R) ⋙ sectionsDerived J R (base P ρ).obj q :=
  ExactBaseChange.baseChangeNatTrans (sheafGlobalSectionsRepForgetIso J R).hom q

variable [HasColimitsOfShape (Discrete G) (ModuleCat.{w} R)]
variable [HasExactColimitsOfShape (Discrete G) (ModuleCat.{w} R)]

/-- The comparison is an isomorphism: restriction sends an injective resolution on the
twisted site to an injective resolution over `X`. -/
theorem isIso_restrictionGlobalComparison_app (q : ℕ)
    (F : Sheaf (twistedTopology ρ J) (ModuleCat.{w} R)) :
    IsIso ((restrictionGlobalComparison J R (ρ := ρ) q).app F) := by
  let K := (injectiveResolution F).cocomplex
  have := ExactBaseChange.quasiIso_mapResolutionAugmentation (restriction ρ J (ModuleCat.{w} R))
    (injectiveResolution F).ι
  have : IsIso ((NatTrans.mapHomologicalComplex (sheafGlobalSectionsRepForgetIso J R).hom
      (ComplexShape.up ℕ)).app K) :=
    inferInstanceAs (IsIso ((NatIso.mapHomologicalComplex (sheafGlobalSectionsRepForgetIso J R)
      (ComplexShape.up ℕ)).app K).hom)
  exact ExactBaseChange.isIso_baseChangeNatTrans_app_of_acyclic
    (sheafGlobalSectionsRepForgetIso J R).hom (ε := (injectiveResolution F).ι)
    (ε' := mapResolutionAugmentation (restriction ρ J (ModuleCat.{w} R))
      (injectiveResolution F).ι)
    (ψ := 𝟙 _)
    (Φ := (NatTrans.mapHomologicalComplex (sheafGlobalSectionsRepForgetIso J R).hom
      (ComplexShape.up ℕ)).app K)
    (Category.comp_id _)
    (fun n => by simp; rfl)
    (fun n r => (sheafGlobalSectionsRep J R).isZero_rightDerived_obj_injective_succ r (K.X n))
    (fun n r => (sheafSectionsModule J R (base P ρ).obj).isZero_rightDerived_obj_injective_succ
      r ((restriction ρ J (ModuleCat.{w} R)).obj (K.X n)))
    q

/-- The module underlying `sheafGlobalRepDerived J R q` is the cohomology `H^q(X, b^*F)` of the
restriction over the base object. This defines the action of `G` on `H^q(X, b^*F)`. -/
def restrictionGlobalCohomologyIso (q : ℕ) :
    sheafGlobalRepDerived J R (ρ := ρ) q ⋙ forget₂ (Rep.{w} R G) (ModuleCat.{w} R) ≅
      restriction ρ J (ModuleCat.{w} R) ⋙ sectionsDerived J R (base P ρ).obj q :=
  haveI : ∀ F, IsIso ((restrictionGlobalComparison J R (ρ := ρ) q).app F) :=
    isIso_restrictionGlobalComparison_app J R q
  haveI : IsIso (restrictionGlobalComparison J R (ρ := ρ) q) :=
    NatIso.isIso_of_isIso_app _
  asIso (restrictionGlobalComparison J R q)

end Global

section Compact

variable {I : Type uI} [MulAction G I] {Φ : I → J.Point.{w}}
variable [LocallySmall.{w} (P.Over ⊤ X)] [TopologicalSpace I] [ContinuousConstSMul G I]
variable [HasSheafify J (ModuleCat.{w} R)] [HasSheafify (twistedTopology ρ J) (ModuleCat.{w} R)]
variable [EnoughInjectives (Sheaf (twistedTopology ρ J) (ModuleCat.{w} R))]

/-- The compactly supported cohomology of module sheaves on the twisted site, as
representations of `G`: the right derived functors of the compactly supported global
sections representation. -/
def sheafCompactRepDerived (E : PointEquivariance ρ Φ) (q : ℕ) :
    Sheaf (twistedTopology ρ J) (ModuleCat.{w} R) ⥤ Rep.{w} R G :=
  (sheafCompactSectionsRep J R E).rightDerived q

/-- In degree zero, it is the compactly supported global sections representation. -/
def sheafCompactRepDerivedZeroIso (E : PointEquivariance ρ Φ) :
    sheafCompactRepDerived J R E 0 ≅ sheafCompactSectionsRep J R E :=
  (sheafCompactSectionsRep J R E).rightDerivedZeroIsoSelf

/-- It is computed by any injective resolution on the twisted site. -/
def sheafCompactRepDerivedIso (E : PointEquivariance ρ Φ)
    {F : Sheaf (twistedTopology ρ J) (ModuleCat.{w} R)} (I : InjectiveResolution F) (q : ℕ) :
    (sheafCompactRepDerived J R E q).obj F ≅
      (HomologicalComplex.homologyFunctor (Rep.{w} R G) (ComplexShape.up ℕ) q).obj
        (((sheafCompactSectionsRep J R E).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          I.cocomplex) :=
  I.isoRightDerivedObj (sheafCompactSectionsRep J R E) q

omit [HasSheafify J (ModuleCat.{w} R)] in
/-- It vanishes in positive degrees on injective sheaves. -/
theorem isZero_sheafCompactRepDerived_succ_of_injective (E : PointEquivariance ρ Φ)
    (F : Sheaf (twistedTopology ρ J) (ModuleCat.{w} R)) [Injective F] (q : ℕ) :
    IsZero ((sheafCompactRepDerived J R E (q + 1)).obj F) :=
  (sheafCompactSectionsRep J R E).isZero_rightDerived_obj_injective_succ q F

variable [EnoughInjectives (Sheaf J (ModuleCat.{w} R))]
variable [∀ F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R, (ι P ρ).op.HasPointwiseRightKanExtension F]

/-- The comparison from the module underlying the representation `sheafCompactRepDerived` to
the compactly supported cohomology `H^q_c(X, b^*F)` of the restriction over the base object:
the base change transformation of `sheafCompactSectionsRepForgetIso` along the exact functors
`forget₂` and restriction. -/
def restrictionCompactComparison (E : PointEquivariance ρ Φ) (q : ℕ) :
    sheafCompactRepDerived J R E q ⋙ forget₂ (Rep.{w} R G) (ModuleCat.{w} R) ⟶
      restriction ρ J (ModuleCat.{w} R) ⋙ compactDerived J Φ R (base P ρ).obj q :=
  ExactBaseChange.baseChangeNatTrans (sheafCompactSectionsRepForgetIso J (R := R) E).hom q

variable [HasColimitsOfShape (Discrete G) (ModuleCat.{w} R)]
variable [HasExactColimitsOfShape (Discrete G) (ModuleCat.{w} R)]

/-- The compact comparison is an isomorphism: restriction sends an injective resolution on
the twisted site to an injective resolution over `X`. -/
theorem isIso_restrictionCompactComparison_app (E : PointEquivariance ρ Φ) (q : ℕ)
    (F : Sheaf (twistedTopology ρ J) (ModuleCat.{w} R)) :
    IsIso ((restrictionCompactComparison J R E q).app F) := by
  let K := (injectiveResolution F).cocomplex
  have := ExactBaseChange.quasiIso_mapResolutionAugmentation (restriction ρ J (ModuleCat.{w} R))
    (injectiveResolution F).ι
  have : IsIso ((NatTrans.mapHomologicalComplex (sheafCompactSectionsRepForgetIso J (R := R) E).hom
      (ComplexShape.up ℕ)).app K) :=
    inferInstanceAs (IsIso ((NatIso.mapHomologicalComplex
      (sheafCompactSectionsRepForgetIso J (R := R) E) (ComplexShape.up ℕ)).app K).hom)
  exact ExactBaseChange.isIso_baseChangeNatTrans_app_of_acyclic
    (sheafCompactSectionsRepForgetIso J (R := R) E).hom (ε := (injectiveResolution F).ι)
    (ε' := mapResolutionAugmentation (restriction ρ J (ModuleCat.{w} R))
      (injectiveResolution F).ι)
    (ψ := 𝟙 _)
    (Φ := (NatTrans.mapHomologicalComplex (sheafCompactSectionsRepForgetIso J (R := R) E).hom
      (ComplexShape.up ℕ)).app K)
    (Category.comp_id _)
    (fun n => by simp; rfl)
    (fun n r => (sheafCompactSectionsRep J R E).isZero_rightDerived_obj_injective_succ r (K.X n))
    (fun n r => (sheafCompactSections J Φ R (base P ρ).obj).isZero_rightDerived_obj_injective_succ
      r ((restriction ρ J (ModuleCat.{w} R)).obj (K.X n)))
    q

/-- The module underlying `sheafCompactRepDerived J R E q` is the compactly supported
cohomology `H^q_c(X, b^*F)` of the restriction over the base object. This defines the action
of `G` on `H^q_c(X, b^*F)`. -/
def restrictionCompactCohomologyIso (E : PointEquivariance ρ Φ) (q : ℕ) :
    sheafCompactRepDerived J R E q ⋙ forget₂ (Rep.{w} R G) (ModuleCat.{w} R) ≅
      restriction ρ J (ModuleCat.{w} R) ⋙ compactDerived J Φ R (base P ρ).obj q :=
  haveI : ∀ F, IsIso ((restrictionCompactComparison J R E q).app F) :=
    isIso_restrictionCompactComparison_app J R E q
  haveI : IsIso (restrictionCompactComparison J R E q) :=
    NatIso.isIso_of_isIso_app _
  asIso (restrictionCompactComparison J R E q)

end Compact

end Langlands.Sheaf.Equivariant.TwistedOver
