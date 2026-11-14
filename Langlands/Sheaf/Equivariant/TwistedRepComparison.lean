import Langlands.Sheaf.Equivariant.TwistedExactGlobalComparison
import Langlands.Sheaf.Equivariant.TwistedRepCohomology
import Langlands.Cohomology.ExactBaseChange.Paste

/-!
# The comparison maps through the cohomology of the restriction as a representation

Let `𝒜` be an abelian category with an exact additive functor `incl` to module sheaves on the
twisted site of a `G`-object `X`. The comparison maps `H^q(X{G}, incl F) → H^q(X, b^*incl F)`
and `H^q_c(X{G}, incl F) → H^q_c(X, b^*incl F)` of `TwistedExactGlobalComparison` and
`TwistedExactCompactComparison` are maps of modules. The modules `H^q(X, b^*F)` and
`H^q_c(X, b^*F)` carry the action of `G` of `TwistedRepCohomology`, through the
representation-valued derived functors `sheafGlobalRepDerived` and `sheafCompactRepDerived`.

This module factors the comparison maps through these representations. The inclusion of the
smooth part into the global sections representation gives a morphism of representations
`exactGlobalRepComparison : H^q(X{G}, F) → (sheafGlobalRepDerived q)(incl F)`, and the
comparison map of modules is this morphism followed by `restrictionGlobalComparison`
(`exactGlobalComparison_app_eq`). Consequently the comparison map carries the action of `g`
on `H^q(X{G}, F)` to the action of `g` on the representation
(`exactGlobalComparison_app_representation`). The same holds with compact supports.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.TwistedOver

open CategoryTheory CategoryTheory.Limits
open Langlands.Sheaf.PointSupport
open Langlands.Cohomology

universe w u v uG uI uA vA

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C} [P.RespectsIso] {X : C}
variable {G : Type uG} [Group G] {ρ : G →* Aut X}
variable [P.ContainsIdentities]
variable (J : GrothendieckTopology (P.Over ⊤ X)) [IsTranslationInvariant (ρ := ρ) J]
variable (R : Type w) [CommRing R]
variable [TopologicalSpace G] [IsTopologicalGroup G]
variable {𝒜 : Type uA} [Category.{vA} 𝒜]
variable (incl : 𝒜 ⥤ Sheaf (twistedTopology ρ J) (ModuleCat.{w} R))

section Global

/-- The inclusion of the smooth global sections of `incl F` into the global sections
representation, as a morphism of representations: the counit of the smooth-part
adjunction. -/
def exactGlobalRepInclusion :
    exactGlobalSections J R incl ⋙ SmoothRep.toRep ⟶ incl ⋙ sheafGlobalSectionsRep J R where
  app F := (SmoothRep.toRepSmoothPartAdjunction R G).counit.app
    ((sheafGlobalSectionsRep J R).obj (incl.obj F))
  naturality _ _ f := (SmoothRep.toRepSmoothPartAdjunction R G).counit.naturality
    ((sheafGlobalSectionsRep J R).map (incl.map f))

/-- The inclusion of smooth global sections into the sections over the base object is the
inclusion into the global sections representation, followed by the identification of its
underlying module. -/
theorem exactGlobalInclusion_eq_paste :
    exactGlobalInclusion J R incl =
      ExactBaseChange.pasteNatTrans (exactGlobalRepInclusion J R incl)
        (sheafGlobalSectionsRepForgetIso J R).hom := by
  refine NatTrans.ext (funext fun F => ?_)
  exact (Category.comp_id ((exactGlobalInclusion J R incl).app F)).symm

variable [Abelian 𝒜] [incl.Additive] [PreservesFiniteLimits incl] [PreservesFiniteColimits incl]
variable [EnoughInjectives 𝒜]
variable [HasSheafify (twistedTopology ρ J) (ModuleCat.{w} R)]
variable [EnoughInjectives (Sheaf (twistedTopology ρ J) (ModuleCat.{w} R))]

/-- The map of representations `H^q(X{G}, incl F) → (sheafGlobalRepDerived q)(incl F)` in
degree `q`: the base change transformation of `exactGlobalRepInclusion` along the exact
functors `SmoothRep.toRep` and `incl`. -/
def exactGlobalRepComparison (q : ℕ) :
    exactGlobalDerived J R incl q ⋙ SmoothRep.toRep ⟶ incl ⋙ sheafGlobalRepDerived J R q :=
  ExactBaseChange.baseChangeNatTrans (exactGlobalRepInclusion J R incl) q

variable [HasSheafify J (ModuleCat.{w} R)] [EnoughInjectives (Sheaf J (ModuleCat.{w} R))]
variable [∀ F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R, (ι P ρ).op.HasPointwiseRightKanExtension F]

/-- The comparison map `H^q(X{G}, incl F) → H^q(X, b^*incl F)` factors as the map of
representations `exactGlobalRepComparison`, followed by `restrictionGlobalComparison`. -/
theorem exactGlobalComparison_app_eq (q : ℕ) (F : 𝒜) :
    (exactGlobalComparison J R incl q).app F =
      (forget₂ (Rep.{w} R G) (ModuleCat.{w} R)).map
          ((exactGlobalRepComparison J R incl q).app F) ≫
        (restrictionGlobalComparison J R q).app (incl.obj F) := by
  rw [exactGlobalComparison, exactGlobalInclusion_eq_paste]
  exact ExactBaseChange.baseChangeNatTrans_paste_app _ _ q F

/-- The factorization of `exactGlobalComparison_app_eq`, on elements. -/
theorem exactGlobalComparison_app_apply (q : ℕ) (F : 𝒜)
    (x : (exactGlobalDerived J R incl q ⋙ smoothForget R G).obj F) :
    ((exactGlobalComparison J R incl q).app F).hom x =
      ((restrictionGlobalComparison J R q).app (incl.obj F)).hom
        (((exactGlobalRepComparison J R incl q).app F).hom x) := by
  rw [exactGlobalComparison_app_eq]
  rfl

/-- The comparison map carries the action of `g` on `H^q(X{G}, incl F)` to the action of `g`
on `(sheafGlobalRepDerived q)(incl F)`. -/
theorem exactGlobalComparison_app_representation (q : ℕ) (F : 𝒜) (g : G)
    (x : (exactGlobalDerived J R incl q ⋙ smoothForget R G).obj F) :
    ((exactGlobalComparison J R incl q).app F).hom
        (((exactGlobalDerived J R incl q).obj F).representation g x) =
      ((restrictionGlobalComparison J R q).app (incl.obj F)).hom
        (((sheafGlobalRepDerived J R q).obj (incl.obj F)).ρ g
          (((exactGlobalRepComparison J R incl q).app F).hom x)) := by
  rw [exactGlobalComparison_app_apply]
  exact congrArg _ (Rep.hom_comm_apply ((exactGlobalRepComparison J R incl q).app F) g x)

end Global

section Compact

variable {I : Type uI} [MulAction G I] {Φ : I → J.Point.{w}}
variable [LocallySmall.{w} (P.Over ⊤ X)] [TopologicalSpace I] [ContinuousConstSMul G I]

/-- The inclusion of the smooth compactly supported global sections of `incl F` into the
compactly supported global sections representation, as a morphism of representations: the
counit of the smooth-part adjunction. -/
def exactCompactRepInclusion (E : PointEquivariance ρ Φ) :
    exactCompactSections J R incl E ⋙ SmoothRep.toRep ⟶ incl ⋙ sheafCompactSectionsRep J R E where
  app F := (SmoothRep.toRepSmoothPartAdjunction R G).counit.app
    ((sheafCompactSectionsRep J R E).obj (incl.obj F))
  naturality _ _ f := (SmoothRep.toRepSmoothPartAdjunction R G).counit.naturality
    ((sheafCompactSectionsRep J R E).map (incl.map f))

/-- The inclusion of smooth compactly supported global sections into the compactly supported
sections over the base object is the inclusion into the compactly supported global sections
representation, followed by the identification of its underlying module. -/
theorem exactCompactInclusion_eq_paste (E : PointEquivariance ρ Φ) :
    exactCompactInclusion J R incl E =
      ExactBaseChange.pasteNatTrans (exactCompactRepInclusion J R incl E)
        (sheafCompactSectionsRepForgetIso J (R := R) E).hom := by
  refine NatTrans.ext (funext fun F => ?_)
  exact (Category.comp_id ((exactCompactInclusion J R incl E).app F)).symm

variable [Abelian 𝒜] [incl.Additive] [PreservesFiniteLimits incl] [PreservesFiniteColimits incl]
variable [EnoughInjectives 𝒜]
variable [HasSheafify J (ModuleCat.{w} R)] [HasSheafify (twistedTopology ρ J) (ModuleCat.{w} R)]
variable [EnoughInjectives (Sheaf (twistedTopology ρ J) (ModuleCat.{w} R))]

/-- The map of representations `H^q_c(X{G}, incl F) → (sheafCompactRepDerived q)(incl F)` in
degree `q`: the base change transformation of `exactCompactRepInclusion` along the exact
functors `SmoothRep.toRep` and `incl`. -/
def exactCompactRepComparison (E : PointEquivariance ρ Φ) (q : ℕ) :
    exactCompactDerived J R incl E q ⋙ SmoothRep.toRep ⟶
      incl ⋙ sheafCompactRepDerived J R E q :=
  ExactBaseChange.baseChangeNatTrans (exactCompactRepInclusion J R incl E) q

variable [EnoughInjectives (Sheaf J (ModuleCat.{w} R))]
variable [∀ F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R, (ι P ρ).op.HasPointwiseRightKanExtension F]

/-- The comparison map `H^q_c(X{G}, incl F) → H^q_c(X, b^*incl F)` factors as the map of
representations `exactCompactRepComparison`, followed by `restrictionCompactComparison`. -/
theorem exactCompactComparison_app_eq (E : PointEquivariance ρ Φ) (q : ℕ) (F : 𝒜) :
    (exactCompactComparison J R incl E q).app F =
      (forget₂ (Rep.{w} R G) (ModuleCat.{w} R)).map
          ((exactCompactRepComparison J R incl E q).app F) ≫
        (restrictionCompactComparison J R E q).app (incl.obj F) := by
  rw [exactCompactComparison, exactCompactInclusion_eq_paste]
  exact ExactBaseChange.baseChangeNatTrans_paste_app _ _ q F

/-- The factorization of `exactCompactComparison_app_eq`, on elements. -/
theorem exactCompactComparison_app_apply (E : PointEquivariance ρ Φ) (q : ℕ) (F : 𝒜)
    (x : (exactCompactDerived J R incl E q ⋙ smoothForget R G).obj F) :
    ((exactCompactComparison J R incl E q).app F).hom x =
      ((restrictionCompactComparison J R E q).app (incl.obj F)).hom
        (((exactCompactRepComparison J R incl E q).app F).hom x) := by
  rw [exactCompactComparison_app_eq]
  rfl

/-- The compact comparison map carries the action of `g` on `H^q_c(X{G}, incl F)` to the
action of `g` on `(sheafCompactRepDerived q)(incl F)`. -/
theorem exactCompactComparison_app_representation (E : PointEquivariance ρ Φ) (q : ℕ) (F : 𝒜)
    (g : G) (x : (exactCompactDerived J R incl E q ⋙ smoothForget R G).obj F) :
    ((exactCompactComparison J R incl E q).app F).hom
        (((exactCompactDerived J R incl E q).obj F).representation g x) =
      ((restrictionCompactComparison J R E q).app (incl.obj F)).hom
        (((sheafCompactRepDerived J R E q).obj (incl.obj F)).ρ g
          (((exactCompactRepComparison J R incl E q).app F).hom x)) := by
  rw [exactCompactComparison_app_apply]
  exact congrArg _ (Rep.hom_comm_apply ((exactCompactRepComparison J R incl E q).app F) g x)

end Compact

end Langlands.Sheaf.Equivariant.TwistedOver
