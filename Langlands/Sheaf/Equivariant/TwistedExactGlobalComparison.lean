import Langlands.Sheaf.Equivariant.TwistedGlobalSections
import Langlands.Sheaf.Equivariant.TwistedExactCompactComparison

/-!
# Global comparison maps for exact abelian subcategories of twisted sheaves

Let `G` act on an object `X`, and let `J` be a translation-invariant topology on the
site over `X`. The published module `TwistedGlobalSections` constructs, for the discrete
sheaves of a local action system, Berkovich's smooth global sections `Γ_{X{G}}`, their
right derived functors `H^q(X{G}, -)` and the comparison maps
`H^q(X{G}, F) → H^q(X, b^*F)`. Those constructions use only that discrete sheaves form an
abelian category with enough injectives whose inclusion into module sheaves on the
twisted site is exact.

This module repeats them for an arbitrary abelian category `𝒜` with an exact additive
functor `incl` to module sheaves on the twisted site, as `TwistedExactCompactComparison`
does for compact supports. It also adds the invariant global sections `Γ_{X(G)}`, their
derived functors `H^q(X(G), -)` and the edge maps `H^q(X(G), F) → H^q(X{G}, F)^G`.
The locally discrete sheaves of `LocalActionSmoothPart`, among them Berkovich's étale
`G`-sheaves, are an instance.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.TwistedOver

open CategoryTheory CategoryTheory.Limits
open Langlands.Cohomology

universe w u v uG uA vA

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C} [P.RespectsIso] {X : C}
variable {G : Type uG} [Group G] {ρ : G →* Aut X}
variable [P.ContainsIdentities]
variable (J : GrothendieckTopology (P.Over ⊤ X)) [IsTranslationInvariant (ρ := ρ) J]
variable (R : Type w) [CommRing R]
variable [TopologicalSpace G] [IsTopologicalGroup G]

section Sheaves

/-- The inclusion of the smooth global sections of a module sheaf on the twisted site into
the sections over the base object of its restriction to the site over `X`: the counit of
the smooth-part adjunction. -/
def sheafSmoothGlobalInclusion :
    sheafGlobalSectionsSmooth J R (ρ := ρ) ⋙ smoothForget R G ⟶
      restriction ρ J (ModuleCat.{w} R) ⋙ sheafSectionsModule J R (base P ρ).obj where
  app F := (forget₂ (Rep.{w} R G) (ModuleCat.{w} R)).map
    ((SmoothRep.toRepSmoothPartAdjunction R G).counit.app ((sheafGlobalSectionsRep J R).obj F))
  naturality F F' f := by
    have h := (SmoothRep.toRepSmoothPartAdjunction R G).counit.naturality
      ((sheafGlobalSectionsRep J R).map f)
    exact ((forget₂ (Rep.{w} R G) (ModuleCat.{w} R)).map_comp _ _).symm.trans
      (((forget₂ (Rep.{w} R G) (ModuleCat.{w} R)).congr_map h).trans
        ((forget₂ (Rep.{w} R G) (ModuleCat.{w} R)).map_comp _ _))

/-- A smooth global section is sent to itself. -/
theorem sheafSmoothGlobalInclusion_app_apply (F : Sheaf (twistedTopology ρ J) (ModuleCat.{w} R))
    (s : ((sheafGlobalSectionsSmooth J R ⋙ smoothForget R G).obj F)) :
    ((sheafSmoothGlobalInclusion J R).app F).hom s = s.1 := rfl

end Sheaves

variable {𝒜 : Type uA} [Category.{vA} 𝒜]
variable (incl : 𝒜 ⥤ Sheaf (twistedTopology ρ J) (ModuleCat.{w} R))

section Functors

/-- Smooth global sections on `𝒜`, the shape of Berkovich's `Γ_{X{G}}`: `incl` followed by
the smooth part of the global sections representation. -/
def exactGlobalSections : 𝒜 ⥤ SmoothRep.{w, uG, w} R G :=
  incl ⋙ sheafGlobalSectionsSmooth J R

instance exactGlobalSections_additive [Preadditive 𝒜] [incl.Additive] :
    (exactGlobalSections J R incl).Additive :=
  inferInstanceAs (incl ⋙ sheafGlobalSectionsSmooth J R).Additive

/-- The inclusion `Γ_{X{G}}(incl F) → Γ(X, incl F|_X)` on `𝒜`. -/
def exactGlobalInclusion :
    exactGlobalSections J R incl ⋙ smoothForget R G ⟶
      exactRestriction J R incl ⋙ sheafSectionsModule J R (base P ρ).obj :=
  Functor.whiskerLeft incl (sheafSmoothGlobalInclusion J R)

theorem exactGlobalInclusion_app (F : 𝒜) :
    (exactGlobalInclusion J R incl).app F = (sheafSmoothGlobalInclusion J R).app (incl.obj F) :=
  rfl

/-- A smooth global section is sent to itself. -/
theorem exactGlobalInclusion_app_apply (F : 𝒜)
    (s : ((exactGlobalSections J R incl ⋙ smoothForget R G).obj F)) :
    ((exactGlobalInclusion J R incl).app F).hom s = s.1 := rfl

/-- Invariant global sections on `𝒜`, the shape of Berkovich's `Γ_{X(G)}`: the
`G`-invariant vectors of the smooth global sections. -/
def exactInvariantGlobalSections : 𝒜 ⥤ ModuleCat.{w} R :=
  exactGlobalSections J R incl ⋙ smoothInvariantsFunctor R G

instance exactInvariantGlobalSections_additive [Preadditive 𝒜] [incl.Additive] :
    (exactInvariantGlobalSections J R incl).Additive :=
  inferInstanceAs (exactGlobalSections J R incl ⋙ smoothInvariantsFunctor R G).Additive

end Functors

variable [Abelian 𝒜] [incl.Additive]
variable [PreservesFiniteLimits incl]

section Exactness

/-- Smooth global sections on `𝒜` are left exact. -/
instance exactGlobalSections_preservesFiniteLimits :
    PreservesFiniteLimits (exactGlobalSections J R incl) :=
  comp_preservesFiniteLimits _ _

/-- Invariant global sections on `𝒜` are left exact. -/
instance exactInvariantGlobalSections_preservesFiniteLimits :
    PreservesFiniteLimits (exactInvariantGlobalSections J R incl) :=
  comp_preservesFiniteLimits _ _

end Exactness

variable [EnoughInjectives 𝒜]

section Derived

/-- Degree `q` smooth cohomology on `𝒜`, the shape of Berkovich's `H^q(X{G}, F)`: the
right derived functors of `exactGlobalSections`, computed with injective resolutions in
`𝒜`. -/
def exactGlobalDerived (q : ℕ) : 𝒜 ⥤ SmoothRep.{w, uG, w} R G :=
  (exactGlobalSections J R incl).rightDerived q

/-- In degree zero, the derived functor is the functor itself. -/
def exactGlobalDerivedZeroIso : exactGlobalDerived J R incl 0 ≅ exactGlobalSections J R incl :=
  (exactGlobalSections J R incl).rightDerivedZeroIsoSelf

/-- The derived functors are computed by any injective resolution in `𝒜`. -/
def exactGlobalDerivedIso {F : 𝒜} (I : InjectiveResolution F) (q : ℕ) :
    (exactGlobalDerived J R incl q).obj F ≅
      (HomologicalComplex.homologyFunctor (SmoothRep.{w, uG, w} R G) (ComplexShape.up ℕ) q).obj
        (((exactGlobalSections J R incl).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          I.cocomplex) :=
  I.isoRightDerivedObj (exactGlobalSections J R incl) q

omit [PreservesFiniteLimits incl] in
/-- The derived functors vanish in positive degrees on injective objects of `𝒜`. -/
theorem isZero_exactGlobalDerived_succ_of_injective (F : 𝒜) [Injective F] (q : ℕ) :
    IsZero ((exactGlobalDerived J R incl (q + 1)).obj F) :=
  (exactGlobalSections J R incl).isZero_rightDerived_obj_injective_succ q F

/-- Degree `q` invariant cohomology on `𝒜`, the shape of Berkovich's `H^q(X(G), F)`: the
right derived functors of `exactInvariantGlobalSections`. -/
def exactInvariantGlobalDerived (q : ℕ) : 𝒜 ⥤ ModuleCat.{w} R :=
  (exactInvariantGlobalSections J R incl).rightDerived q

/-- In degree zero, the derived functor is the functor itself. -/
def exactInvariantGlobalDerivedZeroIso :
    exactInvariantGlobalDerived J R incl 0 ≅ exactInvariantGlobalSections J R incl :=
  (exactInvariantGlobalSections J R incl).rightDerivedZeroIsoSelf

/-- The edge map from invariant cohomology to the invariants of the smooth cohomology,
`H^q(X(G), F) → H^q(X{G}, F)^G`. -/
def exactInvariantGlobalEdgeMap (q : ℕ) :
    exactInvariantGlobalDerived J R incl q ⟶
      exactGlobalDerived J R incl q ⋙ smoothInvariantsFunctor R G :=
  LeftExactHomology.derivedNatTrans (smoothInvariantsFunctor R G)
    (exactGlobalSections J R incl) q

/-- In degree zero, the edge map is an isomorphism. -/
instance isIso_exactInvariantGlobalEdgeMap_zero :
    IsIso (exactInvariantGlobalEdgeMap J R incl 0) :=
  LeftExactHomology.isIso_derivedNatTrans_zero _ _

variable [HasSheafify J (ModuleCat.{w} R)]
variable [PreservesFiniteColimits incl]
variable [∀ F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R, (ι P ρ).op.HasPointwiseRightKanExtension F]
variable [EnoughInjectives (Sheaf J (ModuleCat.{w} R))]

/-- The comparison `H^q(X{G}, incl F) → H^q(X, incl F|_X)` in degree `q`: the base change
transformation of `exactGlobalInclusion` along the exact functors `smoothForget` and
`exactRestriction`. -/
def exactGlobalComparison (q : ℕ) :
    exactGlobalDerived J R incl q ⋙ smoothForget R G ⟶
      exactRestriction J R incl ⋙ sectionsDerived J R (base P ρ).obj q :=
  ExactBaseChange.baseChangeNatTrans (exactGlobalInclusion J R incl) q

end Derived

end Langlands.Sheaf.Equivariant.TwistedOver
