import Langlands.Sheaf.Equivariant.TwistedCompactComparison

/-!
# Equivariant global sections and their cohomology on a twisted site

For module sheaves on a site, the sections over an object are left exact, and their right
derived functors are the cohomology over that object. On a twisted site of a `G`-object
`X`, the global sections of a module sheaf form a representation of `G`; their smooth part
is Berkovich's `Γ_{X{G}}`. On discrete sheaves, its right derived functors are Berkovich's
`H^q(X{G}, F)` as smooth representations. The inclusion of the smooth global sections into
the global sections of the restriction to the site over `X` induces comparison maps
`H^q(X{G}, F) → H^q(X, b^*F)`.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.TwistedOver

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Cohomology

universe w v u uG

section Plain

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (R : Type w) [CommRing R]

/-- Sections over `U` of module sheaves. -/
def sheafSectionsModule (U : C) : Sheaf J (ModuleCat.{w} R) ⥤ ModuleCat.{w} R :=
  sheafToPresheaf J (ModuleCat.{w} R) ⋙
    (CategoryTheory.evaluation Cᵒᵖ (ModuleCat.{w} R)).obj (Opposite.op U)

@[simp]
theorem sheafSectionsModule_obj (U : C) (F : Sheaf J (ModuleCat.{w} R)) :
    (sheafSectionsModule J R U).obj F = F.obj.obj (Opposite.op U) :=
  rfl

instance sheafSectionsModule_additive (U : C) : (sheafSectionsModule J R U).Additive :=
  inferInstanceAs (sheafToPresheaf J (ModuleCat.{w} R) ⋙
    (CategoryTheory.evaluation Cᵒᵖ (ModuleCat.{w} R)).obj (Opposite.op U)).Additive

/-- Sections over `U` of module sheaves are left exact. -/
instance sheafSectionsModule_preservesFiniteLimits (U : C) :
    PreservesFiniteLimits (sheafSectionsModule J R U) :=
  comp_preservesFiniteLimits _ _

variable [HasSheafify J (ModuleCat.{w} R)] [EnoughInjectives (Sheaf J (ModuleCat.{w} R))]

/-- Degree `q` cohomology over `U` of module sheaves: the right derived functors of the
sections over `U`, computed with injective resolutions of module sheaves. -/
def sectionsDerived (U : C) (q : ℕ) : Sheaf J (ModuleCat.{w} R) ⥤ ModuleCat.{w} R :=
  (sheafSectionsModule J R U).rightDerived q

/-- In degree zero, the cohomology over `U` is the sections over `U`. -/
def sectionsDerivedZeroIso (U : C) : sectionsDerived J R U 0 ≅ sheafSectionsModule J R U :=
  (sheafSectionsModule J R U).rightDerivedZeroIsoSelf

/-- The cohomology over `U` is the homology of the sections over `U` of any injective
resolution. -/
def sectionsDerivedIso (U : C) {F : Sheaf J (ModuleCat.{w} R)} (I : InjectiveResolution F)
    (q : ℕ) :
    (sectionsDerived J R U q).obj F ≅
      (HomologicalComplex.homologyFunctor (ModuleCat.{w} R) (ComplexShape.up ℕ) q).obj
        (((sheafSectionsModule J R U).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          I.cocomplex) :=
  I.isoRightDerivedObj (sheafSectionsModule J R U) q

/-- The cohomology over `U` vanishes in positive degrees on injective sheaves. -/
theorem isZero_sectionsDerived_succ_of_injective (U : C) (F : Sheaf J (ModuleCat.{w} R))
    [Injective F] (q : ℕ) : IsZero ((sectionsDerived J R U (q + 1)).obj F) :=
  (sheafSectionsModule J R U).isZero_rightDerived_obj_injective_succ q F

end Plain

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C} [P.RespectsIso] {X : C}
variable {G : Type uG} [Group G] {ρ : G →* Aut X}
variable [P.ContainsIdentities]
variable (J : GrothendieckTopology (P.Over ⊤ X)) [IsTranslationInvariant (ρ := ρ) J]
variable (R : Type w) [CommRing R]

section Sections

/-- Global sections of module sheaves on the twisted site, as representations of `G`: `g`
acts by restriction along the endomorphism `g⁻¹` of the base object. -/
def sheafGlobalSectionsRep : Sheaf (twistedTopology ρ J) (ModuleCat.{w} R) ⥤ Rep.{w} R G :=
  sheafSectionsRep R (twistedTopology ρ J) (baseAction P ρ)

instance sheafGlobalSectionsRep_additive : (sheafGlobalSectionsRep J R (ρ := ρ)).Additive :=
  inferInstanceAs (sheafSectionsRep R (twistedTopology ρ J) (baseAction P ρ)).Additive

/-- Global sections of module sheaves on the twisted site are left exact. -/
instance sheafGlobalSectionsRep_preservesFiniteLimits :
    PreservesFiniteLimits (sheafGlobalSectionsRep J R (ρ := ρ)) :=
  inferInstanceAs
    (PreservesFiniteLimits (sheafSectionsRep R (twistedTopology ρ J) (baseAction P ρ)))

/-- The module underlying the global sections representation is the module of sections of
the restriction to the site over `X` at the base object. -/
def sheafGlobalSectionsRepForgetIso :
    sheafGlobalSectionsRep J R (ρ := ρ) ⋙ forget₂ (Rep.{w} R G) (ModuleCat.{w} R) ≅
      restriction ρ J (ModuleCat.{w} R) ⋙ sheafSectionsModule J R (base P ρ).obj :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- Smooth global sections, Berkovich's `Γ_{X{G}}`: the smooth part of the global sections
representation. -/
def sheafGlobalSectionsSmooth :
    Sheaf (twistedTopology ρ J) (ModuleCat.{w} R) ⥤ SmoothRep.{w, uG, w} R G :=
  sheafGlobalSectionsRep J R ⋙ SmoothRep.smoothPartFunctor R G

instance sheafGlobalSectionsSmooth_additive :
    (sheafGlobalSectionsSmooth J R (ρ := ρ)).Additive where
  map_add := rfl

instance sheafGlobalSectionsSmooth_preservesFiniteLimits :
    PreservesFiniteLimits (sheafGlobalSectionsSmooth J R (ρ := ρ)) :=
  comp_preservesFiniteLimits _ _

end Sections

variable [TopologicalSpace G] [IsTopologicalGroup G]
variable (L : LocalActionSystem (TwistedOver P ρ) G)

section Discrete

/-- Smooth global sections of discrete module sheaves on the twisted site. -/
def discreteGlobalSections :
    L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J) ⥤ SmoothRep.{w, uG, w} R G :=
  L.discreteSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J) ⋙ sheafGlobalSectionsSmooth J R

instance discreteGlobalSections_additive : (discreteGlobalSections J R L).Additive :=
  inferInstanceAs (L.discreteSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J) ⋙
    sheafGlobalSectionsSmooth J R).Additive

variable [HasSheafify (twistedTopology ρ J) (ModuleCat.{w} R)]
variable [L.HasFiniteEquivariantRefinements (twistedTopology ρ J)]

/-- Smooth global sections of discrete sheaves are left exact. -/
instance discreteGlobalSections_preservesFiniteLimits :
    PreservesFiniteLimits (discreteGlobalSections J R L) :=
  comp_preservesFiniteLimits _ _

variable [EnoughInjectives (Sheaf (twistedTopology ρ J) (ModuleCat.{w} R))]

/-- Degree `q` cohomology of discrete module sheaves on the twisted site, as smooth
representations of `G`: the right derived functors of the smooth global sections, computed
with injective resolutions among discrete sheaves. This is the shape of Berkovich's
`H^q(X{G}, F)`. -/
def discreteGlobalDerived (q : ℕ) :
    L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J) ⥤ SmoothRep.{w, uG, w} R G :=
  (discreteGlobalSections J R L).rightDerived q

/-- In degree zero, the derived functor is the functor itself. -/
def discreteGlobalDerivedZeroIso : discreteGlobalDerived J R L 0 ≅ discreteGlobalSections J R L :=
  (discreteGlobalSections J R L).rightDerivedZeroIsoSelf

/-- The derived functors are computed by any injective resolution among discrete sheaves. -/
def discreteGlobalDerivedIso {F : L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J)}
    (I : InjectiveResolution F) (q : ℕ) :
    (discreteGlobalDerived J R L q).obj F ≅
      (HomologicalComplex.homologyFunctor (SmoothRep.{w, uG, w} R G) (ComplexShape.up ℕ) q).obj
        (((discreteGlobalSections J R L).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          I.cocomplex) :=
  I.isoRightDerivedObj (discreteGlobalSections J R L) q

/-- The derived functors vanish in positive degrees on injective discrete sheaves. -/
theorem isZero_discreteGlobalDerived_succ_of_injective
    (F : L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J)) [Injective F] (q : ℕ) :
    IsZero ((discreteGlobalDerived J R L (q + 1)).obj F) :=
  (discreteGlobalSections J R L).isZero_rightDerived_obj_injective_succ q F

end Discrete

section Comparison

/-- The inclusion of the smooth global sections of a discrete sheaf into the global sections
of its restriction to the site over `X`: the counit of the smooth-part adjunction. -/
def smoothGlobalInclusion :
    discreteGlobalSections J R L ⋙ smoothForget R G ⟶
      (L.discreteSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J) ⋙
        restriction ρ J (ModuleCat.{w} R)) ⋙ sheafSectionsModule J R (base P ρ).obj where
  app F := (forget₂ (Rep.{w} R G) (ModuleCat.{w} R)).map
    ((SmoothRep.toRepSmoothPartAdjunction R G).counit.app
      ((sheafGlobalSectionsRep J R).obj F.obj))
  naturality F F' f := by
    have h := (SmoothRep.toRepSmoothPartAdjunction R G).counit.naturality
      ((sheafGlobalSectionsRep J R).map f.hom)
    exact ((forget₂ (Rep.{w} R G) (ModuleCat.{w} R)).map_comp _ _).symm.trans
      (((forget₂ (Rep.{w} R G) (ModuleCat.{w} R)).congr_map h).trans
        ((forget₂ (Rep.{w} R G) (ModuleCat.{w} R)).map_comp _ _))

theorem smoothGlobalInclusion_app_apply
    (F : L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J))
    (s : ((discreteGlobalSections J R L ⋙ smoothForget R G).obj F)) :
    ((smoothGlobalInclusion J R L).app F).hom s = s.1 := rfl

variable [HasSheafify J (ModuleCat.{w} R)]
variable [HasSheafify (twistedTopology ρ J) (ModuleCat.{w} R)]
variable [L.HasFiniteEquivariantRefinements (twistedTopology ρ J)]
variable [∀ F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R, (ι P ρ).op.HasPointwiseRightKanExtension F]
variable [EnoughInjectives (Sheaf (twistedTopology ρ J) (ModuleCat.{w} R))]
variable [EnoughInjectives (Sheaf J (ModuleCat.{w} R))]

/-- The comparison from the cohomology of a discrete sheaf on the twisted site, as smooth
representations, to the cohomology over `X` of its restriction to the site over `X`, in
degree `q`: the base change transformation of `smoothGlobalInclusion` along the exact
functors `smoothForget` and restriction. This is the shape of Berkovich's maps
`H^q(X{G}, F) → H^q(X, b^*F)`. -/
def globalComparison (q : ℕ) :
    discreteGlobalDerived J R L q ⋙ smoothForget R G ⟶
      (L.discreteSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J) ⋙
        restriction ρ J (ModuleCat.{w} R)) ⋙ sectionsDerived J R (base P ρ).obj q :=
  ExactBaseChange.baseChangeNatTrans (smoothGlobalInclusion J R L) q

end Comparison

end Langlands.Sheaf.Equivariant.TwistedOver
