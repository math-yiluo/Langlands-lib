import Langlands.Sheaf.Equivariant.TwistedExactGlobalComparison

/-!
# Derived global section complexes for exact abelian subcategories of twisted sheaves

Let `G` act on an object `X`, let `J` be a translation-invariant topology on the site
over `X`, and let `incl : 𝒜 ⥤ Sheaf (twistedTopology ρ J) (ModuleCat R)` be an exact
additive functor out of an abelian category with enough injectives. The published module
`TwistedExactGlobalComparison` defines, degree by degree, Berkovich's `H^q(X{G}, -)` and
`H^q(X(G), -)` on `𝒜` and the comparison maps `H^q(X{G}, F) → H^q(X, F|_X)`. This
module packages these derived functors as single objects of bounded below derived
categories, as `TwistedExactCompactComparison` does for compact supports:

* `sheafSectionsComplex`: `RΓ(U, F)` for module sheaves on a site, a complex of modules;
* `exactGlobalComplex`: `RΓ(X{G}, F)`, a complex of smooth representations of `G`;
* `exactInvariantGlobalComplex`: `RΓ(X(G), F)`, a complex of modules;
* `exactGlobalComplexComparison`: the comparison `RΓ(X{G}, F) → RΓ(X, F|_X)` in the
  derived category of modules, with the action of `G` forgotten.

Their cohomology in each degree `q ≥ 0` is the corresponding derived functor, they have no
cohomology in negative degrees, and on cohomology the comparison of complexes is
`exactGlobalComparison`. The proofs repeat those of the compact case.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.TwistedOver

open CategoryTheory CategoryTheory.Limits
open Langlands.Cohomology Langlands.Cohomology.DiscreteSheafDerivedComparison
open Langlands.Cohomology.AcyclicResolution

universe w w₁ w₂ w₃ w₄ u v uG uA vA

section Plain

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (R : Type w) [CommRing R]
variable [HasSheafify J (ModuleCat.{w} R)] [EnoughInjectives (Sheaf J (ModuleCat.{w} R))]
variable [HasDerivedCategory.{w₂} (Sheaf J (ModuleCat.{w} R))]
variable [HasDerivedCategory.{w₄} (ModuleCat.{w} R)]

/-- The derived section complex `RΓ(U, F)` over `U` of module sheaves on a site, in the
bounded below derived category of modules. -/
def sheafSectionsComplex (U : C) :
    Sheaf J (ModuleCat.{w} R) ⥤ DerivedCategory.Plus (ModuleCat.{w} R) :=
  DerivedPlus.derivedComplex (sheafSectionsModule J R U)

/-- Cohomology of `sheafSectionsComplex` in degree `q` is `sectionsDerived J R U q`. -/
def sheafSectionsComplexHomologyIso (U : C) (F : Sheaf J (ModuleCat.{w} R)) (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{w} R) q).obj
        ((sheafSectionsComplex J R U).obj F) ≅
      (sectionsDerived J R U q).obj F :=
  DerivedPlus.homologyIso (sheafSectionsModule J R U) (injectiveResolution F) q

/-- `sheafSectionsComplex` has no cohomology in negative degrees. -/
theorem isZero_sheafSectionsComplex_homology (U : C) (F : Sheaf J (ModuleCat.{w} R)) {n : ℤ}
    (hn : n < 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{w} R) n).obj
      ((sheafSectionsComplex J R U).obj F)) :=
  DerivedPlus.isZero_homology_of_neg (sheafSectionsModule J R U) F hn

end Plain

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C} [P.RespectsIso] {X : C}
variable {G : Type uG} [Group G] {ρ : G →* Aut X}
variable [P.ContainsIdentities]
variable (J : GrothendieckTopology (P.Over ⊤ X)) [IsTranslationInvariant (ρ := ρ) J]
variable (R : Type w) [CommRing R]
variable [TopologicalSpace G] [IsTopologicalGroup G]
variable {𝒜 : Type uA} [Category.{vA} 𝒜]
variable (incl : 𝒜 ⥤ Sheaf (twistedTopology ρ J) (ModuleCat.{w} R))
variable [Abelian 𝒜] [incl.Additive] [PreservesFiniteLimits incl] [EnoughInjectives 𝒜]
variable [HasDerivedCategory.{w₁} 𝒜]

section Complexes

variable [HasDerivedCategory.{w₃} (SmoothRep.{w, uG, w} R G)]

/-- The complex `RΓ(X{G}, incl F)` in the bounded below derived category of smooth
representations of `G`: the smooth global sections derived with injective resolutions in
`𝒜`. -/
def exactGlobalComplex : 𝒜 ⥤ DerivedCategory.Plus (SmoothRep.{w, uG, w} R G) :=
  DerivedPlus.derivedComplex (exactGlobalSections J R incl)

/-- Cohomology of `exactGlobalComplex` in degree `q` is `exactGlobalDerived`. -/
def exactGlobalComplexHomologyIso (F : 𝒜) (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (SmoothRep.{w, uG, w} R G) q).obj
        ((exactGlobalComplex J R incl).obj F) ≅
      (exactGlobalDerived J R incl q).obj F :=
  DerivedPlus.homologyIso (exactGlobalSections J R incl) (injectiveResolution F) q

omit [PreservesFiniteLimits incl] in
/-- `exactGlobalComplex` has no cohomology in negative degrees. -/
theorem isZero_exactGlobalComplex_homology (F : 𝒜) {n : ℤ} (hn : n < 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor (SmoothRep.{w, uG, w} R G) n).obj
      ((exactGlobalComplex J R incl).obj F)) :=
  DerivedPlus.isZero_homology_of_neg (exactGlobalSections J R incl) F hn

end Complexes

section Invariant

variable [HasDerivedCategory.{w₄} (ModuleCat.{w} R)]

/-- The complex `RΓ(X(G), incl F)` in the bounded below derived category of modules: the
`G`-invariant smooth global sections derived with injective resolutions in `𝒜`. -/
def exactInvariantGlobalComplex : 𝒜 ⥤ DerivedCategory.Plus (ModuleCat.{w} R) :=
  DerivedPlus.derivedComplex (exactInvariantGlobalSections J R incl)

/-- Cohomology of `exactInvariantGlobalComplex` in degree `q` is
`exactInvariantGlobalDerived`. -/
def exactInvariantGlobalComplexHomologyIso (F : 𝒜) (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{w} R) q).obj
        ((exactInvariantGlobalComplex J R incl).obj F) ≅
      (exactInvariantGlobalDerived J R incl q).obj F :=
  DerivedPlus.homologyIso (exactInvariantGlobalSections J R incl) (injectiveResolution F) q

omit [PreservesFiniteLimits incl] in
/-- `exactInvariantGlobalComplex` has no cohomology in negative degrees. -/
theorem isZero_exactInvariantGlobalComplex_homology (F : 𝒜) {n : ℤ} (hn : n < 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{w} R) n).obj
      ((exactInvariantGlobalComplex J R incl).obj F)) :=
  DerivedPlus.isZero_homology_of_neg (exactInvariantGlobalSections J R incl) F hn

end Invariant

section Comparison

variable [HasSheafify J (ModuleCat.{w} R)] [PreservesFiniteColimits incl]
variable [∀ F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R, (ι P ρ).op.HasPointwiseRightKanExtension F]
variable [EnoughInjectives (Sheaf J (ModuleCat.{w} R))]
variable [HasDerivedCategory.{w₂} (Sheaf J (ModuleCat.{w} R))]
variable [HasDerivedCategory.{w₃} (SmoothRep.{w, uG, w} R G)]
variable [HasDerivedCategory.{w₄} (ModuleCat.{w} R)]

/-- The derived composite comparison for the exact restriction: from the derived complex
of global sections over `X` of the restriction, as a functor on `𝒜`, to the derived
complex of global sections evaluated at the restriction. -/
def exactRestrictionGlobalComparison :
    DerivedPlus.derivedComplex
        (exactRestriction J R incl ⋙ sheafSectionsModule J R (base P ρ).obj) ⋙
          DerivedCategory.Plus.ι ⟶
      exactRestriction J R incl ⋙
        (sheafSectionsComplex J R (base P ρ).obj ⋙ DerivedCategory.Plus.ι) where
  app F := derivedCompComparison (sheafSectionsModule J R (base P ρ).obj)
    (Iso.refl (exactRestriction J R incl ⋙ sheafSectionsModule J R (base P ρ).obj)) F
    (isZero_exactRestriction_rightDerived J R incl F)
  naturality _ _ f := derivedCompComparison_naturality
    (sheafSectionsModule J R (base P ρ).obj)
    (Iso.refl (exactRestriction J R incl ⋙ sheafSectionsModule J R (base P ρ).obj)) f
    (isZero_exactRestriction_rightDerived J R incl _)
    (isZero_exactRestriction_rightDerived J R incl _)

/-- The comparison `RΓ(X{G}, incl F) → RΓ(X, incl F|_X)` in the derived category of
modules, with the action of `G` on the source forgotten: the exact postcomposition
isomorphism for `smoothForget`, the map induced by `exactGlobalInclusion`, and the derived
composite comparison for the exact restriction. -/
def exactGlobalComplexComparison :
    (exactGlobalComplex J R incl ⋙ DerivedCategory.Plus.ι) ⋙
        (smoothForget R G).mapDerivedCategory ⟶
      exactRestriction J R incl ⋙
        (sheafSectionsComplex J R (base P ρ).obj ⋙ DerivedCategory.Plus.ι) :=
  (DerivedPlus.derivedPostcompIso (exactGlobalSections J R incl) (smoothForget R G)).hom ≫
    derivedComplexMap (exactGlobalInclusion J R incl) ≫
      exactRestrictionGlobalComparison J R incl

omit [HasDerivedCategory.{w₃} (SmoothRep.{w, uG, w} R G)] in
set_option backward.isDefEq.respectTransparency false in
/-- On cohomology in degree `n`, the map induced by `exactGlobalInclusion` followed by the
derived composite comparison for restriction is `exactGlobalComparison`, precomposed with
the comparison `LeftExactHomology.derivedNatTrans` for the exact functor `smoothForget`. -/
@[reassoc]
theorem exactGlobalInclusionRestrictionComparison_homology (F : 𝒜) (n : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{w} R) (n : ℤ)).map
        ((derivedComplexMap (exactGlobalInclusion J R incl)).app F ≫
          (exactRestrictionGlobalComparison J R incl).app F) ≫
        (DerivedPlus.homologyIso (sheafSectionsModule J R (base P ρ).obj)
          (injectiveResolution ((exactRestriction J R incl).obj F)) n).hom =
      (DerivedPlus.homologyIso (exactGlobalSections J R incl ⋙ smoothForget R G)
          (injectiveResolution F) n).hom ≫
        (LeftExactHomology.derivedNatTrans (smoothForget R G)
          (exactGlobalSections J R incl) n).app F ≫
        (exactGlobalComparison J R incl n).app F := by
  have h := derivedCompComparison_homology (sheafSectionsModule J R (base P ρ).obj)
    (Iso.refl (exactRestriction J R incl ⋙ sheafSectionsModule J R (base P ρ).obj)) F
    (isZero_exactRestriction_rightDerived J R incl F) n
  have h' := derivedComplexMap_homology (exactGlobalInclusion J R incl) F n
  rw [Functor.map_comp, Category.assoc]
  erw [h, reassoc_of% h']
  congr 1
  simp only [exactGlobalComparison, ExactBaseChange.baseChangeNatTrans, NatTrans.comp_app,
    NatIso.isIso_inv_app, IsIso.hom_inv_id_assoc, ExactBaseChange.compComparisonNatTrans_app]

set_option backward.isDefEq.respectTransparency false in
/-- On cohomology in degree `n`, `exactGlobalComplexComparison` is `exactGlobalComparison`
in degree `n`, through `mapDerivedCategoryHomologyIso` and the identifications
`DerivedPlus.homologyIso` of both derived complexes. -/
theorem exactGlobalComplexComparison_homology_eq (F : 𝒜) (n : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{w} R) (n : ℤ)).map
        ((exactGlobalComplexComparison J R incl).app F) ≫
        (DerivedPlus.homologyIso (sheafSectionsModule J R (base P ρ).obj)
          (injectiveResolution ((exactRestriction J R incl).obj F)) n).hom =
      (DerivedPlus.mapDerivedCategoryHomologyIso (smoothForget R G) (n : ℤ)).hom.app
          ((DerivedPlus.derivedComplex (exactGlobalSections J R incl) ⋙
            DerivedCategory.Plus.ι).obj F) ≫
        (smoothForget R G).map (DerivedPlus.homologyIso (exactGlobalSections J R incl)
          (injectiveResolution F) n).hom ≫
        (exactGlobalComparison J R incl n).app F := by
  have h₀ : (DerivedPlus.derivedCompIso (exactGlobalSections J R incl) (smoothForget R G)
      (Iso.refl _)).hom.app F =
        (DerivedPlus.derivedPostcompIso (exactGlobalSections J R incl)
          (smoothForget R G)).hom.app F := by
    simp only [DerivedPlus.derivedCompIso, Iso.trans_hom, NatTrans.comp_app,
      AcyclicResolution.derivedComplexCongr_refl_hom_app, Category.comp_id]
  have h₁ := DerivedPlus.derivedCompIso_hom_homology (exactGlobalSections J R incl)
    (smoothForget R G) (Iso.refl _) (injectiveResolution F) n
  have h₂ := exactGlobalInclusionRestrictionComparison_homology J R incl F n
  have h₃ := rightDerivedCompIsoOfResolution_refl_hom_comp_derivedNatTrans (smoothForget R G)
    (exactGlobalSections J R incl) F n
  rw [h₀] at h₁
  have e : (exactGlobalComplexComparison J R incl).app F =
      (DerivedPlus.derivedPostcompIso (exactGlobalSections J R incl)
        (smoothForget R G)).hom.app F ≫
        ((derivedComplexMap (exactGlobalInclusion J R incl)).app F ≫
          (exactRestrictionGlobalComparison J R incl).app F) := rfl
  rw [e, Functor.map_comp, Category.assoc]
  erw [h₂, reassoc_of% h₁, reassoc_of% h₃]
  rfl

/-- The cohomology in degree `n` of `exactGlobalComplex` with the action of `G` forgotten
is the module underlying `exactGlobalDerived` in degree `n`. -/
def exactGlobalComplexForgetHomologyIso (F : 𝒜) (n : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{w} R) (n : ℤ)).obj
        ((smoothForget R G).mapDerivedCategory.obj
          (DerivedCategory.Plus.ι.obj ((exactGlobalComplex J R incl).obj F))) ≅
      (smoothForget R G).obj ((exactGlobalDerived J R incl n).obj F) :=
  (DerivedPlus.mapDerivedCategoryHomologyIso (smoothForget R G) (n : ℤ)).app
      (DerivedCategory.Plus.ι.obj ((exactGlobalComplex J R incl).obj F)) ≪≫
    (smoothForget R G).mapIso (exactGlobalComplexHomologyIso J R incl F n)

/-- On cohomology in degree `n`, `exactGlobalComplexComparison` is `exactGlobalComparison`
in degree `n`, through `exactGlobalComplexForgetHomologyIso` on the source and
`sheafSectionsComplexHomologyIso` on the target. -/
theorem exactGlobalComplexComparison_homology (F : 𝒜) (n : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{w} R) (n : ℤ)).map
        ((exactGlobalComplexComparison J R incl).app F) ≫
        (sheafSectionsComplexHomologyIso J R (base P ρ).obj
          ((exactRestriction J R incl).obj F) n).hom =
      (exactGlobalComplexForgetHomologyIso J R incl F n).hom ≫
        (exactGlobalComparison J R incl n).app F :=
  (exactGlobalComplexComparison_homology_eq J R incl F n).trans (Category.assoc _ _ _).symm

end Comparison

end Langlands.Sheaf.Equivariant.TwistedOver
