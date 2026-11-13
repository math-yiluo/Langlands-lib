import Langlands.Cohomology.DiscreteSheafDerivedComparisonHomology

/-!
# Compact comparison maps for exact abelian subcategories of twisted sheaves

Let `G` act on an object `X`, and let `J` be a translation-invariant topology on the
site over `X` with a `G`-equivariant family of points. The published modules
`TwistedCompactComparison`, `DiscreteSheafDerivedComparison` and
`DiscreteSheafDerivedComparisonHomology` construct, for the discrete sheaves of a local
action system, the comparison maps from smooth compactly supported cohomology on the
twisted site to compactly supported cohomology of the restriction to the site over
`X`. Those constructions use only that discrete sheaves form an abelian category with
enough injectives whose inclusion into module sheaves on the twisted site is exact.

This module repeats them for an arbitrary abelian category `𝒜` with an exact additive
functor `incl` to module sheaves on the twisted site. The locally discrete sheaves of
`LocalActionSmoothPart` are an instance. Berkovich's étale `G`-sheaves are of that kind.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.TwistedOver

open CategoryTheory CategoryTheory.Limits
open Langlands.Sheaf.PointSupport
open Langlands.Cohomology Langlands.Cohomology.DiscreteSheafDerivedComparison
open Langlands.Cohomology.AcyclicResolution

universe w w₁ w₂ w₃ w₄ u v uG uI uA vA

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C} [P.RespectsIso] {X : C}
variable {G : Type uG} [Group G] {ρ : G →* Aut X}
variable (J : GrothendieckTopology (P.Over ⊤ X)) [IsTranslationInvariant (ρ := ρ) J]
variable (R : Type w) [CommRing R]
variable {I : Type uI} [MulAction G I] {Φ : I → J.Point.{w}}
variable [P.ContainsIdentities] [LocallySmall.{w} (P.Over ⊤ X)]
variable [TopologicalSpace I] [ContinuousConstSMul G I]
variable [TopologicalSpace G] [IsTopologicalGroup G]

section Sheaves

/-- The inclusion of the smooth compactly supported global sections of a module sheaf
on the twisted site into the compactly supported sections of its restriction to the
site over `X`: the counit of the smooth-part adjunction. -/
def sheafSmoothCompactInclusion (E : PointEquivariance ρ Φ) :
    sheafCompactSectionsSmooth J R E ⋙ smoothForget R G ⟶
      restriction ρ J (ModuleCat.{w} R) ⋙ sheafCompactSections J Φ R (base P ρ).obj where
  app F := (forget₂ (Rep.{w} R G) (ModuleCat.{w} R)).map
    ((SmoothRep.toRepSmoothPartAdjunction R G).counit.app ((sheafCompactSectionsRep J R E).obj F))
  naturality F F' f := by
    have h := (SmoothRep.toRepSmoothPartAdjunction R G).counit.naturality
      ((sheafCompactSectionsRep J R E).map f)
    exact ((forget₂ (Rep.{w} R G) (ModuleCat.{w} R)).map_comp _ _).symm.trans
      (((forget₂ (Rep.{w} R G) (ModuleCat.{w} R)).congr_map h).trans
        ((forget₂ (Rep.{w} R G) (ModuleCat.{w} R)).map_comp _ _))

/-- A smooth compactly supported section is sent to itself. -/
theorem sheafSmoothCompactInclusion_app_apply (E : PointEquivariance ρ Φ)
    (F : Sheaf (twistedTopology ρ J) (ModuleCat.{w} R))
    (s : ((sheafCompactSectionsSmooth J R E ⋙ smoothForget R G).obj F)) :
    ((sheafSmoothCompactInclusion J R E).app F).hom s = s.1 := rfl

end Sheaves

variable {𝒜 : Type uA} [Category.{vA} 𝒜]
variable (incl : 𝒜 ⥤ Sheaf (twistedTopology ρ J) (ModuleCat.{w} R))

section Functors

/-- Smooth compactly supported global sections on `𝒜`: `incl` followed by Berkovich's
`Γ_{c,X{G}}` on the twisted site. -/
def exactCompactSections (E : PointEquivariance ρ Φ) : 𝒜 ⥤ SmoothRep.{w, uG, w} R G :=
  incl ⋙ sheafCompactSectionsSmooth J R E

instance exactCompactSections_additive [Preadditive 𝒜] [incl.Additive]
    (E : PointEquivariance ρ Φ) :
    (exactCompactSections J R incl E).Additive :=
  inferInstanceAs (incl ⋙ sheafCompactSectionsSmooth J R E).Additive

/-- Restriction from `𝒜` to module sheaves on the site over `X`: `incl` followed by
restriction along the inclusion of the site over `X` into the twisted site. -/
def exactRestriction : 𝒜 ⥤ Sheaf J (ModuleCat.{w} R) :=
  incl ⋙ restriction ρ J (ModuleCat.{w} R)

instance exactRestriction_additive [Preadditive 𝒜] [incl.Additive] :
    (exactRestriction J R incl).Additive where
  map_add := by
    intros
    exact congrArg (restriction ρ J (ModuleCat.{w} R)).map (incl.map_add)

/-- The inclusion `Γ_{c,X{G}}(incl F) → Γ_c(X, incl F|_X)` on `𝒜`. -/
def exactCompactInclusion (E : PointEquivariance ρ Φ) :
    exactCompactSections J R incl E ⋙ smoothForget R G ⟶
      exactRestriction J R incl ⋙ sheafCompactSections J Φ R (base P ρ).obj :=
  Functor.whiskerLeft incl (sheafSmoothCompactInclusion J R E)

theorem exactCompactInclusion_app (E : PointEquivariance ρ Φ) (F : 𝒜) :
    (exactCompactInclusion J R incl E).app F = (sheafSmoothCompactInclusion J R E).app (incl.obj F) :=
  rfl

/-- Invariant compactly supported global sections on `𝒜`: the `G`-invariant vectors of
the smooth compactly supported global sections. -/
def exactInvariantCompactSections (E : PointEquivariance ρ Φ) : 𝒜 ⥤ ModuleCat.{w} R :=
  exactCompactSections J R incl E ⋙ smoothInvariantsFunctor R G

instance exactInvariantCompactSections_additive [Preadditive 𝒜] [incl.Additive]
    (E : PointEquivariance ρ Φ) :
    (exactInvariantCompactSections J R incl E).Additive :=
  inferInstanceAs (exactCompactSections J R incl E ⋙ smoothInvariantsFunctor R G).Additive

end Functors

variable [Abelian 𝒜] [incl.Additive]
variable [HasSheafify J (ModuleCat.{w} R)]
variable [PreservesFiniteLimits incl] [PreservesFiniteColimits incl]

section Exactness

instance exactCompactSections_preservesFiniteLimits (E : PointEquivariance ρ Φ) :
    PreservesFiniteLimits (exactCompactSections J R incl E) :=
  comp_preservesFiniteLimits _ _

instance exactInvariantCompactSections_preservesFiniteLimits (E : PointEquivariance ρ Φ) :
    PreservesFiniteLimits (exactInvariantCompactSections J R incl E) :=
  comp_preservesFiniteLimits _ _

instance exactRestriction_preservesFiniteLimits :
    PreservesFiniteLimits (exactRestriction J R incl) :=
  comp_preservesFiniteLimits _ _

variable [∀ F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R, (ι P ρ).op.HasPointwiseRightKanExtension F]

instance exactRestriction_preservesFiniteColimits :
    PreservesFiniteColimits (exactRestriction J R incl) :=
  comp_preservesFiniteColimits _ _

end Exactness

variable [EnoughInjectives 𝒜]

section Derived

/-- Degree `q` smooth compactly supported cohomology on `𝒜`: the right derived functors
of `exactCompactSections`, computed with injective resolutions in `𝒜`. -/
def exactCompactDerived (E : PointEquivariance ρ Φ) (q : ℕ) : 𝒜 ⥤ SmoothRep.{w, uG, w} R G :=
  (exactCompactSections J R incl E).rightDerived q

/-- In degree zero, the derived functor is the functor itself. -/
def exactCompactDerivedZeroIso (E : PointEquivariance ρ Φ) :
    exactCompactDerived J R incl E 0 ≅ exactCompactSections J R incl E :=
  (exactCompactSections J R incl E).rightDerivedZeroIsoSelf

/-- Degree `q` invariant compactly supported cohomology on `𝒜`: the right derived
functors of `exactInvariantCompactSections`. -/
def exactInvariantCompactDerived (E : PointEquivariance ρ Φ) (q : ℕ) : 𝒜 ⥤ ModuleCat.{w} R :=
  (exactInvariantCompactSections J R incl E).rightDerived q

/-- In degree zero, the derived functor is the functor itself. -/
def exactInvariantCompactDerivedZeroIso (E : PointEquivariance ρ Φ) :
    exactInvariantCompactDerived J R incl E 0 ≅ exactInvariantCompactSections J R incl E :=
  (exactInvariantCompactSections J R incl E).rightDerivedZeroIsoSelf

/-- The edge map from invariant compactly supported cohomology to the invariants of the
smooth compactly supported cohomology. -/
def exactInvariantEdgeMap (E : PointEquivariance ρ Φ) (q : ℕ) :
    exactInvariantCompactDerived J R incl E q ⟶
      exactCompactDerived J R incl E q ⋙ smoothInvariantsFunctor R G :=
  LeftExactHomology.derivedNatTrans (smoothInvariantsFunctor R G)
    (exactCompactSections J R incl E) q

/-- In degree zero, the edge map is an isomorphism. -/
instance isIso_exactInvariantEdgeMap_zero (E : PointEquivariance ρ Φ) :
    IsIso (exactInvariantEdgeMap J R incl E 0) :=
  LeftExactHomology.isIso_derivedNatTrans_zero _ _

variable [∀ F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R, (ι P ρ).op.HasPointwiseRightKanExtension F]
variable [EnoughInjectives (Sheaf J (ModuleCat.{w} R))]

/-- The comparison `H^q_c(X{G}, incl F) → H^q_c(X, incl F|_X)` in degree `q`: the base change
transformation of `exactCompactInclusion` along the exact functors `smoothForget` and
`exactRestriction`. -/
def exactCompactComparison (E : PointEquivariance ρ Φ) (q : ℕ) :
    exactCompactDerived J R incl E q ⋙ smoothForget R G ⟶
      exactRestriction J R incl ⋙ compactDerived J Φ R (base P ρ).obj q :=
  ExactBaseChange.baseChangeNatTrans (exactCompactInclusion J R incl E) q

omit [P.ContainsIdentities] [LocallySmall.{w} (P.Over ⊤ X)] [TopologicalSpace G]
  [IsTopologicalGroup G]
  [EnoughInjectives (Sheaf J (ModuleCat.{w} R))] in
/-- The positive right derived functors of the exact restriction vanish. -/
theorem isZero_exactRestriction_rightDerived (F : 𝒜) (q : ℕ) :
    IsZero (((exactRestriction J R incl).rightDerived (q + 1)).obj F) :=
  Langlands.AlgebraicGeometry.Modules.DerivedSections.isZero_rightDerived_succ_of_preservesHomology
    (exactRestriction J R incl) F q

end Derived

section Complexes

variable [∀ F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R, (ι P ρ).op.HasPointwiseRightKanExtension F]
variable [EnoughInjectives (Sheaf J (ModuleCat.{w} R))]
variable [HasDerivedCategory.{w₁} 𝒜]
variable [HasDerivedCategory.{w₂} (Sheaf J (ModuleCat.{w} R))]
variable [HasDerivedCategory.{w₃} (SmoothRep.{w, uG, w} R G)]
variable [HasDerivedCategory.{w₄} (ModuleCat.{w} R)]

/-- The complex `RΓ_c(X{G}, incl F)` in the bounded below derived category of smooth
representations of `G`. -/
def exactCompactComplex (E : PointEquivariance ρ Φ) :
    𝒜 ⥤ DerivedCategory.Plus (SmoothRep.{w, uG, w} R G) :=
  DerivedPlus.derivedComplex (exactCompactSections J R incl E)

/-- Cohomology of `exactCompactComplex` in degree `q` is `exactCompactDerived`. -/
def exactCompactComplexHomologyIso (E : PointEquivariance ρ Φ) (F : 𝒜) (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (SmoothRep.{w, uG, w} R G) q).obj
        ((exactCompactComplex J R incl E).obj F) ≅
      (exactCompactDerived J R incl E q).obj F :=
  DerivedPlus.homologyIso (exactCompactSections J R incl E) (injectiveResolution F) q

omit [HasSheafify J (ModuleCat.{w} R)]
  [PreservesFiniteLimits incl] [PreservesFiniteColimits incl]
  [∀ F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R, (ι P ρ).op.HasPointwiseRightKanExtension F]
  [EnoughInjectives (Sheaf J (ModuleCat.{w} R))]
  [HasDerivedCategory.{w₂} (Sheaf J (ModuleCat.{w} R))]
  [HasDerivedCategory.{w₄} (ModuleCat.{w} R)] in
/-- `exactCompactComplex` has no cohomology in negative degrees. -/
theorem isZero_exactCompactComplex_homology (E : PointEquivariance ρ Φ) (F : 𝒜) {n : ℤ}
    (hn : n < 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor (SmoothRep.{w, uG, w} R G) n).obj
      ((exactCompactComplex J R incl E).obj F)) :=
  DerivedPlus.isZero_homology_of_neg (exactCompactSections J R incl E) F hn

variable (Φ) in
/-- The derived composite comparison for the exact restriction: from the derived
complex of compactly supported sections over `X` of the restriction, as a functor on
`𝒜`, to the derived complex of compactly supported sections evaluated at the
restriction. -/
def exactRestrictionCompactComparison :
    DerivedPlus.derivedComplex
        (exactRestriction J R incl ⋙ sheafCompactSections J Φ R (base P ρ).obj) ⋙
          DerivedCategory.Plus.ι ⟶
      exactRestriction J R incl ⋙
        (DiscreteSheafDerivedComplex.sheafCompactComplex J Φ R (base P ρ).obj ⋙
          DerivedCategory.Plus.ι) where
  app F := derivedCompComparison (sheafCompactSections J Φ R (base P ρ).obj)
    (Iso.refl (exactRestriction J R incl ⋙ sheafCompactSections J Φ R (base P ρ).obj)) F
    (isZero_exactRestriction_rightDerived J R incl F)
  naturality _ _ f := derivedCompComparison_naturality
    (sheafCompactSections J Φ R (base P ρ).obj)
    (Iso.refl (exactRestriction J R incl ⋙ sheafCompactSections J Φ R (base P ρ).obj)) f
    (isZero_exactRestriction_rightDerived J R incl _)
    (isZero_exactRestriction_rightDerived J R incl _)

/-- The comparison `RΓ_c(X{G}, incl F) → RΓ_c(X, incl F|_X)` in the derived category of
modules, with the action of `G` on the source forgotten: the exact postcomposition
isomorphism for `smoothForget`, the map induced by `exactCompactInclusion`, and the
derived composite comparison for the exact restriction. -/
def exactCompactComplexComparison (E : PointEquivariance ρ Φ) :
    (exactCompactComplex J R incl E ⋙ DerivedCategory.Plus.ι) ⋙
        (smoothForget R G).mapDerivedCategory ⟶
      exactRestriction J R incl ⋙
        (DiscreteSheafDerivedComplex.sheafCompactComplex J Φ R (base P ρ).obj ⋙
          DerivedCategory.Plus.ι) :=
  (DerivedPlus.derivedPostcompIso (exactCompactSections J R incl E) (smoothForget R G)).hom ≫
    derivedComplexMap (exactCompactInclusion J R incl E) ≫
      exactRestrictionCompactComparison J R Φ incl

omit [HasDerivedCategory.{w₃} (SmoothRep.{w, uG, w} R G)] in
set_option backward.isDefEq.respectTransparency false in
/-- On cohomology in degree `n`, the map induced by `exactCompactInclusion` followed by
the derived composite comparison for restriction is `exactCompactComparison`,
precomposed with the comparison `LeftExactHomology.derivedNatTrans` for the exact
functor `smoothForget`. -/
@[reassoc]
theorem exactInclusionRestrictionComparison_homology (E : PointEquivariance ρ Φ) (F : 𝒜)
    (n : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{w} R) (n : ℤ)).map
        ((derivedComplexMap (exactCompactInclusion J R incl E)).app F ≫
          (exactRestrictionCompactComparison J R Φ incl).app F) ≫
        (DerivedPlus.homologyIso (sheafCompactSections J Φ R (base P ρ).obj)
          (injectiveResolution ((exactRestriction J R incl).obj F)) n).hom =
      (DerivedPlus.homologyIso (exactCompactSections J R incl E ⋙ smoothForget R G)
          (injectiveResolution F) n).hom ≫
        (LeftExactHomology.derivedNatTrans (smoothForget R G)
          (exactCompactSections J R incl E) n).app F ≫
        (exactCompactComparison J R incl E n).app F := by
  have h := derivedCompComparison_homology (sheafCompactSections J Φ R (base P ρ).obj)
    (Iso.refl (exactRestriction J R incl ⋙ sheafCompactSections J Φ R (base P ρ).obj)) F
    (isZero_exactRestriction_rightDerived J R incl F) n
  have h' := derivedComplexMap_homology (exactCompactInclusion J R incl E) F n
  rw [Functor.map_comp, Category.assoc]
  erw [h, reassoc_of% h']
  congr 1
  simp only [exactCompactComparison, ExactBaseChange.baseChangeNatTrans, NatTrans.comp_app,
    NatIso.isIso_inv_app, IsIso.hom_inv_id_assoc, ExactBaseChange.compComparisonNatTrans_app]

set_option backward.isDefEq.respectTransparency false in
/-- On cohomology in degree `n`, `exactCompactComplexComparison` is
`exactCompactComparison` in degree `n`, through `mapDerivedCategoryHomologyIso` and the
identifications `DerivedPlus.homologyIso` of both derived complexes. -/
theorem exactCompactComplexComparison_homology_eq (E : PointEquivariance ρ Φ) (F : 𝒜)
    (n : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{w} R) (n : ℤ)).map
        ((exactCompactComplexComparison J R incl E).app F) ≫
        (DerivedPlus.homologyIso (sheafCompactSections J Φ R (base P ρ).obj)
          (injectiveResolution ((exactRestriction J R incl).obj F)) n).hom =
      (DerivedPlus.mapDerivedCategoryHomologyIso (smoothForget R G) (n : ℤ)).hom.app
          ((DerivedPlus.derivedComplex (exactCompactSections J R incl E) ⋙
            DerivedCategory.Plus.ι).obj F) ≫
        (smoothForget R G).map (DerivedPlus.homologyIso (exactCompactSections J R incl E)
          (injectiveResolution F) n).hom ≫
        (exactCompactComparison J R incl E n).app F := by
  have h₀ : (DerivedPlus.derivedCompIso (exactCompactSections J R incl E) (smoothForget R G)
      (Iso.refl _)).hom.app F =
        (DerivedPlus.derivedPostcompIso (exactCompactSections J R incl E)
          (smoothForget R G)).hom.app F := by
    simp only [DerivedPlus.derivedCompIso, Iso.trans_hom, NatTrans.comp_app,
      AcyclicResolution.derivedComplexCongr_refl_hom_app, Category.comp_id]
  have h₁ := DerivedPlus.derivedCompIso_hom_homology (exactCompactSections J R incl E)
    (smoothForget R G) (Iso.refl _) (injectiveResolution F) n
  have h₂ := exactInclusionRestrictionComparison_homology J R incl E F n
  have h₃ := rightDerivedCompIsoOfResolution_refl_hom_comp_derivedNatTrans (smoothForget R G)
    (exactCompactSections J R incl E) F n
  rw [h₀] at h₁
  have e : (exactCompactComplexComparison J R incl E).app F =
      (DerivedPlus.derivedPostcompIso (exactCompactSections J R incl E)
        (smoothForget R G)).hom.app F ≫
        ((derivedComplexMap (exactCompactInclusion J R incl E)).app F ≫
          (exactRestrictionCompactComparison J R Φ incl).app F) := rfl
  rw [e, Functor.map_comp, Category.assoc]
  erw [h₂, reassoc_of% h₁, reassoc_of% h₃]
  rfl

/-- The cohomology in degree `n` of `exactCompactComplex` with the action of `G`
forgotten is the module underlying `exactCompactDerived` in degree `n`. -/
def exactCompactComplexForgetHomologyIso (E : PointEquivariance ρ Φ) (F : 𝒜) (n : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{w} R) (n : ℤ)).obj
        ((smoothForget R G).mapDerivedCategory.obj
          (DerivedCategory.Plus.ι.obj ((exactCompactComplex J R incl E).obj F))) ≅
      (smoothForget R G).obj ((exactCompactDerived J R incl E n).obj F) :=
  (DerivedPlus.mapDerivedCategoryHomologyIso (smoothForget R G) (n : ℤ)).app
      (DerivedCategory.Plus.ι.obj ((exactCompactComplex J R incl E).obj F)) ≪≫
    (smoothForget R G).mapIso (exactCompactComplexHomologyIso J R incl E F n)

/-- On cohomology in degree `n`, `exactCompactComplexComparison` is
`exactCompactComparison` in degree `n`, through `exactCompactComplexForgetHomologyIso`
on the source and `sheafCompactComplexHomologyIso` on the target. -/
theorem exactCompactComplexComparison_homology (E : PointEquivariance ρ Φ) (F : 𝒜) (n : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{w} R) (n : ℤ)).map
        ((exactCompactComplexComparison J R incl E).app F) ≫
        (DiscreteSheafDerivedComplex.sheafCompactComplexHomologyIso J Φ R (base P ρ).obj
          ((exactRestriction J R incl).obj F) n).hom =
      (exactCompactComplexForgetHomologyIso J R incl E F n).hom ≫
        (exactCompactComparison J R incl E n).app F :=
  (exactCompactComplexComparison_homology_eq J R incl E F n).trans (Category.assoc _ _ _).symm

end Complexes

end Langlands.Sheaf.Equivariant.TwistedOver
