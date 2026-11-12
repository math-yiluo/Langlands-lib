import Langlands.Cohomology.DiscreteSheafDerivedComparison
import Langlands.Cohomology.AcyclicResolution.DerivedComparisonComposite

/-!
# Cohomology of the derived comparison for compactly supported cohomology

For an exact functor, the homology comparison `LeftExactHomology.homologyHom` is
Mathlib's `ShortComplex.mapHomologyIso`, and the comparison
`LeftExactHomology.derivedHom` of right derived functors is inverse to
`DerivedPlus.rightDerivedCompIsoOfResolution` for the identity isomorphism. As a
consequence, in each degree the cohomology of the derived comparison
`compactComplexComparison` on a twisted site is the degree-wise comparison
`compactComparison`, through the identification
`compactComplexForgetHomologyIso` of the cohomology of its source.
-/

noncomputable section

namespace Langlands.Cohomology.DiscreteSheafDerivedComparison

open CategoryTheory CategoryTheory.Limits

universe w w₁ w₂ w₃ w₄ vC vD vE uC uD uE v u uG uI

section Exact

variable {D : Type uD} [Category.{vD} D] [Abelian D] {E : Type uE} [Category.{vE} E] [Abelian E]
  (Φ : D ⥤ E) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]

/-- For an exact functor, Mathlib's cycles comparison is a left inverse of
`LeftExactHomology.toCycles`. -/
lemma mapCyclesIso_hom_comp_toCycles (S : ShortComplex D) :
    (S.mapCyclesIso Φ).hom ≫ LeftExactHomology.toCycles Φ S = 𝟙 _ := by
  rw [← cancel_mono (S.map Φ).iCycles, Category.assoc, LeftExactHomology.toCycles_iCycles,
    ShortComplex.mapCyclesIso_hom_iCycles, Category.id_comp]

/-- For an exact functor, `LeftExactHomology.homologyHom` is Mathlib's homology
comparison `ShortComplex.mapHomologyIso`. -/
lemma homologyHom_eq_mapHomologyIso_hom (S : ShortComplex D) :
    LeftExactHomology.homologyHom Φ S = (S.mapHomologyIso Φ).hom := by
  rw [← cancel_epi (S.map Φ).homologyπ, LeftExactHomology.homologyπ_homologyHom,
    DerivedPlus.homologyπ_mapHomologyIso_hom,
    IsIso.inv_eq_of_inv_hom_id (mapCyclesIso_hom_comp_toCycles Φ S)]

variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasInjectiveResolutions C]
  (G : C ⥤ D) [G.Additive]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- For an exact functor `Φ`, the classical comparison
`Φ (Rⁿ G X) ≅ Rⁿ (G ⋙ Φ) X` for the identity of `G ⋙ Φ`, followed by
`LeftExactHomology.derivedHom`, is the identity. -/
theorem rightDerivedCompIsoOfResolution_refl_hom_comp_derivedHom {X : C}
    (I : InjectiveResolution X) (n : ℕ) :
    (DerivedPlus.rightDerivedCompIsoOfResolution G Φ (Iso.refl (G ⋙ Φ)) I n).hom ≫
      LeftExactHomology.derivedHom Φ G I n = 𝟙 _ := by
  have h₀ : (Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ Φ))
      (ComplexShape.up ℕ)).hom.app I.cocomplex = 𝟙 _ := by
    ext i
    simp [Functor.mapHomologicalComplexCompIso]
  rw [DerivedPlus.rightDerivedCompIsoOfResolution_hom, h₀, HomologicalComplex.homologyMap_id,
    LeftExactHomology.derivedHom, LeftExactHomology.homologyNatTrans_app,
    homologyHom_eq_mapHomologyIso_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  erw [Category.id_comp, Iso.inv_hom_id_assoc]
  rw [← Φ.map_comp, Iso.hom_inv_id, Φ.map_id]

/-- For an exact functor `Φ`, `LeftExactHomology.derivedNatTrans Φ G n` is the inverse
of the classical comparison for the identity of `G ⋙ Φ`, computed with Mathlib's
chosen injective resolution. -/
theorem rightDerivedCompIsoOfResolution_refl_hom_comp_derivedNatTrans (X : C) (n : ℕ) :
    (DerivedPlus.rightDerivedCompIsoOfResolution G Φ (Iso.refl (G ⋙ Φ))
        (injectiveResolution X) n).hom ≫
      (LeftExactHomology.derivedNatTrans Φ G n).app X = 𝟙 _ :=
  rightDerivedCompIsoOfResolution_refl_hom_comp_derivedHom Φ G (injectiveResolution X) n

end Exact

section Compact

open Langlands.Sheaf.Equivariant Langlands.Sheaf.PointSupport
open Langlands.Sheaf.Equivariant.TwistedOver Langlands.Cohomology.DiscreteSheafDerivedComplex

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C} [P.RespectsIso] {X : C}
variable {G : Type uG} [Group G] {ρ : G →* Aut X}
variable (J : GrothendieckTopology (P.Over ⊤ X)) [IsTranslationInvariant (ρ := ρ) J]
variable (R : Type w) [CommRing R] [TopologicalSpace G]
variable (L : LocalActionSystem (TwistedOver P ρ) G)
variable [HasSheafify J (ModuleCat.{w} R)]
variable [HasSheafify (twistedTopology ρ J) (ModuleCat.{w} R)]
variable [L.HasFiniteEquivariantRefinements (twistedTopology ρ J)]
variable [∀ F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R, (ι P ρ).op.HasPointwiseRightKanExtension F]
variable [EnoughInjectives (Sheaf (twistedTopology ρ J) (ModuleCat.{w} R))]
variable {I : Type uI} [TopologicalSpace I] {Φ : I → J.Point.{w}}
variable [P.ContainsIdentities] [LocallySmall.{w} (P.Over ⊤ X)]
variable [EnoughInjectives (Sheaf J (ModuleCat.{w} R))]
variable [HasDerivedCategory.{w₁} (L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J))]
variable [HasDerivedCategory.{w₂} (Sheaf J (ModuleCat.{w} R))]
variable [HasDerivedCategory.{w₄} (ModuleCat.{w} R)]
variable [MulAction G I] [ContinuousConstSMul G I] [IsTopologicalGroup G]
variable [HasDerivedCategory.{w₃} (SmoothRep.{w, uG, w} R G)]

set_option backward.isDefEq.respectTransparency false in
/-- On cohomology in degree `n`, the derived comparison `compactComplexComparison`
is the degree-wise comparison `compactComparison J R L E n`: under the
identification of the cohomology of the forgetful image of the source with the
image of its cohomology (`mapDerivedCategoryHomologyIso`) and the published
identifications `DerivedPlus.homologyIso` of both derived complexes. -/
theorem compactComplexComparison_homology_eq (E : PointEquivariance ρ Φ)
    (F : L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J)) (n : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{w} R) (n : ℤ)).map
        ((compactComplexComparison J R L E).app F) ≫
        (DerivedPlus.homologyIso (sheafCompactSections J Φ R (base P ρ).obj)
          (injectiveResolution ((discreteRestriction J R L).obj F)) n).hom =
      (DerivedPlus.mapDerivedCategoryHomologyIso (smoothForget R G) (n : ℤ)).hom.app
          ((DerivedPlus.derivedComplex (discreteCompactSections J R L E) ⋙
            DerivedCategory.Plus.ι).obj F) ≫
        (smoothForget R G).map (DerivedPlus.homologyIso (discreteCompactSections J R L E)
          (injectiveResolution F) n).hom ≫
        (compactComparison J R L E n).app F := by
  have h₀ : (DerivedPlus.derivedCompIso (discreteCompactSections J R L E) (smoothForget R G)
      (Iso.refl _)).hom.app F =
        (DerivedPlus.derivedPostcompIso (discreteCompactSections J R L E)
          (smoothForget R G)).hom.app F := by
    simp only [DerivedPlus.derivedCompIso, Iso.trans_hom, NatTrans.comp_app,
      AcyclicResolution.derivedComplexCongr_refl_hom_app, Category.comp_id]
  have h₁ := DerivedPlus.derivedCompIso_hom_homology (discreteCompactSections J R L E)
    (smoothForget R G) (Iso.refl _) (injectiveResolution F) n
  have h₂ := inclusionRestrictionComparison_homology J R L E F n
  have h₃ := rightDerivedCompIsoOfResolution_refl_hom_comp_derivedNatTrans (smoothForget R G)
    (discreteCompactSections J R L E) F n
  rw [h₀] at h₁
  have e : (compactComplexComparison J R L E).app F =
      (DerivedPlus.derivedPostcompIso (discreteCompactSections J R L E)
        (smoothForget R G)).hom.app F ≫
        ((derivedComplexMap (smoothCompactInclusion J R L E)).app F ≫
          (restrictionCompactComparison J R L Φ).app F) := rfl
  rw [e, Functor.map_comp, Category.assoc]
  erw [h₂, reassoc_of% h₁, reassoc_of% h₃]
  rfl

/-- The cohomology in degree `n` of the derived complex of smooth compactly
supported global sections, with the action of `G` forgotten, is the module
underlying `discreteCompactDerived J R L E n`: the published
`mapDerivedCategoryHomologyIso` for the exact functor `smoothForget`, followed by
`smoothForget` applied to `compactComplexHomologyIso`. -/
def compactComplexForgetHomologyIso (E : PointEquivariance ρ Φ)
    (F : L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J)) (n : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{w} R) (n : ℤ)).obj
        ((smoothForget R G).mapDerivedCategory.obj
          (DerivedCategory.Plus.ι.obj ((compactComplex J R L E).obj F))) ≅
      (smoothForget R G).obj ((discreteCompactDerived J R L E n).obj F) :=
  (DerivedPlus.mapDerivedCategoryHomologyIso (smoothForget R G) (n : ℤ)).app
      (DerivedCategory.Plus.ι.obj ((compactComplex J R L E).obj F)) ≪≫
    (smoothForget R G).mapIso (compactComplexHomologyIso J R L E F n)

/-- On cohomology in degree `n`, the derived comparison `compactComplexComparison`
is the degree-wise comparison `compactComparison J R L E n`, through
`compactComplexForgetHomologyIso` on the source and the published
`sheafCompactComplexHomologyIso` on the target. -/
theorem compactComplexComparison_homology (E : PointEquivariance ρ Φ)
    (F : L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J)) (n : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{w} R) (n : ℤ)).map
        ((compactComplexComparison J R L E).app F) ≫
        (sheafCompactComplexHomologyIso J Φ R (base P ρ).obj
          ((discreteRestriction J R L).obj F) n).hom =
      (compactComplexForgetHomologyIso J R L E F n).hom ≫
        (compactComparison J R L E n).app F :=
  (compactComplexComparison_homology_eq J R L E F n).trans (Category.assoc _ _ _).symm

end Compact

end Langlands.Cohomology.DiscreteSheafDerivedComparison
