/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Exact.ExactCompactificationUnit
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationRefinementHomotopyUnit

/-!
# Compatibility of exact compactification units with refinements

Source: Stacks Project, Tags 0F7B, 0F7I and 0D6E
(blueprint: lem-sfb-exact-compactification-unit-refinement).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

private lemma exactCompactificationUnit_whisker
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (a : F ≅ openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
      lowerStar (ModuleCat.{u + 1} A) c.g) :
    Functor.whiskerLeft DerivedCategory.Qh (exactCompactificationUnit A c F a) =
      normalizationHomotopyTransformation F
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i)
        (lowerStar (ModuleCat.{u + 1} A) c.g) a.hom := by
  unfold exactCompactificationUnit normalizationLocalizationDesc
  exact (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ)) _).map_preimage _

private lemma exactCompactificationUnit_transport
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f}
    (r : c.Refinement d) (hcart : IsPullback c.i (𝟙 X) r.hom d.i)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (a : F ≅ openImmersionLowerShriek (ModuleCat.{u + 1} A) d.i ⋙
      lowerStar (ModuleCat.{u + 1} A) d.g)
    : exactCompactificationUnit A d F a ≫
      rightDerivedLowerShriekOfCompactificationComparison (ModuleCat.{u + 1} A) r hcart =
      normalizationLocalizationDesc DerivedCategory.Qh
        (HomotopyCategory.quasiIso
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ))
        (normalizationHomotopyTransformation F
          (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i)
          (lowerStar (ModuleCat.{u + 1} A) c.g)
          (a.hom ≫ compactificationSheafRefinement A r hcart)) := by
  apply (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ)) _).map_injective
  change Functor.whiskerLeft DerivedCategory.Qh
    (exactCompactificationUnit A d F a ≫
      rightDerivedLowerShriekOfCompactificationComparison (ModuleCat.{u + 1} A) r hcart) = _
  rw [Functor.whiskerLeft_comp, exactCompactificationUnit_whisker]
  unfold normalizationLocalizationDesc
  rw [(Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ)) _).map_preimage]
  exact compactificationRefinement_homotopyUnit A r hcart F a.hom

/-- Two compactification units with the same underlying sheaf inclusion agree under the
canonical common-refinement comparison.
Source: Stacks Project, Tags 0F7B, 0F7I and 0D6E
(blueprint: lem-sfb-exact-compactification-unit-refinement).

Proof: first take a proper refinement from c to d. Its comparison is the proper/open
comparison for the coarser open immersion, followed by derived composition of direct images.
The sheaf proper/open map preserves the section in the ordinary direct image. Thus its
composite with the supplied sheaf isomorphism for d is the supplied isomorphism for c:
the compactification inclusion is injective, so it cancels. Apply the normalization of the
proper/open comparison on a K-injective resolution of the finer extension by zero. Direct
image preserves K-injectives, and the derived-composition unit identity identifies the two
resolution maps. This is equality of the descended units on homotopy representatives, hence
on the derived category by localization full faithfulness. For arbitrary c and d apply the
refinement identity to their two arrows from the common refinement and cancel the invertible
comparison. This is exactly the definition of the common-refinement comparison used here. -/
theorem exactCompactificationUnit_refinement
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (c d : Compactification f)
    (a : F ≅ openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
      lowerStar (ModuleCat.{u + 1} A) c.g)
    (b : F ≅ openImmersionLowerShriek (ModuleCat.{u + 1} A) d.i ⋙
      lowerStar (ModuleCat.{u + 1} A) d.g)
    (hab : a.hom ≫ compactificationSheafToDirectImage A c =
      b.hom ≫ compactificationSheafToDirectImage A d) :
    exactCompactificationUnit A c F a ≫
      (rightDerivedLowerShriekOfCompactificationIso A c d).hom =
        exactCompactificationUnit A d F b := by
  let e := Compactification.inf c d
  let r := Compactification.infFst c d
  let s := Compactification.infSnd c d
  have hr := Compactification.isPullback_infFst c d
  have hs := Compactification.isPullback_infSnd c d
  obtain ⟨hn, hm⟩ := compactificationSheafRefinement_properties A r hr
  have he : a.hom ≫ compactificationSheafRefinement A r hr =
      b.hom ≫ compactificationSheafRefinement A s hs := by
    have : ∀ M, Mono ((compactificationSheafToDirectImage A e).app M) := hm
    have : Mono (compactificationSheafToDirectImage A e) :=
      NatTrans.mono_of_mono_app _
    apply (cancel_mono (compactificationSheafToDirectImage A e)).1
    have hn' := (compactificationSheafRefinement_properties A s hs).1
    simp only [Category.assoc]
    rw [hn, hn']
    exact hab
  have h₁ := exactCompactificationUnit_transport A r hr F a
  have h₂ := exactCompactificationUnit_transport A s hs F b
  have ht : exactCompactificationUnit A c F a ≫
      rightDerivedLowerShriekOfCompactificationComparison (ModuleCat.{u + 1} A) r hr =
      exactCompactificationUnit A d F b ≫
        rightDerivedLowerShriekOfCompactificationComparison (ModuleCat.{u + 1} A) s hs := by
    rw [h₁, h₂, he]
  simp only [rightDerivedLowerShriekOfCompactificationIso, Iso.trans_hom,
    Iso.symm_hom, asIso_hom]
  rw [← Category.assoc, ht, Category.assoc]
  simp

end AlgebraicGeometry.Etale
