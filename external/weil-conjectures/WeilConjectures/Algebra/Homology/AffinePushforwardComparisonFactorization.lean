/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.AffinePushforwardComparisonCoordinates
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

/-! # Naturality of the ordinary affine comparison on cohomology -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace AlgebraicGeometry
private lemma cancelComparison {D : Type*} [Category D]
    {X Y Z W V U : D} (s : X ≅ Y) (b : Y ⟶ Z) (c : Z ⟶ W)
    (d : W ⟶ V) (e : V ⟶ U) :
    s.inv ≫ (s.hom ≫ b ≫ c) ≫ d ≫ e = b ≫ c ≫ d ≫ e := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The ordinary comparison can be evaluated on cohomology before the derived unit.
Source: Stacks Project, perfect.tex, Tag 0AVW, affine morphism equivalence proof;
Mathlib `ShortComplex.homologyMap_mapNatTrans` and naturality of
`DerivedCategory.homologyFunctorFactors`.
(blueprint: lem-pc-affine-pushforward-comparison-factorization).

Proof: Write F = res_phi followed by tilde_B and G = tilde_A followed by pushforward.
Expand the defined comparison map as the exact homology comparison for F, the
inverse Q/homology comparison, H(Q(sigma_C)), and the derived unit. Naturality of
the inverse Q/homology comparison moves H(Q(sigma_C)) to the left as the ordinary
homology map of sigma_C. The natural transformation homology formula identifies
that map with the homology comparison for F, sigma evaluated at H^i(C), and the
inverse homology comparison for G. Cancel the inverse and forward comparisons
for F and associate the four remaining factors. This gives the displayed equation.
This argument is purely naturality: it works in every degree, on unbounded and
zero complexes, and over the zero ring. The preservation instances express
exactness of G, which follows from the supplied sigma and exactness of F. -/
theorem affinePushforwardComparison_factorization
    (A B : Type u) [CommRing A] [CommRing B] (φ : B →+* A) (i : ℤ)
    (σ : ModuleCat.restrictScalars φ ⋙ affinePushforwardTilde B ≅
      affinePushforwardTilde A ⋙
        Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom φ)))
    [(affinePushforwardTilde A ⋙ RingedSpace.moduleDirectImage
      (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).PreservesZeroMorphisms]
    [(affinePushforwardTilde A ⋙ RingedSpace.moduleDirectImage
      (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).PreservesHomology]
    (C : CochainComplex (ModuleCat A) ℤ) :
    affinePushforwardCohomologyMapOfComparison A B φ σ C i =
      σ.hom.app (C.homology i) ≫
        ((C.sc i).mapHomologyIso
          (affinePushforwardTilde A ⋙ RingedSpace.moduleDirectImage
            (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom)).inv ≫
        ((DerivedCategory.homologyFunctorFactors
          (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i).app
          (((affinePushforwardTilde A ⋙ RingedSpace.moduleDirectImage
            (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).mapHomologicalComplex
              (.up ℤ)).obj C)).inv ≫
        (cast (by rfl)
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i).map
            ((RingedSpace.moduleDirectImage
              (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).rightDerivedFunctorUnit.app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj
                (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj C))))) := by
  let F := ModuleCat.restrictScalars φ ⋙ affinePushforwardTilde B
  let G := affinePushforwardTilde A ⋙ RingedSpace.moduleDirectImage
    (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom
  let : (affinePushforwardTilde B).Additive := by
    constructor
    intro M N f g
    exact tilde.map_add (R := .of B) f g
  let : (affinePushforwardTilde B).PreservesHomology := tilde_preservesHomology B
  let : PreservesFiniteLimits (affinePushforwardTilde B) :=
    Functor.preservesFiniteLimits_of_preservesHomology _
  let : PreservesFiniteColimits (affinePushforwardTilde B) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  let : F.PreservesHomology := inferInstance
  let : (affinePushforwardTilde A ⋙
      Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom φ))).PreservesZeroMorphisms :=
    ⟨fun X Y => by
      rw [Functor.comp_map, (affinePushforwardTilde A).map_zero]
      exact (Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom φ))).map_zero _ _⟩
  let σ' : F ≅ G := σ
  let a := (σ'.hom.mapHomologicalComplex (.up ℤ)).app C
  have hn := (DerivedCategory.homologyFunctorFactors
    (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i).inv.naturality a
  dsimp only [Functor.comp_map] at hn
  dsimp only [affinePushforwardCohomologyMapOfComparison]
  erw [← reassoc_of% hn]
  have hh := ShortComplex.homologyMap_mapNatTrans (C.sc i) σ'.hom
  change (HomologicalComplex.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) (.up ℤ) i).map a =
    ((C.sc i).mapHomologyIso F).hom ≫ σ'.hom.app (C.homology i) ≫
      ((C.sc i).mapHomologyIso G).inv at hh
  dsimp only [F, G, σ'] at hh
  erw [hh]
  exact cancelComparison
    ((C.sc i).mapHomologyIso (ModuleCat.restrictScalars φ ⋙ affinePushforwardTilde B))
    (σ.hom.app (C.homology i))
    ((C.sc i).mapHomologyIso (affinePushforwardTilde A ⋙ RingedSpace.moduleDirectImage
      (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom)).inv _ _

end AlgebraicGeometry
