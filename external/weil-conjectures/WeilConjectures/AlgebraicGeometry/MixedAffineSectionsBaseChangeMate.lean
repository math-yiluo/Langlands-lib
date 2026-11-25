/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GlobalHomPullbackComparison
public import WeilConjectures.AlgebraicGeometry.MixedGlobalExtension
public import WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
import WeilConjectures.AlgebraicGeometry.MixedExtensionSectionsUnit
import WeilConjectures.AlgebraicGeometry.MixedSectionsBaseChangeUnitSquare

/-! # Affine sections transport the base-change mate with independent universes
Source: Stacks Project, Tags 0AA7, 08HY and 0D5T.
(blueprint: lem-sc-mixed-affine-sections-base-change-mate).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w wA
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]

/-- Restricted derived sections intertwine the two base-change mates.
This does not assume flatness, perfectness, or invertibility of sheaf base change.
Only Rf_*E is required to have quasi-coherent cohomology.
Source: Stacks Project, perfect.tex, Tag 0AA7, construction of the canonical map;
cohomology.tex, Tags 08HY (counit description) and 0D5T (Leray).
(blueprint: lem-sc-mixed-affine-sections-base-change-mate).

Proof:
1. Identify each affine base with the spectrum of its global ring by isoSpec.
   Derived direct-image composition identifies restricted RΓ_X E with RΓ_Y Rf_*E.
   On sheaves this comparison is the identity on sections. Derive it with its
   right-derived-unit equation, as for mixedGlobalSectionsDirectImageIso.
2. Rf_*E is quasi-coherent. The affine derived equivalence and the tilde/pullback
   formula on K-flat representatives identify RΓ_Y' Lg^*Rf_*E with derived
   extension of RΓ_Y Rf_*E. Uniqueness of the left adjoint to the fixed derived
   restriction identifies this extension with mixedGlobalExtension g, including
   its unit. Compose with extension of the inverse comparison from step 1 to
   obtain a. Direct-image composition gives the natural target comparison d.
3. Transpose the displayed right-hand composite under the fixed scalar adjunction.
   Expand sheaf base change as the mate of pullback composition and the counit
   for f. Naturality moves m past that counit; the adjunction triangle identities
   cancel the paired units and counits. Direct-image composition leaves RΓ_X(m)
   followed by Leray for g_X. The identity on underived sections and the
   right-derived-unit equation identify this with mixedGlobalSectionsDirectImageIso.
   The scalar-square identification is the equality of the two restricted actions.
4. The scalar adjunction Hom equivalence is injective, giving the stated equality
   simultaneously for all L and m. These computations take place in the sheaf
   and module localizations separately, so their universe levels need not agree.
   Zero E or an empty base gives the same identity on zero objects. -/
theorem exists_mixedAffineSectionsBaseChangeMate
    {X Y Y' : Scheme.{u}} [IsAffine Y] [IsAffine Y']
    (f : X ⟶ Y) (g : Y' ⟶ Y) (E : schemeDerivedCategory X)
    (hE : schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E)) :
    ∃ a : (mixedGlobalExtension g).obj
        ((schemeGlobalScalarRestriction f).obj ((schemeDerivedGlobalSections X).obj E)) ≅
        (schemeDerivedGlobalSections Y').obj
          ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj E)),
      ∃ d : schemeDerivedDirectImage (pullback.snd f g) ⋙ schemeDerivedGlobalSections Y' ≅
          schemeDerivedGlobalSections (pullback f g) ⋙
            schemeGlobalScalarRestriction (pullback.snd f g),
        ∀ (L : schemeDerivedCategory (pullback f g))
          (m : E ⟶ (schemeDerivedDirectImage (pullback.fst f g)).obj L),
          ((mixedGlobalExtensionAdjunction g).homEquiv _ _).symm
              ((schemeGlobalScalarRestriction f).map
                  ((schemeDerivedGlobalSections X).map m ≫
                    (mixedGlobalSectionsDirectImageIso (pullback.fst f g)).hom.app L) ≫
                (schemeGlobalScalarSquareIso f (pullback.snd f g) g (pullback.fst f g)
                  pullback.condition).hom.app ((schemeDerivedGlobalSections
                    (pullback f g)).obj L)) =
            a.hom ≫ (schemeDerivedGlobalSections Y').map
              (schemeDerivedBaseChangeMap f (pullback.snd f g) g
                (pullback.fst f g) pullback.condition E) ≫
              (schemeDerivedGlobalSections Y').map
                ((schemeDerivedDirectImage (pullback.snd f g)).map
                  (((schemeHomPullbackAdjunction (pullback.fst f g)).homEquiv E L).symm m)) ≫
              d.hom.app L := by
  obtain ⟨a₀, ha₀⟩ := exists_mixedExtensionSectionsUnit g
    ((schemeDerivedDirectImage f).obj E) hE
  let b := mixedGlobalSectionsDirectImageIso f
  let d := mixedGlobalSectionsDirectImageIso (pullback.snd f g)
  let a := (mixedGlobalExtension g).mapIso (b.app E).symm ≪≫ a₀
  have ha : (mixedGlobalExtensionAdjunction g).unit.app
        ((schemeGlobalScalarRestriction f).obj ((schemeDerivedGlobalSections X).obj E)) ≫
      (schemeGlobalScalarRestriction g).map a.hom =
    b.inv.app E ≫ (schemeDerivedGlobalSections Y).map
        ((schemeHomPullbackAdjunction g).unit.app ((schemeDerivedDirectImage f).obj E)) ≫
      (mixedGlobalSectionsDirectImageIso g).hom.app
        ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj E)) := by
    dsimp only [a, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv]
    rw [Functor.map_comp, ← Category.assoc]
    erw [← (mixedGlobalExtensionAdjunction g).unit.naturality (b.inv.app E)]
    simp only [Functor.id_map, Functor.comp_obj]
    erw [Category.assoc, ha₀]
  have hu := mixedSectionsBaseChange_unit_square f g E
  refine ⟨a, d, ?_⟩
  intro L m
  let n := ((schemeHomPullbackAdjunction (pullback.fst f g)).homEquiv E L).symm m
  have hm : (schemeHomPullbackAdjunction (pullback.fst f g)).unit.app E ≫
      (schemeDerivedDirectImage (pullback.fst f g)).map n = m :=
    ((schemeHomPullbackAdjunction (pullback.fst f g)).homEquiv E L).apply_symm_apply m
  apply ((mixedGlobalExtensionAdjunction g).homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  simp only [Functor.map_comp]
  rw [← Category.assoc, ha]
  let S := schemeGlobalScalarRestriction g
  have hn := d.hom.naturality n
  dsimp only [Functor.comp_map] at hn
  simp only [Category.assoc]
  erw [← S.map_comp, hn, S.map_comp]
  have hu' := congrArg (fun k ↦ b.inv.app E ≫ k) hu
  change b.inv.app E ≫ _ = b.inv.app E ≫ b.hom.app E ≫ _ at hu'
  simp only [Functor.map_comp, Iso.inv_hom_id_app_assoc] at hu'
  erw [reassoc_of% hu']
  have hs := (schemeGlobalScalarSquareIso f (pullback.snd f g) g (pullback.fst f g)
    pullback.condition).hom.naturality ((schemeDerivedGlobalSections (pullback f g)).map n)
  dsimp only [Functor.comp_map] at hs
  have hc := (mixedGlobalSectionsDirectImageIso (pullback.fst f g)).hom.naturality n
  dsimp only [Functor.comp_map] at hc
  erw [← hs]
  have hc' := congrArg (fun k ↦ (schemeGlobalScalarRestriction f).map k) hc
  simp only [Functor.map_comp] at hc'
  erw [← reassoc_of% hc']
  have hm' := congrArg (fun k ↦ (schemeGlobalScalarRestriction f).map
    ((schemeDerivedGlobalSections X).map k)) hm
  simp only [Functor.map_comp] at hm'
  erw [← reassoc_of% hm']


end AlgebraicGeometry
