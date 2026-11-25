/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GlobalHomPullbackComparison
public import WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageSquareMate
import WeilConjectures.AlgebraicGeometry.MixedSectionsCompositionCoherence

/-! # Coherence of mixed sections comparisons
Source: Stacks Project, cohomology.tex, Tags 08HY, 0D5T and 0D5W.
(blueprint: lem-sc-mixed-sections-square-comparison-coherence).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w wA
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry
private theorem composeComparisonSquare
    {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
    {A B P Q : C} {T U V W : D}
    (e₁ : A ≅ P) (e₂ : B ≅ Q) (t : P ⟶ Q)
    (cP : G.obj P ⟶ T) (cQ : G.obj Q ⟶ U)
    (s₁ : T ≅ V) (s₂ : U ≅ W) (s : T ⟶ U)
    (cL : G.obj A ⟶ V) (cR : G.obj B ⟶ W)
    (hl : cL = G.map e₁.hom ≫ cP ≫ s₁.hom)
    (hr : cR = G.map e₂.hom ≫ cQ ≫ s₂.hom)
    (ht : G.map t ≫ cQ = cP ≫ s) :
    G.map (e₁.hom ≫ t ≫ e₂.inv) ≫ cR = cL ≫ s₁.inv ≫ s ≫ s₂.hom := by
  rw [hl, hr]
  simp only [Functor.map_comp, Category.assoc]
  rw [← G.map_comp_assoc e₂.inv e₂.hom, e₂.inv_hom_id, G.map_id, Category.id_comp]
  rw [reassoc_of% ht]
  simp only [Iso.hom_inv_id_assoc]

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]

private theorem mixedSections_eq_naturality
    {A B : Scheme.{u}} (t t' : A ⟶ B) (h : t = t')
    (F : schemeDerivedCategory A) :
    (schemeDerivedGlobalSections B).map
        ((eqToHom (congrArg (fun t ↦ schemeDerivedDirectImage t) h)).app F) ≫
        (mixedGlobalSectionsDirectImageIso t').hom.app F =
      (mixedGlobalSectionsDirectImageIso t).hom.app F ≫
        (eqToHom (congrArg (fun t ↦ schemeGlobalScalarRestriction t) h)).app
          ((schemeDerivedGlobalSections A).obj F) := by
  subst t'
  simp only [eqToHom_refl, NatTrans.id_app]
  erw [CategoryTheory.Functor.map_id]
  erw [Category.id_comp, Category.comp_id]

-- Give the path calculation fixed natural transformations rather than expanded mate data.
private theorem mixedSections_compare_paths
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (g : Y' ⟶ Y) (gX : X' ⟶ X) (comm : gX ≫ f = f' ≫ g)
    (δ : schemeDerivedDirectImage gX ⋙ schemeDerivedDirectImage f ⟶
      schemeDerivedDirectImage f' ⋙ schemeDerivedDirectImage g)
    (hδ : δ = (schemeNormalizedDirectImageCompIso gX f).hom ≫
      eqToHom (congrArg (fun t ↦ schemeDerivedDirectImage t) comm) ≫
      (schemeNormalizedDirectImageCompIso f' g).inv)
    (F : schemeDerivedCategory X') :
    (schemeDerivedGlobalSections Y).map (δ.app F) ≫
        (mixedGlobalSectionsDirectImageIso g).hom.app ((schemeDerivedDirectImage f').obj F) ≫
        (schemeGlobalScalarRestriction g).map
          ((mixedGlobalSectionsDirectImageIso f').hom.app F) =
      (mixedGlobalSectionsDirectImageIso f).hom.app ((schemeDerivedDirectImage gX).obj F) ≫
        (schemeGlobalScalarRestriction f).map
          ((mixedGlobalSectionsDirectImageIso gX).hom.app F) ≫
        (schemeGlobalScalarSquareIso f f' g gX comm).hom.app
          ((schemeDerivedGlobalSections X').obj F) := by
  let e₁ :=
    schemeNormalizedDirectImageCompIso gX f
  let e₂ :=
    schemeNormalizedDirectImageCompIso f' g
  have hl := mixedSections_composition_coherence gX f F
  have hr := mixedSections_composition_coherence f' g F
  dsimp only at hl hr
  rw [hδ]
  let S := (schemeDerivedGlobalSections X').obj F
  have ht := mixedSections_eq_naturality (gX ≫ f)
    (f' ≫ g) comm F
  have h := composeComparisonSquare (schemeDerivedGlobalSections Y)
    (e₁.app F) (e₂.app F)
    ((eqToHom (congrArg (fun t ↦ schemeDerivedDirectImage t) comm)).app F)
    ((mixedGlobalSectionsDirectImageIso (gX ≫ f)).hom.app F)
    ((mixedGlobalSectionsDirectImageIso (f' ≫ g)).hom.app F)
    ((schemeGlobalScalarRestrictionCompIso gX f).app S)
    ((schemeGlobalScalarRestrictionCompIso f' g).app S)
    ((eqToHom (congrArg (fun t ↦ schemeGlobalScalarRestriction t)
      comm)).app S)
    ((mixedGlobalSectionsDirectImageIso f).hom.app
      ((schemeDerivedDirectImage gX).obj F) ≫
      (schemeGlobalScalarRestriction f).map
        ((mixedGlobalSectionsDirectImageIso gX).hom.app F))
    ((mixedGlobalSectionsDirectImageIso g).hom.app
      ((schemeDerivedDirectImage f').obj F) ≫
      (schemeGlobalScalarRestriction g).map
        ((mixedGlobalSectionsDirectImageIso f').hom.app F)) hl hr ht
  calc
    _ = (schemeDerivedGlobalSections Y).map
        (e₁.hom.app F ≫
          (eqToHom (congrArg (fun t ↦ schemeDerivedDirectImage t)
            comm)).app F ≫ e₂.inv.app F) ≫
        ((mixedGlobalSectionsDirectImageIso g).hom.app
          ((schemeDerivedDirectImage f').obj F) ≫
          (schemeGlobalScalarRestriction g).map
            ((mixedGlobalSectionsDirectImageIso f').hom.app F)) := rfl
    _ = ((mixedGlobalSectionsDirectImageIso f).hom.app
          ((schemeDerivedDirectImage gX).obj F) ≫
          (schemeGlobalScalarRestriction f).map
            ((mixedGlobalSectionsDirectImageIso gX).hom.app F)) ≫
        (schemeGlobalScalarRestrictionCompIso gX f).inv.app S ≫
        (eqToHom (congrArg (fun t ↦ schemeGlobalScalarRestriction t)
          comm)).app S ≫
        (schemeGlobalScalarRestrictionCompIso f' g).hom.app S := h
    _ = _ := by
      dsimp only [S, schemeGlobalScalarSquareIso, Iso.trans_hom, Iso.symm_hom,
        NatTrans.comp_app, eqToIso.hom]
      simp only [Category.assoc]


set_option backward.defeqAttrib.useBackward true in
-- Checking canonical comparison choices expands derived-functor and sheaf instances.
/-- Normalized Leray comparisons commute with the conjugate of the fixed pullback
composition comparison. No pullback unit or base-change map occurs in this statement.
Source: Stacks Project, cohomology.tex, Tags 0D5T and 08HY, with the normalized
sections comparison of Tag 0D5W.
(blueprint: lem-sc-mixed-sections-square-comparison-coherence).

Proof: Choose a K-injective representative J of F. Transpose the fixed left-derived
pullback composition comparisons under the pinned derived adjunctions. Their
left-derived counit equations and the Hom-equivalence equation of
exists_schemeDerivedAdjunction identify their conjugate delta with the right-derived
comparison induced by the identity underived pushforward square. Its normalization
is the pasted right-derived-unit equation of Tag 0D5T. Precompose the displayed
identity at Qh(J) with the pasted right-derived unit for the path p_*; f_*; Gamma_Y.
Direct image of a K-injective complex is acyclic for further direct image and global
sections, so this pasted unit is invertible. Substitute the characterizing equations
of exists_mixedGlobalSectionsDirectImageIso for f, p, f-prime, and g. Naturality
moves the units past the underived composition comparisons, and exact scalar
restriction moves its unit through localization. Both composites now localize the
same map on underived sections: all four Leray comparisons are identity on elements,
and pullback.condition identifies their scalar actions. The remaining scalar
comparison is precisely schemeGlobalScalarSquareIso, built from restriction along
composites. Cancel the invertible pasted unit. Every derived object is isomorphic
to Qh of a K-injective complex; naturality transports the equality to F. The sheaf
and module localizations are used separately, so no equality of w and wA is needed.
For F=0 the two morphisms are zero; identity squares give the composition unit law.
Empty schemes and nonflat g require no change, as neither units of pullback nor
invertibility of base change are asserted. -/
theorem mixedSections_square_comparison_coherence
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (F : schemeDerivedCategory (pullback f g)) :
    let a := fun {A D : Scheme.{u}} (h : A ⟶ D) ↦ schemeHomPullbackAdjunction h
    let p := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))
    let k := p (pullback.snd f g) g ≪≫
      eqToIso (congrArg (fun h ↦ derivedPullback h)
        (pullback.condition (f := f) (g := g)).symm) ≪≫
          (p (pullback.fst f g) f).symm
    let δ := conjugateEquiv ((a f).comp (a (pullback.fst f g)))
      ((a g).comp (a (pullback.snd f g))) k.hom
    (schemeDerivedGlobalSections Y).map (δ.app F) ≫
        (mixedGlobalSectionsDirectImageIso g).hom.app
          ((schemeDerivedDirectImage (pullback.snd f g)).obj F) ≫
        (schemeGlobalScalarRestriction g).map
          ((mixedGlobalSectionsDirectImageIso (pullback.snd f g)).hom.app F) =
      (mixedGlobalSectionsDirectImageIso f).hom.app
          ((schemeDerivedDirectImage (pullback.fst f g)).obj F) ≫
        (schemeGlobalScalarRestriction f).map
          ((mixedGlobalSectionsDirectImageIso (pullback.fst f g)).hom.app F) ≫
        (schemeGlobalScalarSquareIso f (pullback.snd f g) g (pullback.fst f g)
          pullback.condition).hom.app ((schemeDerivedGlobalSections (pullback f g)).obj F)
    := by
  dsimp only
  apply mixedSections_compare_paths f (pullback.snd f g) g (pullback.fst f g)
    pullback.condition _ _ F
  exact derivedDirectImage_square_mate f (pullback.snd f g) g
    (pullback.fst f g) pullback.condition

end AlgebraicGeometry
