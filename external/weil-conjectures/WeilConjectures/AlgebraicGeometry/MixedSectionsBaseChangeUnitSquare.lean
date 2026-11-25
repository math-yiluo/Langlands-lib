/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GlobalHomPullbackComparison
public import WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
import WeilConjectures.AlgebraicGeometry.MixedSectionsSquareComparisonCoherence

/-! # Sections of the base-change unit square with independent universes
Source: Stacks Project, cohomology.tex, Tags 08HY and 0D5T.
(blueprint: lem-sc-mixed-sections-base-change-unit-square).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w wA
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem mixed_mate_unit_square
    {S X T Y : Type*} [Category* S] [Category* X] [Category* T] [Category* Y]
    {Lf : S ⥤ X} {Rf : X ⥤ S} {Lq : T ⥤ Y} {Rq : Y ⥤ T}
    {Lg : S ⥤ T} {Rg : T ⥤ S} {Lp : X ⥤ Y} {Rp : Y ⥤ X}
    (af : Lf ⊣ Rf) (aq : Lq ⊣ Rq) (ag : Lg ⊣ Rg) (ap : Lp ⊣ Rp)
    (k : Lg ⋙ Lq ⟶ Lf ⋙ Lp) (E : X) :
    ag.unit.app (Rf.obj E) ≫ Rg.map
        (aq.homEquiv _ _ (k.app (Rf.obj E) ≫ Lp.map (af.counit.app E))) =
      Rf.map (ap.unit.app E) ≫
        (conjugateEquiv (af.comp ap) (ag.comp aq) k).app (Lp.obj E) := by
  let α : TwoSquare Lg Lf Lq Lp := .mk _ _ _ _ k
  have h := unit_mateEquiv ap ag (mateEquiv af aq α) E
  change Rf.map (ap.unit.app E) ≫
      ((mateEquiv ap ag (mateEquiv af aq α))).app (Lp.obj E) = _ at h
  rw [iterated_mateEquiv_conjugateEquiv] at h
  simpa [α, mateEquiv, Adjunction.homEquiv_unit, Functor.map_comp,
    Category.assoc] using h.symm


private theorem mixed_sections_paste
    {C D A B M N P Q : Type*}
    [Category* C] [Category* D] [Category* A] [Category* B]
    [Category* M] [Category* N] [Category* P] [Category* Q]
    (Rf : C ⥤ D) (Rg : A ⥤ D) (Rq : B ⥤ A) (Rp : B ⥤ C)
    (U : D ⥤ M) (V : A ⥤ P) (W : C ⥤ N) (Z : B ⥤ Q)
    (ρ : P ⥤ M) (σ : N ⥤ M) (τ : Q ⥤ P) (ν : Q ⥤ N)
    (cg : Rg ⋙ U ⟶ V ⋙ ρ) (cf : Rf ⋙ U ⟶ W ⋙ σ)
    (cq : Rq ⋙ V ⟶ Z ⋙ τ) (cp : Rp ⋙ W ⟶ Z ⋙ ν)
    (q : ν ⋙ σ ⟶ τ ⋙ ρ)
    {E : C} {F : B} {H : A}
    (ηg : Rf.obj E ⟶ Rg.obj H) (β : H ⟶ Rq.obj F)
    (ηp : E ⟶ Rp.obj F) (δ : Rf.obj (Rp.obj F) ⟶ Rg.obj (Rq.obj F))
    (hu : ηg ≫ Rg.map β = Rf.map ηp ≫ δ)
    (hc : U.map δ ≫ cg.app (Rq.obj F) ≫ ρ.map (cq.app F) =
      cf.app (Rp.obj F) ≫ σ.map (cp.app F) ≫ q.app (Z.obj F)) :
    U.map ηg ≫ cg.app H ≫ ρ.map (V.map β ≫ cq.app F) =
      cf.app E ≫ σ.map (W.map ηp ≫ cp.app F) ≫ q.app (Z.obj F) := by
  have hn := cg.naturality β
  have hf := cf.naturality ηp
  change U.map (Rg.map β) ≫ cg.app (Rq.obj F) =
    cg.app H ≫ ρ.map (V.map β) at hn
  change U.map (Rf.map ηp) ≫ cf.app (Rp.obj F) =
    cf.app E ≫ σ.map (W.map ηp) at hf
  rw [Functor.map_comp, ← reassoc_of% hn]
  rw [← Functor.map_comp_assoc, hu, Functor.map_comp, Category.assoc, hc]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hf]

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]

/-- Taking sections of the unit description of sheaf base change gives this identity
over the global ring of Y. No affine or quasi-coherence hypothesis is needed.
It concerns only the canonical unit at E, and constructs no extension isomorphism.
Source: Stacks Project, cohomology.tex, Remark 08HY and Lemma 0D5T.
(blueprint: lem-sc-mixed-sections-base-change-unit-square).

Proof:
1. Expand schemeDerivedBaseChangeMap as the f'-adjunct of the pullback-composition
comparison followed by Lg_X* of the counit of f. Apply the g-adjunction unit.
Naturality of the units moves the composition comparison through the adjunct.
The triangle identity for f cancels its counit with its unit. What remains is the
unit for g_X followed by the mate of the pullback-composition comparison, namely
the direct-image composition comparison of Tag 0D5T.
2. Apply RΓ_Y to this equation. The normalized Leray isomorphisms for f, g, f',
and g_X replace sections of the composed direct images with the two restrictions
of sections on X'. On underived sheaves these isomorphisms act identically on
sections. Equality of the two scalar actions is precisely pullback.condition;
schemeGlobalScalarSquareIso is the corresponding identity comparison.
3. On K-injective representatives the two composite comparisons are therefore
identical. Their right-derived-unit equations, supplied by
exists_mixedGlobalSectionsDirectImageIso and the derived direct-image composition
comparison, identify them on the full derived categories by the universal property
of right derivation. Thus the equality from step 1 becomes the displayed equality.
The sheaf and module localizations are separate, so their universe levels can differ.
This is an equality of maps, not an invertibility statement: E=0, identity maps,
empty schemes, and nonflat g all satisfy it without extra assumptions. -/
theorem mixedSectionsBaseChange_unit_square
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (E : schemeDerivedCategory X) :
    (schemeDerivedGlobalSections Y).map
        ((schemeHomPullbackAdjunction g).unit.app ((schemeDerivedDirectImage f).obj E)) ≫
      (mixedGlobalSectionsDirectImageIso g).hom.app
        ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj E)) ≫
      (schemeGlobalScalarRestriction g).map
        ((schemeDerivedGlobalSections Y').map
            (schemeDerivedBaseChangeMap f (pullback.snd f g) g
              (pullback.fst f g) pullback.condition E) ≫
          (mixedGlobalSectionsDirectImageIso (pullback.snd f g)).hom.app
            ((derivedPullback (pullback.fst f g)).obj E)) =
      (mixedGlobalSectionsDirectImageIso f).hom.app E ≫
        (schemeGlobalScalarRestriction f).map
          ((schemeDerivedGlobalSections X).map
              ((schemeHomPullbackAdjunction (pullback.fst f g)).unit.app E) ≫
            (mixedGlobalSectionsDirectImageIso (pullback.fst f g)).hom.app
              ((derivedPullback (pullback.fst f g)).obj E)) ≫
        (schemeGlobalScalarSquareIso f (pullback.snd f g) g (pullback.fst f g)
          pullback.condition).hom.app
            ((schemeDerivedGlobalSections (pullback f g)).obj
              ((derivedPullback (pullback.fst f g)).obj E)) := by
  classical
  let a := fun {A D : Scheme.{u}} (h : A ⟶ D) ↦ schemeHomPullbackAdjunction h
  let p := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))
  let k := p (pullback.snd f g) g ≪≫
    eqToIso (congrArg (fun h ↦ derivedPullback h)
      (pullback.condition (f := f) (g := g)).symm) ≪≫
        (p (pullback.fst f g) f).symm
  let δ := conjugateEquiv ((a f).comp (a (pullback.fst f g)))
    ((a g).comp (a (pullback.snd f g))) k.hom
  have hu := mixed_mate_unit_square (a f) (a (pullback.snd f g))
    (a g) (a (pullback.fst f g)) k.hom E
  have hβ : (a (pullback.snd f g)).homEquiv _ _
      (k.hom.app ((schemeDerivedDirectImage f).obj E) ≫
        (derivedPullback (pullback.fst f g)).map ((a f).counit.app E)) =
      schemeDerivedBaseChangeMap f (pullback.snd f g) g
        (pullback.fst f g) pullback.condition E := by
    simp only [k, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app,
      Iso.symm_hom, Category.assoc]
    rfl
  rw [hβ] at hu
  change (a g).unit.app ((schemeDerivedDirectImage f).obj E) ≫
      (schemeDerivedDirectImage g).map
        (schemeDerivedBaseChangeMap f (pullback.snd f g) g
          (pullback.fst f g) pullback.condition E) =
    (schemeDerivedDirectImage f).map ((a (pullback.fst f g)).unit.app E) ≫
      δ.app ((derivedPullback (pullback.fst f g)).obj E) at hu
  exact mixed_sections_paste
    (schemeDerivedDirectImage f) (schemeDerivedDirectImage g)
    (schemeDerivedDirectImage (pullback.snd f g))
    (schemeDerivedDirectImage (pullback.fst f g))
    (schemeDerivedGlobalSections Y) (schemeDerivedGlobalSections Y')
    (schemeDerivedGlobalSections X) (schemeDerivedGlobalSections (pullback f g))
    (schemeGlobalScalarRestriction g) (schemeGlobalScalarRestriction f)
    (schemeGlobalScalarRestriction (pullback.snd f g))
    (schemeGlobalScalarRestriction (pullback.fst f g))
    (mixedGlobalSectionsDirectImageIso g).hom (mixedGlobalSectionsDirectImageIso f).hom
    (mixedGlobalSectionsDirectImageIso (pullback.snd f g)).hom
    (mixedGlobalSectionsDirectImageIso (pullback.fst f g)).hom
    (schemeGlobalScalarSquareIso f (pullback.snd f g) g (pullback.fst f g)
      pullback.condition).hom
    ((a g).unit.app ((schemeDerivedDirectImage f).obj E))
    (schemeDerivedBaseChangeMap f (pullback.snd f g) g
      (pullback.fst f g) pullback.condition E)
    ((a (pullback.fst f g)).unit.app E)
    (δ.app ((derivedPullback (pullback.fst f g)).obj E)) hu
    (mixedSections_square_comparison_coherence f g
      ((derivedPullback (pullback.fst f g)).obj E))

end AlgebraicGeometry
