/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenCounitCompatibility
public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenSquareComparison

/-! # Coherence of open pullback squares

Source: Stacks Project, Tag 0D5S, and Tag 0DJ9, first paragraph.
(blueprint: lem-pc-t2-open-pullback-cube).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private noncomputable def compositionOfEq
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C)
    (t : A ⟶ C) (h : a ≫ b = t) :
    derivedPullback b ⋙ derivedPullback a ≅ derivedPullback t :=
  singleComplexOpenPinnedComposition a b ≪≫
    eqToIso (congrArg (fun k ↦ derivedPullback k) h)

private theorem compositionOfEq_assoc
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {A B C D : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D)
    (ab : A ⟶ C) (bc : B ⟶ D) (t : A ⟶ D)
    (hab : a ≫ b = ab) (hbc : b ≫ c = bc)
    (ht : ab ≫ c = t) (ht' : a ≫ bc = t) (M : schemeDerivedCategory D) :
    (compositionOfEq a b ab hab).hom.app ((derivedPullback c).obj M) ≫
      (compositionOfEq ab c t ht).hom.app M =
    (derivedPullback a).map ((compositionOfEq b c bc hbc).hom.app M) ≫
      (compositionOfEq a bc t ht').hom.app M := by
  classical
  subst ab bc t
  have hc := (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition)))).2.choose_spec.2.2 a b c
  have hh := congrArg (fun z ↦ z.hom.app M) hc
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, eqToIso.hom, eqToHom_app,
    Functor.comp_obj, Category.id_comp] at hh
  dsimp only [compositionOfEq, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom,
    eqToHom_app]
  simp only [eqToHom_refl, NatTrans.id_app, Category.comp_id]
  apply (cancel_mono (eqToHom (congrArg
    (fun k ↦ (derivedPullback k).obj M) (Category.assoc a b c)))).mp
  simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using hh.symm

private noncomputable def pullbackSquare
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {A B C D : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ D)
    (d : A ⟶ C) (e : C ⟶ D) (h : a ≫ b = d ≫ e) :
    derivedPullback b ⋙ derivedPullback a ⟶ derivedPullback e ⋙ derivedPullback d :=
  (compositionOfEq a b (d ≫ e) h).hom ≫
    (compositionOfEq d e (d ≫ e) rfl).inv

private theorem pullbackSquare_cube
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' U U' V V' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g)
    (iU : U ⟶ X) (iU' : U' ⟶ X') (iV : V ⟶ S) (iV' : V' ⟶ S')
    (f₀ : U ⟶ V) (f₀' : U' ⟶ V') (g₀ : V' ⟶ V) (j : U' ⟶ U)
    (hd : f₀ ≫ iV = iU ≫ f) (hd' : f₀' ≫ iV' = iU' ≫ f')
    (he : g₀ ≫ iV = iV' ≫ g) (hj : j ≫ iU = iU' ≫ g')
    (h₀ : j ≫ f₀ = f₀' ≫ g₀) (M : schemeDerivedCategory S) :
    (pullbackSquare f₀' g₀ j f₀ h₀.symm).app ((derivedPullback iV).obj M) ≫
        (derivedPullback j).map ((pullbackSquare f₀ iV iU f hd).app M) ≫
        (pullbackSquare j iU iU' g' hj).app ((derivedPullback f).obj M) =
      (derivedPullback f₀').map ((pullbackSquare g₀ iV iV' g he).app M) ≫
        (pullbackSquare f₀' iV' iU' f' hd').app ((derivedPullback g).obj M) ≫
        (derivedPullback iU').map ((pullbackSquare f' g g' f h.symm).app M) := by
  classical
  let t := j ≫ (iU ≫ f)
  have ht₄ : (iU' ≫ g') ≫ f = t := by
    dsimp only [t]
    rw [← hj, Category.assoc]
  have ht₅ : (j ≫ f₀) ≫ iV = t := by
    dsimp only [t]
    rw [Category.assoc, hd]
  have ht₃ : f₀' ≫ (iV' ≫ g) = t := by
    dsimp only [t]
    rw [← he, ← Category.assoc, ← h₀, Category.assoc, hd]
  have ht₂ : (iU' ≫ f') ≫ g = t := by
    rw [Category.assoc, ← h, ← Category.assoc, ht₄]
  have ht₆ : iU' ≫ (g' ≫ f) = t := by
    rw [← Category.assoc, ht₄]
  have ha := compositionOfEq_assoc j iU f (iU' ≫ g') (iU ≫ f) t
    hj rfl ht₄ rfl M
  have hb := compositionOfEq_assoc j f₀ iV (j ≫ f₀) (iU ≫ f) t
    rfl hd ht₅ rfl M
  have hc := compositionOfEq_assoc f₀' g₀ iV (j ≫ f₀) (iV' ≫ g) t
    h₀.symm he ht₅ ht₃ M
  have hd₁ := compositionOfEq_assoc iU' g' f (iU' ≫ g') (g' ≫ f) t
    rfl rfl ht₄ ht₆ M
  have hd₂ := compositionOfEq_assoc iU' f' g (iU' ≫ f') (g' ≫ f) t
    rfl h.symm ht₂ ht₆ M
  have hd₃ := compositionOfEq_assoc f₀' iV' g (iU' ≫ f') (iV' ≫ g) t
    hd' rfl ht₂ ht₃ M
  apply (cancel_mono
    ((compositionOfEq iU' g' (iU' ≫ g') rfl).hom.app ((derivedPullback f).obj M) ≫
      (compositionOfEq (iU' ≫ g') f t ht₄).hom.app M)).mp
  simp only [pullbackSquare, NatTrans.comp_app, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  rw [ha]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Category.comp_id]
  simp only [Functor.map_comp, Category.assoc]
  rw [← hb]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [hc]
  rw [hd₁]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Category.comp_id]
  simp only [Functor.map_comp, Category.assoc]
  rw [← hd₂]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [hd₃]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Category.comp_id]

private theorem squareComparison_eq
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g) :
    singleComplexOpenSquareComparison f f' g g' h =
      pullbackSquare f' g g' f h.symm := by
  ext M
  simp only [singleComplexOpenSquareComparison, pullbackSquare, compositionOfEq,
    NatTrans.comp_app, Iso.trans_hom, Iso.trans_inv, eqToIso.hom, eqToIso.inv,
    eqToHom_app, eqToHom_refl, Category.id_comp, Category.assoc]

private theorem openSquare_app
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (s : X ⟶ Y) (U : Y.Opens) (U' : X.Opens)
    (j : U'.toScheme ⟶ U.toScheme) (hj : j ≫ U.ι = U'.ι ≫ s)
    (M : schemeDerivedCategory Y) :
    (singleComplexOpenPullbackSquareIso s U U' j hj).hom.app M =
      (derivedPullback j).map ((singleComplexOpenPullbackIso Y U).inv.app M) ≫
        (pullbackSquare j U.ι U'.ι s hj).app M ≫
          (singleComplexOpenPullbackIso X U').hom.app ((derivedPullback s).obj M) := by
  simp only [singleComplexOpenPullbackSquareIso, NatIso.ofComponents_hom_app,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom,
    pullbackSquare, compositionOfEq, NatTrans.comp_app, eqToIso.hom,
    eqToHom_app, Iso.trans_inv, eqToIso.inv, eqToHom_refl,
    Category.id_comp, Category.assoc]

/-- The two paths around a commuting cube of pullback comparisons agree.
Source: Stacks Project, cohomology.tex, Tag 0D5S; perfect.tex, Tag 0DJ9.
(blueprint: lem-pc-t2-open-pullback-cube).

Proof: First extend the pinned two-arrow composition isomorphisms by equality
transport to named composites. Their three-arrow identity follows by substituting
the named composites in the associativity clause of exists_derivedPullbackComposition.
Normalize the six paths j,U.ι,f; j,f restricted,V.ι;
f' restricted,g restricted,V.ι; U'.ι,g',f; U'.ι,f',g;
and f' restricted,V'.ι,g to the common total morphism j ≫ (U.ι ≫ f).
Postcompose both ordinary cube paths with an invertible comparison to that total
pullback, apply the three-arrow identities, and cancel neighboring comparisons.
The commuting-face equations give the required equality transports; their proofs
coincide by proof irrelevance. Expand each open square into inverse open comparison,
ordinary pullback square, and terminal open comparison. Cancel the intermediate
open comparisons. Naturality moves the remaining inverse open comparison on V
to the front and the open comparison on U' to the end. The ordinary cube identity
then proves the displayed equation with these two common factors. The calculation
uses only functoriality and invertible comparisons, hence applies to empty opens,
zero objects, and arbitrary unbounded complexes. No direct image or adjunction
counit occurs in this assertion. -/
theorem singleComplexOpen_pullback_cube
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g)
    (V : S.Opens) (V' : S'.Opens) (hV' : V' ≤ g ⁻¹ᵁ V)
    (j : (f' ⁻¹ᵁ V').toScheme ⟶ (f ⁻¹ᵁ V).toScheme)
    (hj : j ≫ (f ⁻¹ᵁ V).ι = (f' ⁻¹ᵁ V').ι ≫ g')
    (h₀ : j ≫ (f ∣_ V) = (f' ∣_ V') ≫ g.resLE V V' hV')
    (M : schemeDerivedCategory S) :
    let q := singleComplexOpenSquareComparison f f' g g' h
    let q₀ := singleComplexOpenSquareComparison
      (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j h₀
    let RS := (schemeOpenRestriction S V).mapDerivedCategory
    let RX' := (schemeOpenRestriction X' (f' ⁻¹ᵁ V')).mapDerivedCategory
    let d := singleComplexOpenPullbackSquareIso f V (f ⁻¹ᵁ V) (f ∣_ V)
      (morphismRestrict_ι f V)
    let d' := singleComplexOpenPullbackSquareIso f' V' (f' ⁻¹ᵁ V') (f' ∣_ V')
      (morphismRestrict_ι f' V')
    let e := singleComplexOpenPullbackSquareIso g V V' (g.resLE V V' hV')
      (Scheme.Hom.resLE_comp_ι g hV')
    let e' := singleComplexOpenPullbackSquareIso g' (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj
    q₀.app (RS.obj M) ≫ (derivedPullback j).map (d.hom.app M) ≫
        e'.hom.app ((derivedPullback f).obj M) =
      (derivedPullback (f' ∣_ V')).map (e.hom.app M) ≫
        d'.hom.app ((derivedPullback g).obj M) ≫ RX'.map (q.app M) := by
  classical
  intro q q₀ RS RX' d d' e e'
  have H := pullbackSquare_cube f f' g g' h (f ⁻¹ᵁ V).ι (f' ⁻¹ᵁ V').ι V.ι V'.ι
    (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j
    (morphismRestrict_ι f V) (morphismRestrict_ι f' V')
    (Scheme.Hom.resLE_comp_ι g hV') hj h₀ M
  dsimp only [d, d', e, e', RS]
  simp only [openSquare_app f V (f ⁻¹ᵁ V) (f ∣_ V) (morphismRestrict_ι f V) M,
    openSquare_app g' (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj ((derivedPullback f).obj M),
    openSquare_app g V V' (g.resLE V V' hV') (Scheme.Hom.resLE_comp_ι g hV') M,
    openSquare_app f' V' (f' ⁻¹ᵁ V') (f' ∣_ V') (morphismRestrict_ι f' V')
      ((derivedPullback g).obj M)]
  simp only [Functor.map_comp, Category.assoc]
  simp only [← (derivedPullback j).map_comp_assoc
    ((singleComplexOpenPullbackIso X (f ⁻¹ᵁ V)).hom.app ((derivedPullback f).obj M))
    ((singleComplexOpenPullbackIso X (f ⁻¹ᵁ V)).inv.app ((derivedPullback f).obj M)),
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [← (derivedPullback (f' ∣_ V')).map_comp_assoc
    ((singleComplexOpenPullbackIso S' V').hom.app ((derivedPullback g).obj M))
    ((singleComplexOpenPullbackIso S' V').inv.app ((derivedPullback g).obj M)),
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  have hn := q₀.naturality ((singleComplexOpenPullbackIso S V).inv.app M)
  simp only [Functor.comp_map] at hn
  simp only [← reassoc_of% hn]
  have hn' := (singleComplexOpenPullbackIso X' (f' ⁻¹ᵁ V')).hom.naturality (q.app M)
  simp only [Functor.comp_obj] at hn'
  dsimp only [RX']
  simp only [← hn']
  have hq := squareComparison_eq f f' g g' h
  have hq₀ := squareComparison_eq (f ∣_ V) (f' ∣_ V')
    (g.resLE V V' hV') j h₀
  dsimp only [q, q₀]
  simp only [hq, hq₀]
  simpa only [Category.assoc] using congrArg (fun z ↦
    (derivedPullback (f' ∣_ V')).map
        ((derivedPullback (g.resLE V V' hV')).map
          ((singleComplexOpenPullbackIso S V).inv.app M)) ≫
      z ≫ (singleComplexOpenPullbackIso X' (f' ⁻¹ᵁ V')).hom.app
        ((derivedPullback g').obj ((derivedPullback f).obj M))) H

end AlgebraicGeometry
