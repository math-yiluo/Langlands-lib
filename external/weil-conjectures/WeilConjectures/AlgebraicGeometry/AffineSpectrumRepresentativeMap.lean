/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

public import WeilConjectures.AlgebraicGeometry.AffineSpectrumDerivedCoordinates
public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso
import all WeilConjectures.AlgebraicGeometry.AffineSpectrumCompositionCounitSquare

/-! # Chain-map transport for affine spectrum representatives

Source: Stacks Project, Tags 0DJ8 and 0D5S.
(blueprint: lem-pc-affine-spectrum-representative-map).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory
namespace AlgebraicGeometry.SingleComplexBaseChange

attribute [local irreducible] Scheme.Modules.tensorPullbackCompositionIso
  Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj

private theorem transport_representative
    {C₀ C₁ D₀ D₁ E : Type*}
    [Category C₀] [Category C₁] [Category D₀] [Category D₁] [Category E]
    (J : C₀ ⥤ D₀) (S : D₀ ⥤ D₁) (G : C₀ ⥤ C₁) (J' : C₁ ⥤ D₁)
    (Q : E ⥤ D₁) (α : J ⋙ S ≅ G ⋙ J')
    {P K : C₀} {N K' M : C₁} {p : D₀} {A B C : E}
    (eP : P ≅ K) (eN : N ≅ K') (e : p ≅ J.obj K) (e' : Q.obj C ≅ J'.obj K')
    (φ : G.obj K ⟶ K') (ej : J.obj P ⟶ p) (eg : G.obj P ⟶ M)
    (ej' : J'.obj N ⟶ Q.obj C) (ejg : J'.obj M ⟶ Q.obj B)
    (es : S.obj p ⟶ Q.obj A) (a : A ⟶ B) (t : B ⟶ C) (qt : M ⟶ N)
    (he : e.inv = J.map eP.inv ≫ ej) (he' : e'.inv = J'.map eN.inv ≫ ej')
    (hrep : eg ≫ qt ≫ eN.hom = G.map eP.hom ≫ φ)
    (hsq : S.map ej ≫ es ≫ Q.map a =
      α.hom.app P ≫ J'.map eg ≫ ejg)
    (hnat : ejg ≫ Q.map t = J'.map qt ≫ ej') :
    es ≫ Q.map (a ≫ t) ≫ e'.hom = S.map e.hom ≫ α.hom.app K ≫ J'.map φ := by
  have hφ : φ ≫ eN.inv = G.map eP.inv ≫ eg ≫ qt := by
    have h := congrArg (fun f ↦ G.map eP.inv ≫ f ≫ eN.inv) hrep
    have hc : G.map eP.inv ≫ G.map eP.hom = 𝟙 _ := by
      rw [← G.map_comp, Iso.inv_hom_id, G.map_id]
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
      reassoc_of% hc, Category.id_comp] using h.symm
  apply (cancel_mono e'.inv).mp
  apply (cancel_epi (S.map e.inv)).mp
  have hc : S.map e.inv ≫ S.map e.hom = 𝟙 _ := by
    rw [← S.map_comp, Iso.inv_hom_id, S.map_id]
  simp only [Q.map_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id,
    reassoc_of% hc]
  rw [he, he', S.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hsq, hnat]
  have hn := α.hom.naturality eP.inv
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  simp only [← J'.map_comp_assoc]
  rw [hφ]

private theorem remove_comparison_identities
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B : D} {P : C} (f : A ⟶ F.obj P) (g : F.obj P ⟶ B) :
    f ≫ F.map (𝟙 P) ≫ g ≫ 𝟙 B = f ≫ g := by
  simp
private theorem counit_naturality_complex
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {Y Z : Scheme.{u}} (k : Y ⟶ Z)
    {P N : CochainComplex (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) ℤ}
    (f : P ⟶ N) :
    (derivedPullback k).map (DerivedCategory.Q.map f) ≫
      (counit k).app ((HomotopyCategory.quotient _ (.up ℤ)).obj N) =
    (counit k).app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        (((Scheme.Modules.tensorPullback k).mapHomologicalComplex (.up ℤ)).map f) := by
  let : HasDerivedCategory.{w} Y.Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
  have h := (counit k).naturality ((HomotopyCategory.quotient _ (.up ℤ)).map f)
  change (derivedPullback k).map (DerivedCategory.Q.map f) ≫ _ = _ ≫
    DerivedCategory.Qh.map
      (((Scheme.Modules.tensorPullback k).mapHomotopyCategory (.up ℤ)).map
        ((HomotopyCategory.quotient _ (.up ℤ)).map f)) at h
  rw [Functor.mapHomotopyCategory_map] at h
  exact h

/-- Canonical representative identifications transport the coefficient chain map.

Proof: Set j=X.isoSpec.inv and j'=X'.isoSpec.inv. Naturality of isoSpec gives
(Spec.map g'.appTop) ≫ j = j' ≫ g'. The conjugates of pushforward composition
under the pinned tensor-pullback adjunctions give the underived composition
isomorphisms. Map these to complexes and combine them with the equality of
composite scheme maps to obtain an isomorphism from (Spec.map g'.appTop)*j*P
to j'*(g'*P). Compose its hom with j'*c.t to obtain t. The two assumptions on
e and e' say precisely that their inverses are the derived images of c.e.inv
and c.e'.inv followed by the pinned counits, with the quotient/localization
comparison isomorphisms inserted. Naturality of those comparisons and of the
counits, the leftDerivedLift factorization equations defining the two derived
composition comparisons, and c.represents identify Q(t) with the transported
coefficient. Cancel the invertible e and e' to obtain the displayed equation.
This construction uses no arbitrary lift of a morphism into the derived
category, no K-injectivity of N, and no quasi-coherence. Zero complexes and
empty schemes obey the same composition equations.
Source: Stacks Project, Tag 0DJ8, affine reduction; Tag 0D5S, composition of
pullbacks and compatibility of the derived counits.
(blueprint: lem-pc-affine-spectrum-representative-map). -/
private theorem affineSpectrum_representative_map_eq_aux
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' : Scheme.{u}} [IsAffine X] [IsAffine X']
    (g' : X' ⟶ X) (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K') (c : Coordinates g' K K' φ)
    (e : (DerivedCategory.Q.obj
      (((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
        (.up ℤ)).obj c.P) : schemeDerivedCategory (Spec Γ(X, ⊤))) ≅
      affineSpectrumDerivedObject X K)
    (e' : (DerivedCategory.Q.obj
      (((Scheme.Modules.tensorPullback X'.isoSpec.inv).mapHomologicalComplex
        (.up ℤ)).obj c.N) : schemeDerivedCategory (Spec Γ(X', ⊤))) ≅
      affineSpectrumDerivedObject X' K')
    (he : e.inv = (derivedPullback X.isoSpec.inv).map c.e.inv ≫
      (derivedPullback X.isoSpec.inv).map
        ((DerivedCategory.quotientCompQhIso _).inv.app c.P) ≫
      (counit X.isoSpec.inv).app ((HomotopyCategory.quotient _ (.up ℤ)).obj c.P) ≫
      (DerivedCategory.quotientCompQhIso _).hom.app _)
    (he' : e'.inv = (derivedPullback X'.isoSpec.inv).map c.e'.inv ≫
      (derivedPullback X'.isoSpec.inv).map
        ((DerivedCategory.quotientCompQhIso _).inv.app c.N) ≫
      (counit X'.isoSpec.inv).app ((HomotopyCategory.quotient _ (.up ℤ)).obj c.N) ≫
      (DerivedCategory.quotientCompQhIso _).hom.app _) :
    let a : Scheme.Modules.tensorPullback X.isoSpec.inv ⋙
        Scheme.Modules.tensorPullback (Spec.map g'.appTop) ≅
        Scheme.Modules.tensorPullback g' ⋙ Scheme.Modules.tensorPullback X'.isoSpec.inv :=
      (Scheme.Modules.tensorPullbackCompositionIso (Spec.map g'.appTop) X.isoSpec.inv
        ((Spec.map g'.appTop) ≫ X.isoSpec.inv) rfl).symm ≪≫
      Scheme.Modules.tensorPullbackCompositionIso X'.isoSpec.inv g'
        ((Spec.map g'.appTop) ≫ X.isoSpec.inv) (Scheme.isoSpec_inv_naturality g').symm
    let t : ((Scheme.Modules.tensorPullback (Spec.map g'.appTop)).mapHomologicalComplex
        (.up ℤ)).obj
      (((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
        (.up ℤ)).obj c.P) ⟶
      ((Scheme.Modules.tensorPullback X'.isoSpec.inv).mapHomologicalComplex
        (.up ℤ)).obj c.N :=
      (NatIso.mapHomologicalComplex a (.up ℤ)).hom.app c.P ≫
      ((Scheme.Modules.tensorPullback X'.isoSpec.inv).mapHomologicalComplex
        (.up ℤ)).map c.t
    (counit (Spec.map g'.appTop)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj
            (((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
              (.up ℤ)).obj c.P)) ≫
        (DerivedCategory.Q (C := SheafOfModules.{u}
          (moduleRings (Spec Γ(X', ⊤)).toRingedSpace))).map t ≫ e'.hom =
        (derivedPullback (Spec.map g'.appTop)).map e.hom ≫
          affineSpectrumDerivedMorphism g' K K' φ := by
  classical
  let (Y : Scheme.{u}) : HasDerivedCategory.{w} Y.Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
  change e.inv = (derivedPullback X.isoSpec.inv).map c.e.inv ≫
    (derivedPullback X.isoSpec.inv).map (𝟙 (DerivedCategory.Q.obj c.P)) ≫
    (counit X.isoSpec.inv).app ((HomotopyCategory.quotient _ (.up ℤ)).obj c.P) ≫
    𝟙 ((DerivedCategory.Q.{w}
      (C := SheafOfModules.{u} (moduleRings (Spec Γ(X, ⊤)).toRingedSpace))).obj
      (((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex (.up ℤ)).obj
        c.P)) at he
  change e'.inv = (derivedPullback X'.isoSpec.inv).map c.e'.inv ≫
    (derivedPullback X'.isoSpec.inv).map (𝟙 (DerivedCategory.Q.obj c.N)) ≫
    (counit X'.isoSpec.inv).app ((HomotopyCategory.quotient _ (.up ℤ)).obj c.N) ≫
    𝟙 ((DerivedCategory.Q.{w}
      (C := SheafOfModules.{u} (moduleRings (Spec Γ(X', ⊤)).toRingedSpace))).obj
      (((Scheme.Modules.tensorPullback X'.isoSpec.inv).mapHomologicalComplex (.up ℤ)).obj
        c.N)) at he'
  have he0 := he.trans (remove_comparison_identities _ _ _)
  have he0' := he'.trans (remove_comparison_identities _ _ _)
  dsimp only
  exact transport_representative
    (derivedPullback X.isoSpec.inv) (derivedPullback (Spec.map g'.appTop))
    (derivedPullback g') (derivedPullback X'.isoSpec.inv) DerivedCategory.Q
    (affineSpectrumDerivedPullbackIso g') c.e c.e' e e' φ
    ((counit X.isoSpec.inv).app ((HomotopyCategory.quotient _ (.up ℤ)).obj c.P))
    ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj c.P))
    ((counit X'.isoSpec.inv).app ((HomotopyCategory.quotient _ (.up ℤ)).obj c.N))
    ((counit X'.isoSpec.inv).app ((HomotopyCategory.quotient _ (.up ℤ)).obj
      (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj c.P)))
    _ _ _ (DerivedCategory.Q.map c.t) he0 he0' c.represents
    (affineSpectrum_composition_counit_square g' c.P)
    (counit_naturality_complex X'.isoSpec.inv c.t).symm


private theorem counit_naturality_complex_restored
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {Y Z : Scheme.{u}} (k : Y ⟶ Z)
    {P N : CochainComplex (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) ℤ}
    (f : P ⟶ N) :
    (derivedPullback k).map (DerivedCategory.Q.map f) ≫
      (counit k).app ((HomotopyCategory.quotient _ (.up ℤ)).obj N) =
    (counit k).app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        (((Scheme.Modules.tensorPullback k).mapHomologicalComplex (.up ℤ)).map f) := by
  let : HasDerivedCategory.{w} Y.Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
  have h := (counit k).naturality ((HomotopyCategory.quotient _ (.up ℤ)).map f)
  change (derivedPullback k).map (DerivedCategory.Q.map f) ≫ _ = _ ≫
    DerivedCategory.Qh.map
      (((Scheme.Modules.tensorPullback k).mapHomotopyCategory (.up ℤ)).map
        ((HomotopyCategory.quotient _ (.up ℤ)).map f)) at h
  rw [Functor.mapHomotopyCategory_map] at h
  exact h

/-- Canonical representative identifications transport the coefficient chain map.

Proof: Set j=X.isoSpec.inv and j'=X'.isoSpec.inv. Naturality of isoSpec gives
(Spec.map g'.appTop) ≫ j = j' ≫ g'. The conjugates of pushforward composition
under the pinned tensor-pullback adjunctions give the underived composition
isomorphisms. Map these to complexes and combine them with the equality of
composite scheme maps to obtain an isomorphism from (Spec.map g'.appTop)*j*P
to j'*(g'*P). Compose its hom with j'*c.t to obtain t. The two assumptions on
e and e' say precisely that their inverses are the derived images of c.e.inv
and c.e'.inv followed by the pinned counits, with the quotient/localization
comparison isomorphisms inserted. Naturality of those comparisons and of the
counits, the leftDerivedLift factorization equations defining the two derived
composition comparisons, and c.represents identify Q(t) with the transported
coefficient. Cancel the invertible e and e' to obtain the displayed equation.
This construction uses no arbitrary lift of a morphism into the derived
category, no K-injectivity of N, and no quasi-coherence. Zero complexes and
empty schemes obey the same composition equations.
Source: Stacks Project, Tag 0DJ8, affine reduction; Tag 0D5S, composition of
pullbacks and compatibility of the derived counits.
(blueprint: lem-pc-affine-spectrum-representative-map). -/
theorem affineSpectrum_representative_map_eq
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' : Scheme.{u}} [IsAffine X] [IsAffine X']
    (g' : X' ⟶ X) (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K') (c : Coordinates g' K K' φ)
    (e : (DerivedCategory.Q.obj
      (((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
        (.up ℤ)).obj c.P) : schemeDerivedCategory (Spec Γ(X, ⊤))) ≅
      affineSpectrumDerivedObject X K)
    (e' : (DerivedCategory.Q.obj
      (((Scheme.Modules.tensorPullback X'.isoSpec.inv).mapHomologicalComplex
        (.up ℤ)).obj c.N) : schemeDerivedCategory (Spec Γ(X', ⊤))) ≅
      affineSpectrumDerivedObject X' K')
    (he : e.inv = (derivedPullback X.isoSpec.inv).map c.e.inv ≫
      (derivedPullback X.isoSpec.inv).map
        ((DerivedCategory.quotientCompQhIso _).inv.app c.P) ≫
      (counit X.isoSpec.inv).app ((HomotopyCategory.quotient _ (.up ℤ)).obj c.P) ≫
      (DerivedCategory.quotientCompQhIso _).hom.app _)
    (he' : e'.inv = (derivedPullback X'.isoSpec.inv).map c.e'.inv ≫
      (derivedPullback X'.isoSpec.inv).map
        ((DerivedCategory.quotientCompQhIso _).inv.app c.N) ≫
      (counit X'.isoSpec.inv).app ((HomotopyCategory.quotient _ (.up ℤ)).obj c.N) ≫
      (DerivedCategory.quotientCompQhIso _).hom.app _) :
    let a : Scheme.Modules.tensorPullback X.isoSpec.inv ⋙
        Scheme.Modules.tensorPullback (Spec.map g'.appTop) ≅
        Scheme.Modules.tensorPullback g' ⋙ Scheme.Modules.tensorPullback X'.isoSpec.inv :=
      (Scheme.Modules.tensorPullbackCompositionIso (Spec.map g'.appTop) X.isoSpec.inv
        ((Spec.map g'.appTop) ≫ X.isoSpec.inv) rfl).symm ≪≫
      Scheme.Modules.tensorPullbackCompositionIso X'.isoSpec.inv g'
        ((Spec.map g'.appTop) ≫ X.isoSpec.inv) (Scheme.isoSpec_inv_naturality g').symm
    let t : ((Scheme.Modules.tensorPullback (Spec.map g'.appTop)).mapHomologicalComplex
        (.up ℤ)).obj
      (((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
        (.up ℤ)).obj c.P) ⟶
      ((Scheme.Modules.tensorPullback X'.isoSpec.inv).mapHomologicalComplex
        (.up ℤ)).obj c.N :=
      (NatIso.mapHomologicalComplex a (.up ℤ)).hom.app c.P ≫
      ((Scheme.Modules.tensorPullback X'.isoSpec.inv).mapHomologicalComplex
        (.up ℤ)).map c.t
    cast (by rfl) ((counit (Spec.map g'.appTop)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj
            (((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
              (.up ℤ)).obj c.P))) ≫
        (DerivedCategory.Q (C := SheafOfModules.{u}
          (moduleRings (Spec Γ(X', ⊤)).toRingedSpace))).map t ≫ e'.hom =
        (derivedPullback (Spec.map g'.appTop)).map e.hom ≫
          affineSpectrumDerivedMorphism g' K K' φ := by
  with_unfolding_all
    exact affineSpectrum_representative_map_eq_aux g' K K' φ c e e' he he'

end AlgebraicGeometry.SingleComplexBaseChange

