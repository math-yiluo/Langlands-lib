/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineSpectrumDirectImageCoordinates

/-! # Affine spectrum composition unit square

Source: Stacks Project, Tag 0D5S, composition coherence used in the affine reduction.
(blueprint: lem-pc-affine-spectrum-composition-unit-square).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w z
open CategoryTheory
-- Prove the coherence calculation with abstract functors, so its algebra does not
-- unfold the constructions of derived categories or derived pullback.
namespace AffineSpectrumCoherence
variable {S : Type u} [Category.{v} S]
  {D : S → Type w} [∀ X, Category.{z} (D X)]
  (F : ∀ {X Y : S}, (X ⟶ Y) → (D Y ⥤ D X))
  (c : ∀ {X Y Z : S} (f : X ⟶ Y) (g : Y ⟶ Z), F g ⋙ F f ≅ F (f ≫ g))
  (i : ∀ X : S, F (𝟙 X) ≅ 𝟭 (D X))

private noncomputable def tc {P Q Z : S} (k : P ⟶ Q) (l : Q ⟶ Z)
    (m : P ⟶ Z) (e : k ≫ l = m) : F l ⋙ F k ≅ F m :=
  c k l ≪≫ eqToIso (congrArg F e)

private theorem tc_refl {P Q Z : S} (k : P ⟶ Q) (l : Q ⟶ Z) :
    tc F c k l (k ≫ l) rfl = c k l := by
  simp only [tc, eqToIso_refl, Iso.trans_refl]

private theorem tc_assoc
    (hc : ∀ {W X Y Z : S} (h : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z),
      Functor.isoWhiskerRight (c f g) (F h) ≪≫ c h (f ≫ g) =
        Functor.associator (F g) (F f) (F h) ≪≫
          Functor.isoWhiskerLeft (F g) (c h f) ≪≫ c (h ≫ f) g ≪≫
            eqToIso (congrArg F (Category.assoc h f g)))
    {W X Y Z : S} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (a : W ⟶ Y) (b : X ⟶ Z) (t : W ⟶ Z)
    (ha : f ≫ g = a) (hb : g ≫ h = b)
    (ht : a ≫ h = t) (hs : f ≫ b = t) (K : D Z) :
    (tc F c f g a ha).hom.app ((F h).obj K) ≫
        (tc F c a h t ht).hom.app K =
      (F f).map ((tc F c g h b hb).hom.app K) ≫
        (tc F c f b t hs).hom.app K := by
  rcases ha with rfl
  rcases hb with rfl
  rcases hs with rfl
  have he := congrArg (fun e ↦ e.hom.app K) (hc f g h)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp] at he
  simpa only [tc, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom,
    eqToHom_refl, NatTrans.id_app, Category.comp_id, Category.assoc] using he.symm

private theorem tc_id_left
    (hl : ∀ {X Y : S} (f : X ⟶ Y), c (𝟙 X) f ≪≫
      eqToIso (congrArg F (Category.id_comp f)) =
      Functor.isoWhiskerLeft (F f) (i X) ≪≫ Functor.rightUnitor (F f))
    {X Y : S} (f : X ⟶ Y) (K : D Y) :
    (tc F c (𝟙 X) f f (Category.id_comp f)).hom.app K =
      (i X).hom.app ((F f).obj K) := by
  have he := congrArg (fun e ↦ e.hom.app K) (hl f)
  simpa only [tc, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Functor.id_obj, Functor.comp_obj,
    Category.comp_id] using he

private theorem tc_id_right
    (hr : ∀ {X Y : S} (f : X ⟶ Y), c f (𝟙 Y) ≪≫
      eqToIso (congrArg F (Category.comp_id f)) =
      Functor.isoWhiskerRight (i Y) (F f) ≪≫ Functor.leftUnitor (F f))
    {X Y : S} (f : X ⟶ Y) (K : D Y) :
    (tc F c f (𝟙 Y) f (Category.comp_id f)).hom.app K =
      (F f).map ((i Y).hom.app K) := by
  have he := congrArg (fun e ↦ e.hom.app K) (hr f)
  simpa only [tc, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Functor.id_obj, Functor.comp_obj,
    Category.comp_id] using he

private theorem c_square {A B C E : S} (g : A ⟶ B) (h : B ⟶ C)
    (h' : A ⟶ E) (q : E ⟶ C) (e : g ≫ h = h' ≫ q) :
    c g h ≪≫ eqToIso (congrArg F e) ≪≫ (c h' q).symm =
      c g h ≪≫ (tc F c h' q (g ≫ h) e.symm).symm := by
  apply Iso.ext
  simp only [tc, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, eqToIso.hom, eqToIso.inv]

private theorem square
    (hl : ∀ {X Y : S} (f : X ⟶ Y), c (𝟙 X) f ≪≫
      eqToIso (congrArg F (Category.id_comp f)) =
      Functor.isoWhiskerLeft (F f) (i X) ≪≫ Functor.rightUnitor (F f))
    (hr : ∀ {X Y : S} (f : X ⟶ Y), c f (𝟙 Y) ≪≫
      eqToIso (congrArg F (Category.comp_id f)) =
      Functor.isoWhiskerRight (i Y) (F f) ≪≫ Functor.leftUnitor (F f))
    (hc : ∀ {W X Y Z : S} (h : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z),
      Functor.isoWhiskerRight (c f g) (F h) ≪≫ c h (f ≫ g) =
        Functor.associator (F g) (F f) (F h) ≪≫
          Functor.isoWhiskerLeft (F g) (c h f) ≪≫ c (h ≫ f) g ≪≫
            eqToIso (congrArg F (Category.assoc h f g)))
    {X X' T T' : S} (g : X' ⟶ X) (h : X ⟶ T) (v : T ⟶ X)
    (h' : X' ⟶ T') (v' : T' ⟶ X') (q : T' ⟶ T)
    (hv : h ≫ v = 𝟙 X) (hv' : h' ≫ v' = 𝟙 X')
    (e₁ : g ≫ h = h' ≫ q) (e₂ : q ≫ v = v' ≫ g) (K : D X) :
    (c g h ≪≫ eqToIso (congrArg F e₁) ≪≫ (c h' q).symm).hom.app ((F v).obj K) ≫
      (F h').map ((c q v ≪≫ eqToIso (congrArg F e₂) ≪≫ (c v' g).symm).hom.app K) ≫
      (tc F c h' v' (𝟙 X') hv' ≪≫ i X').hom.app ((F g).obj K) =
    (F g).map ((tc F c h v (𝟙 X) hv ≪≫ i X).hom.app K) := by
  have ht : (g ≫ h) ≫ v = g := by
    rw [Category.assoc, hv, Category.comp_id]
  have hs : h' ≫ (q ≫ v) = g := by
    rw [← Category.assoc, ← e₁, ht]
  have h₁ := tc_assoc F c hc h' v' g (𝟙 X') (q ≫ v) g hv' e₂.symm
    (Category.id_comp g) hs K
  have h₂ := tc_assoc F c hc h' q v (g ≫ h) (q ≫ v) g e₁.symm rfl ht hs K
  have h₃ := tc_assoc F c hc g h v (g ≫ h) (𝟙 X) g rfl hv ht
    (Category.comp_id g) K
  simp only [tc_refl] at h₂ h₃
  rw [c_square F c g h h' q e₁, c_square F c q v v' g e₂]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp,
    Category.assoc]
  rw [← tc_id_left F c i hl g K, ← tc_id_right F c i hr g K]
  rw [h₁]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [← h₂]
  simp only [Iso.inv_hom_id_app_assoc]
  exact h₃

private theorem square_expanded
    (hl : ∀ {X Y : S} (f : X ⟶ Y), c (𝟙 X) f ≪≫
      eqToIso (congrArg F (Category.id_comp f)) =
      Functor.isoWhiskerLeft (F f) (i X) ≪≫ Functor.rightUnitor (F f))
    (hr : ∀ {X Y : S} (f : X ⟶ Y), c f (𝟙 Y) ≪≫
      eqToIso (congrArg F (Category.comp_id f)) =
      Functor.isoWhiskerRight (i Y) (F f) ≪≫ Functor.leftUnitor (F f))
    (hc : ∀ {W X Y Z : S} (h : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z),
      Functor.isoWhiskerRight (c f g) (F h) ≪≫ c h (f ≫ g) =
        Functor.associator (F g) (F f) (F h) ≪≫
          Functor.isoWhiskerLeft (F g) (c h f) ≪≫ c (h ≫ f) g ≪≫
            eqToIso (congrArg F (Category.assoc h f g)))
    {X X' T T' : S} (g : X' ⟶ X) (h : X ⟶ T) (v : T ⟶ X)
    (h' : X' ⟶ T') (v' : T' ⟶ X') (q : T' ⟶ T)
    (hv : h ≫ v = 𝟙 X) (hv' : h' ≫ v' = 𝟙 X')
    (e₁ : g ≫ h = h' ≫ q) (e₂ : q ≫ v = v' ≫ g) (K : D X) :
    (c g h ≪≫ eqToIso (congrArg F e₁) ≪≫ (c h' q).symm).hom.app ((F v).obj K) ≫
      (F h').map ((c q v ≪≫ eqToIso (congrArg F e₂) ≪≫ (c v' g).symm).hom.app K) ≫
      (c h' v' ≪≫ eqToIso (congrArg F hv') ≪≫ i X').hom.app ((F g).obj K) =
    (F g).map ((c h v ≪≫ eqToIso (congrArg F hv) ≪≫ i X).hom.app K) := by
  simpa only [tc, Iso.trans_assoc] using
    square F c i hl hr hc g h v h' v' q hv hv' e₁ e₂ K

private theorem square_with_data
    (hl : ∀ {X Y : S} (f : X ⟶ Y), c (𝟙 X) f ≪≫
      eqToIso (congrArg F (Category.id_comp f)) =
      Functor.isoWhiskerLeft (F f) (i X) ≪≫ Functor.rightUnitor (F f))
    (hr : ∀ {X Y : S} (f : X ⟶ Y), c f (𝟙 Y) ≪≫
      eqToIso (congrArg F (Category.comp_id f)) =
      Functor.isoWhiskerRight (i Y) (F f) ≪≫ Functor.leftUnitor (F f))
    (hc : ∀ {W X Y Z : S} (h : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z),
      Functor.isoWhiskerRight (c f g) (F h) ≪≫ c h (f ≫ g) =
        Functor.associator (F g) (F f) (F h) ≪≫
          Functor.isoWhiskerLeft (F g) (c h f) ≪≫ c (h ≫ f) g ≪≫
            eqToIso (congrArg F (Category.assoc h f g)))
    {X X' T T' : S} (g : X' ⟶ X) (h : X ⟶ T) (v : T ⟶ X)
    (h' : X' ⟶ T') (v' : T' ⟶ X') (q : T' ⟶ T)
    (hv : h ≫ v = 𝟙 X) (hv' : h' ≫ v' = 𝟙 X')
    (e₁ : g ≫ h = h' ≫ q) (e₂ : q ≫ v = v' ≫ g) (K : D X)
    (A : F h ⋙ F g ≅ F q ⋙ F h') (B : F v ⋙ F q ≅ F g ⋙ F v')
    (U : F v ⋙ F h ≅ 𝟭 (D X)) (V : F v' ⋙ F h' ≅ 𝟭 (D X'))
    (hA : A = c g h ≪≫ eqToIso (congrArg F e₁) ≪≫ (c h' q).symm)
    (hB : B = c q v ≪≫ eqToIso (congrArg F e₂) ≪≫ (c v' g).symm)
    (hU : U = c h v ≪≫ eqToIso (congrArg F hv) ≪≫ i X)
    (hV : V = c h' v' ≪≫ eqToIso (congrArg F hv') ≪≫ i X') :
    A.hom.app ((F v).obj K) ≫ (F h').map (B.hom.app K) ≫
      V.hom.app ((F g).obj K) = (F g).map (U.hom.app K) := by
  rw [hA, hB, hU, hV]
  exact square_expanded F c i hl hr hc g h v h' v' q hv hv' e₁ e₂ K

end AffineSpectrumCoherence

namespace AlgebraicGeometry

attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj
attribute [local implicit_reducible] Scheme.isoSpec
attribute [local instance_reducible] Scheme.Modules TopCat.Sheaf
attribute [local implicit_reducible] DerivedCategory
  HomotopyCategory DerivedCategory.Q DerivedCategory.Qh

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- Specialize the calculation while c and i are still abstract. Supplying the selected
laws afterward avoids expensive kernel conversions involving the selection predicate. -/
private theorem concrete_square
    {X X' : Scheme.{u}} [IsAffine X] [IsAffine X']
    (g : X' ⟶ X) (K : schemeDerivedCategory X)
    (c : ∀ {P Q Z : Scheme.{u}} (k : P ⟶ Q) (l : Q ⟶ Z),
      derivedPullback l ⋙ derivedPullback k ≅ derivedPullback (k ≫ l))
    (i : ∀ Y : Scheme.{u}, derivedPullback (𝟙 Y) ≅ 𝟭 _)
    (hl : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), c (𝟙 X) f ≪≫
      eqToIso (congrArg (fun k ↦ derivedPullback k) (Category.id_comp f)) =
      Functor.isoWhiskerLeft (derivedPullback f) (i X) ≪≫ Functor.rightUnitor (derivedPullback f))
    (hr : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), c f (𝟙 Y) ≪≫
      eqToIso (congrArg (fun k ↦ derivedPullback k) (Category.comp_id f)) =
      Functor.isoWhiskerRight (i Y) (derivedPullback f) ≪≫ Functor.leftUnitor (derivedPullback f))
    (hc : ∀ {W X Y Z : Scheme.{u}} (h : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z),
      Functor.isoWhiskerRight (c f g) (derivedPullback h) ≪≫ c h (f ≫ g) =
        Functor.associator (derivedPullback g) (derivedPullback f) (derivedPullback h) ≪≫
          Functor.isoWhiskerLeft (derivedPullback g) (c h f) ≪≫ c (h ≫ f) g ≪≫
            eqToIso (congrArg (fun k ↦ derivedPullback k) (Category.assoc h f g)))
    (A : derivedPullback X.toSpecΓ ⋙ derivedPullback g ≅
      derivedPullback (Spec.map g.appTop) ⋙ derivedPullback X'.toSpecΓ)
    (B : derivedPullback X.isoSpec.inv ⋙ derivedPullback (Spec.map g.appTop) ≅
      derivedPullback g ⋙ derivedPullback X'.isoSpec.inv)
    (hA : A = c g X.toSpecΓ ≪≫
      eqToIso (congrArg (fun k ↦ derivedPullback k) (Scheme.toSpecΓ_naturality g)) ≪≫
        (c X'.toSpecΓ (Spec.map g.appTop)).symm)
    (hB : B = c (Spec.map g.appTop) X.isoSpec.inv ≪≫
      eqToIso (congrArg (fun k ↦ derivedPullback k) (Scheme.isoSpec_inv_naturality g)) ≪≫
        (c X'.isoSpec.inv g).symm) :
    A.hom.app ((derivedPullback X.isoSpec.inv).obj K) ≫
      (derivedPullback X'.toSpecΓ).map (B.hom.app K) ≫
      (c X'.isoSpec.hom X'.isoSpec.inv ≪≫
        eqToIso (congrArg (fun k : X' ⟶ X' ↦ derivedPullback k) X'.isoSpec.hom_inv_id) ≪≫
          i X').hom.app ((derivedPullback g).obj K) =
    (derivedPullback g).map ((c X.isoSpec.hom X.isoSpec.inv ≪≫
      eqToIso (congrArg (fun k : X ⟶ X ↦ derivedPullback k) X.isoSpec.hom_inv_id) ≪≫
        i X).hom.app K) := by
  rename_i d hX hX'
  exact AffineSpectrumCoherence.square_with_data
    (D := fun Y : Scheme.{u} ↦ @schemeDerivedCategory.{u, w} Y (d Y))
    (fun {P Q} (k : P ⟶ Q) ↦ @derivedPullback.{u, w} P Q k (d Q) (d P)) c i hl hr hc
    g X.toSpecΓ X.isoSpec.inv X'.toSpecΓ X'.isoSpec.inv
    (Spec.map g.appTop) X.isoSpec.hom_inv_id X'.isoSpec.hom_inv_id
    (Scheme.toSpecΓ_naturality g) (Scheme.isoSpec_inv_naturality g) K A B
    (c X.isoSpec.hom X.isoSpec.inv ≪≫
      eqToIso (congrArg (fun k : X ⟶ X ↦ derivedPullback k) X.isoSpec.hom_inv_id) ≪≫ i X)
    (c X'.isoSpec.hom X'.isoSpec.inv ≪≫
      eqToIso (congrArg (fun k : X' ⟶ X' ↦ derivedPullback k) X'.isoSpec.hom_inv_id) ≪≫ i X')
    hA hB rfl rfl

/-- The comparison square commutes for the unadjointified composition units.
It involves only composition comparisons and identity comparisons, not the
unit chosen by Equivalence.mk.

Proof: write h,h' for the two spectrum maps, v,v' for their inverses, and q
for Spec.map g'.appTop. Transport each composition comparison to a common
composite morphism. Apply associativity to (h',v',g'), (h',q,v), and (g',h,v),
using h;v=id, h';v'=id, g';h=h';q, and q;v=v';g'. The two unit laws identify
the identity-comparison components with the transported comparisons for
(id,g') and (g',id). Substitute the first associativity equation and cancel
the mapped inverse comparison for (v',g'). Substitute the second equation
and cancel the inverse comparison for (h',q). The third equation is exactly
the remaining equality. Equality transport proofs agree by proof irrelevance.
The calculation is first proved for abstract functors and coherent comparison
data, then specialized to the selected derived-pullback comparisons.
Source: Stacks Project, Tag 0D5S, composition coherence; the second step of
the original cancellation node's proof. Tag 08HY explains its base-change use.
(blueprint: lem-pc-affine-spectrum-composition-unit-square). -/
theorem affineSpectrum_composition_unit_square
    {X X' : Scheme.{u}} [IsAffine X] [IsAffine X']
    (g' : X' ⟶ X) (K : schemeDerivedCategory X) :
  let c : ∀ {P Q Z : Scheme.{u}} (k : P ⟶ Q) (l : Q ⟶ Z),
      derivedPullback l ⋙ derivedPullback k ≅ derivedPullback (k ≫ l) :=
    fun k l ↦ (Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))) k l
  let i : ∀ Y : Scheme.{u}, derivedPullback (𝟙 Y) ≅ 𝟭 _ :=
    Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec (Classical.choose_spec exists_derivedPullbackComposition)))).2
  (affineSpectrumForwardPullbackIso g').hom.app ((derivedPullback X.isoSpec.inv).obj K) ≫
      (derivedPullback X'.toSpecΓ).map
        ((affineSpectrumDerivedPullbackIso g').hom.app K) ≫
      (c X'.isoSpec.hom X'.isoSpec.inv ≪≫
      eqToIso (congrArg (fun k : X' ⟶ X' ↦ derivedPullback k) X'.isoSpec.hom_inv_id) ≪≫
      i X').hom.app ((derivedPullback g').obj K) =
    (derivedPullback g').map
      ((c X.isoSpec.hom X.isoSpec.inv ≪≫
      eqToIso (congrArg (fun k : X ⟶ X ↦ derivedPullback k) X.isoSpec.hom_inv_id) ≪≫
      i X).hom.app K) := by
  classical
  rename_i d hX hX'
  dsimp only
  let c : ∀ {P Q Z : Scheme.{u}} (k : P ⟶ Q) (l : Q ⟶ Z),
      derivedPullback l ⋙ derivedPullback k ≅ derivedPullback (k ≫ l) :=
    @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec (@exists_derivedPullbackComposition.{u, w} d))))
  let i : ∀ Y : Scheme.{u}, derivedPullback (𝟙 Y) ≅ 𝟭 _ :=
    Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec (Classical.choose_spec
        (@exists_derivedPullbackComposition.{u, w} d))))).2
  have hi := Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec (@exists_derivedPullbackComposition.{u, w} d))))).2
  exact concrete_square g' K c i hi.1 hi.2.1 hi.2.2
    (affineSpectrumForwardPullbackIso g') (affineSpectrumDerivedPullbackIso g') rfl rfl

end AlgebraicGeometry
