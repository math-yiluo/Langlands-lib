/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CartesianHigherImageTransitions
public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageClassCompatibility
import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Horizontal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompAssoc

@[expose] public section
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

noncomputable local instance localInst_CartesianHigherImageFiniteRawAssembly_1 (X : Scheme.{u}) :
    HasShift (DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) ℤ :=
  inferInstance

noncomputable local instance localInst_CartesianHigherImageFiniteRawAssembly_2 (X : Scheme.{u}) :
    HasZeroMorphisms (DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :=
  inferInstance

private theorem cartesian_map_eq {X S T T' : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) (g' : T' ⟶ S) (a : T' ⟶ T) (w : g' = a ≫ g)
    (r : pullback f g' ⟶ pullback f g)
    (hr₁ : r ≫ pullback.fst f g = pullback.fst f g')
    (hr₂ : r ≫ pullback.snd f g = pullback.snd f g' ≫ a)
    (P : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    cartesianDerivedImageMap f g g' a w P =
      (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
        (show CommSq r (pullback.snd f g') (pullback.snd f g) a from ⟨hr₂⟩)).app
          ((D+((pullback.fst f g)^*[AddCommGrpCat.{u + 1}])).obj P) ≫
        (R+((pullback.snd f g')_*[AddCommGrpCat.{u + 1}])).map
          ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} r (pullback.fst f g)
            (pullback.fst f g') hr₁.symm).inv.app P) := by
  have hr : cartesianImageProjection f g g' a w = r := by
    apply pullback.hom_ext
    · exact (cartesianImageProjection_fst f g g' a w).trans hr₁.symm
    · exact (cartesianImageProjection_snd f g g' a w).trans hr₂.symm
  subst r
  rfl

-- Horizontal pasting gives the exchange part; associativity identifies its coefficient map.
private theorem cartesian_map_comp {X S T T' T'' : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) (g' : T' ⟶ S) (g'' : T'' ⟶ S)
    (a : T' ⟶ T) (b : T'' ⟶ T') (w : g' = a ≫ g) (w' : g'' = b ≫ g')
    (P : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} b a).hom.app
        (cartesianDerivedImage f g P) ≫
      (D+((b)^*[AddCommGrpCat.{u + 1}])).map
        (cartesianDerivedImageMap f g g' a w P) ≫
      cartesianDerivedImageMap f g' g'' b w' P =
    cartesianDerivedImageMap f g g'' (b ≫ a)
      (by rw [Category.assoc, ← w, ← w']) P := by
  let r := cartesianImageProjection f g g' a w
  let s := cartesianImageProjection f g' g'' b w'
  let sq₁ : CommSq r (pullback.snd f g') (pullback.snd f g) a := ⟨by simp [r]⟩
  let sq₂ : CommSq s (pullback.snd f g'') (pullback.snd f g') b := ⟨by simp [s]⟩
  let sq : CommSq (s ≫ r) (pullback.snd f g'') (pullback.snd f g) (b ≫ a) :=
    ⟨by rw [Category.assoc, sq₁.w, ← Category.assoc, sq₂.w, Category.assoc]⟩
  have hp := NatTrans.congr_app (derivedBaseChangeMapPlus_paste_horiz
    AddCommGrpCat.{u + 1} sq₁ sq₂ sq)
    ((D+((pullback.fst f g)^*[AddCommGrpCat.{u + 1}])).obj P)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj,
    Category.id_comp] at hp
  rw [cartesian_map_eq f g g'' (b ≫ a) _ (s ≫ r)
    (by simp [r, s]) sq.w P]
  dsimp only [cartesianDerivedImageMap]
  have hn := (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq₂).naturality
    ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} r (pullback.fst f g)
      (pullback.fst f g') (cartesianImageProjection_fst f g g' a w).symm).inv.app P)
  have ha := NatTrans.congr_app (upperStarCompDerivedPlus_assoc AddCommGrpCat.{u + 1}
    s r (pullback.fst f g) (s ≫ r) (pullback.fst f g') (pullback.fst f g'')
    rfl (cartesianImageProjection_fst f g g' a w).symm
    (by simp [s, r, Category.assoc])) P
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at ha
  simp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]
  have hi := congrArg Iso.inv (show
      (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} s (pullback.fst f g')
        (pullback.fst f g'') (cartesianImageProjection_fst f g' g'' b w').symm).app P ≪≫
        (D+((s)^*[AddCommGrpCat.{u + 1}])).mapIso
          ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} r (pullback.fst f g)
            (pullback.fst f g') (cartesianImageProjection_fst f g g' a w).symm).app P) =
      (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} (s ≫ r) (pullback.fst f g)
        (pullback.fst f g'') (by simp [s, r])).app P ≪≫
        (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} s r).app
          ((D+((pullback.fst f g)^*[AddCommGrpCat.{u + 1}])).obj P) from Iso.ext ha)
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv] at hi
  rw [hp]
  simp only [Category.assoc]
  rw [← Functor.map_comp, hi, Functor.map_comp]

-- Pull both transitions to the fixed base and use naturality of the composition comparison.
private theorem pulled_cartesian_map_comp {X S T T' T'' B : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) (g' : T' ⟶ S) (g'' : T'' ⟶ S)
    (a : T' ⟶ T) (b : T'' ⟶ T') (w : g' = a ≫ g) (w' : g'' = b ≫ g')
    (l : B ⟶ T) (l' : B ⟶ T') (l'' : B ⟶ T'')
    (hl : l = l' ≫ a) (hl' : l' = l'' ≫ b)
    (P : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} l' a l hl).hom.app _ ≫
        (D+((l')^*[AddCommGrpCat.{u + 1}])).map
          (cartesianDerivedImageMap f g g' a w P)) ≫
      ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} l'' b l' hl').hom.app _ ≫
        (D+((l'')^*[AddCommGrpCat.{u + 1}])).map
          (cartesianDerivedImageMap f g' g'' b w' P)) =
    (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} l'' (b ≫ a) l
      (by rw [hl, hl', Category.assoc])).hom.app _ ≫
      (D+((l'')^*[AddCommGrpCat.{u + 1}])).map
        (cartesianDerivedImageMap f g g'' (b ≫ a)
          (by rw [Category.assoc, ← w, ← w']) P) := by
  have hn := (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} l'' b l' hl').hom.naturality
    (cartesianDerivedImageMap f g g' a w P)
  simp only [Functor.comp_map] at hn
  have ha := NatTrans.congr_app (upperStarCompDerivedPlus_assoc AddCommGrpCat.{u + 1}
    l'' b a l' (b ≫ a) l hl' rfl hl) (cartesianDerivedImage f g P)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at ha
  simp only [Category.assoc]
  rw [reassoc_of% hn, ← reassoc_of% ha]
  rw [← Functor.map_comp, ← Functor.map_comp, cartesian_map_comp]

private theorem pulled_cartesian_map_congr {X S T T' B : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) (g' : T' ⟶ S) (a a' : T' ⟶ T) (ha : a = a')
    (w : g' = a ≫ g) (w' : g' = a' ≫ g)
    (l : B ⟶ T) (l' : B ⟶ T') (hl : l = l' ≫ a) (hl' : l = l' ≫ a')
    (P : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} l' a l hl).hom.app _ ≫
        (D+((l')^*[AddCommGrpCat.{u + 1}])).map
          (cartesianDerivedImageMap f g g' a w P) =
      (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} l' a' l hl').hom.app _ ≫
        (D+((l')^*[AddCommGrpCat.{u + 1}])).map
          (cartesianDerivedImageMap f g g' a' w' P) := by
  subst a'
  rfl

private noncomputable def rawTransition {X S : Scheme.{u}} {I : Type u}
    [SmallCategory I] (D : I ⥤ Over S) (c : Cone D) (f : X ⟶ S)
    (P : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    {i j : I} (a : j ⟶ i) :
    (D+(((c.π.app i).left)^*[AddCommGrpCat.{u + 1}])).obj
        (cartesianDerivedImage f (D.obj i).hom P) ⟶
      (D+(((c.π.app j).left)^*[AddCommGrpCat.{u + 1}])).obj
        (cartesianDerivedImage f (D.obj j).hom P) :=
  (upperStarCompDerivedPlus AddCommGrpCat.{u + 1}
    (c.π.app j).left (D.map a).left (c.π.app i).left
    (congrArg (fun b ↦ b.left) (c.w a)).symm).hom.app _ ≫
    (D+(((c.π.app j).left)^*[AddCommGrpCat.{u + 1}])).map
      (cartesianDerivedImageMap f (D.obj i).hom (D.obj j).hom
        (D.map a).left (Over.w (D.map a)).symm P)

private theorem rawTransition_comp {X S : Scheme.{u}} {I : Type u}
    [SmallCategory I] (D : I ⥤ Over S) (c : Cone D) (f : X ⟶ S)
    (P : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    {i j k : I} (a : j ⟶ i) (b : k ⟶ j) :
    rawTransition (i := i) (j := j) D c f P a ≫
      rawTransition (i := j) (j := k) D c f P b =
      rawTransition (i := i) (j := k) D c f P (b ≫ a) := by
  have h := pulled_cartesian_map_comp f (D.obj i).hom (D.obj j).hom (D.obj k).hom
      (D.map a).left (D.map b).left (Over.w (D.map a)).symm (Over.w (D.map b)).symm
      (c.π.app i).left (c.π.app j).left (c.π.app k).left
      (congrArg (fun x ↦ x.left) (c.w a)).symm
      (congrArg (fun x ↦ x.left) (c.w b)).symm P
  dsimp only [rawTransition]
  refine h.trans ?_
  apply pulled_cartesian_map_congr
  exact (congrArg (fun x ↦ x.left) (D.map_comp b a)).symm

/-- Common-stage assembly for a finite family of raw cartesian classes.

Given the individual eventual-zero witnesses for each member of a finite family,
cofilteredness supplies a common stage. The proof uses the composition law for the
displayed raw transition maps and the finite wide-cospan property of a cofiltered
category. Postcomposition carries each zero to the common stage. This theorem contains
only the assembly step; it does not construct individual witnesses.
-/
theorem exists_cartesianHigherImage_finite_raw_assembly
    {k : Type u} [Field k]
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Over (Spec (.of k)))
    [∀ i, QuasiCompact (D.obj i).hom] [∀ i, QuasiSeparated (D.obj i).hom]
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a).left]
    (c : Cone D)
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (i : I) (J : Type u) [Finite J]
    (V : J → c.pt.left.Etale) [∀ t, IsAffine (V t).left]
    (z : ∀ t, (DerivedCategory.Plus.singleFunctor _ 0).obj
      ((abelianComparisonFree c.pt.left).obj (V t)) ⟶
        ((D+(((c.π.app i).left)^*[AddCommGrpCat.{u + 1}])).obj
          (cartesianDerivedImage f (D.obj i).hom
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))⟦(q : ℤ)⟧)
    (hkill : ∀ t, ∃ (j : I) (a : j ⟶ i),
      z t ≫ (shiftFunctor _ (q : ℤ)).map
        ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1}
          (c.π.app j).left (D.map a).left (c.π.app i).left
          (congrArg (fun b ↦ b.left) (c.w a)).symm).hom.app _ ≫
          (D+(((c.π.app j).left)^*[AddCommGrpCat.{u + 1}])).map
            (cartesianDerivedImageMap f (D.obj i).hom (D.obj j).hom
              (D.map a).left (Over.w (D.map a)).symm
              ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) = 0) :
    ∃ (j : I) (a : j ⟶ i), ∀ t,
      z t ≫ (shiftFunctor _ (q : ℤ)).map
        ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1}
          (c.π.app j).left (D.map a).left (c.π.app i).left
          (congrArg (fun b ↦ b.left) (c.w a)).symm).hom.app _ ≫
          (D+(((c.π.app j).left)^*[AddCommGrpCat.{u + 1}])).map
            (cartesianDerivedImageMap f (D.obj i).hom (D.obj j).hom
              (D.map a).left (Over.w (D.map a)).symm
              ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) = 0 := by
  classical
  choose j a ha using hkill
  obtain ⟨l, b, d, hd⟩ := IsCofiltered.wideCospan a
  refine ⟨l, b, fun t ↦ ?_⟩
  change z t ≫ (shiftFunctor _ (q : ℤ)).map
    (rawTransition (i := i) (j := l) D c f ((DerivedCategory.Plus.singleFunctor _ 0).obj F) b) = 0
  rw [← hd t, ← rawTransition_comp (i := i) (j := j t) (k := l),
    Functor.map_comp, ← Category.assoc]
  have ht : z t ≫ (shiftFunctor _ (q : ℤ)).map
      (rawTransition (i := i) (j := j t) D c f
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F) (a t)) = 0 := ha t
  rw [ht, zero_comp]

end AlgebraicGeometry.Etale
