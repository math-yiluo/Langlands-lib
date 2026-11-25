/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Horizontal

/-! # Canonical comparison maps for a base-change cube

Source: Stacks Project, Tags 03Q9 and 095T, restriction of section complexes.
(blueprint: lem-weil-pbc-abelian-exchange-cube-comparisons).
-/

@[expose] public section
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
open Scheme

/-- Apply homology and the inverse-image stalk comparison to a derived morphism.
The equality specifies the point at which its source stalk is taken.
Source: Stacks Project, Tag 03Q1.
(blueprint: lem-weil-pbc-abelian-exchange-cube-comparisons). -/
noncomputable def derivedStalkComparison
    {Y Z : Scheme.{u}} (a : Z ⟶ Y)
    {k : Type u} [Field k] [IsSepClosed k]
    (t : Spec (.of k) ⟶ Z) (s : Spec (.of k) ⟶ Y) (h : t ≫ a = s)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (L : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (m : (D+((a)^*[AddCommGrpCat.{u + 1}])).obj K ⟶ L) (q : ℤ) :
    (pointSmallEtale s).sheafFiber.obj ((DerivedCategory.Plus.homologyFunctor _ q).obj K) ⟶
      (pointSmallEtale t).sheafFiber.obj ((DerivedCategory.Plus.homologyFunctor _ q).obj L) := by
  subst s
  exact (upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} a t).inv.app _ ≫
    (pointSmallEtale t).sheafFiber.map
      ((Functor.mapDerivedCategoryPlusHomologyFunctorIso
        ((a)^*[AddCommGrpCat.{u + 1}]) q).hom.app K ≫
        (DerivedCategory.Plus.homologyFunctor _ q).map m)

variable {S T X X' S₀ T₀ X₀ X₁ : Scheme.{u}}
  {g : T ⟶ S} {f : X ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ T}
  {jA : S₀ ⟶ S} {jB : T₀ ⟶ T} {g₀ : T₀ ⟶ S₀}
  {p₀ : X₀ ⟶ X} {f₀ : X₀ ⟶ S₀} {p₁ : X₁ ⟶ X₀} {f₁ : X₁ ⟶ T₀}
  {b : X₁ ⟶ X'}

/-- Restrict the source of exchange: commute the two inverse images, use the
base-change map for f, and identify the pulled-back single complex.
Source: Stacks Project, Tag 03Q9, restriction complexes.
(blueprint: lem-weil-pbc-abelian-exchange-cube-comparisons). -/
noncomputable def exchangeCubeSourceComparison
    (sq₀ : CommSq p₀ f₀ f jA) (h : jB ≫ g = g₀ ≫ jA)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    let K := (DerivedCategory.Plus.singleFunctor _ 0).obj G
    let K₀ := (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((p₀)^*[AddCommGrpCat.{u + 1}]).obj G)
    (D+((jB)^*[AddCommGrpCat.{u + 1}])).obj
      ((R+((f)_*[AddCommGrpCat.{u + 1}]) ⋙ D+((g)^*[AddCommGrpCat.{u + 1}])).obj K) ⟶
    (R+((f₀)_*[AddCommGrpCat.{u + 1}]) ⋙ D+((g₀)^*[AddCommGrpCat.{u + 1}])).obj K₀ :=
  (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} jB g).inv.app _ ≫
    eqToHom (congrArg (fun a ↦ (D+((a)^*[AddCommGrpCat.{u + 1}])).obj
      ((R+((f)_*[AddCommGrpCat.{u + 1}])).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj G))) h) ≫
    (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} g₀ jA).hom.app _ ≫
    (D+((g₀)^*[AddCommGrpCat.{u + 1}])).map
      ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq₀).app _ ≫
        (R+((f₀)_*[AddCommGrpCat.{u + 1}])).map
          ((Functor.mapDerivedCategoryPlusSingleFunctor
            ((p₀)^*[AddCommGrpCat.{u + 1}]) 0).hom.app G))

/-- Restrict the target of exchange: use the base-change map for f', then commute
inverse images and identify the pulled-back single complex.
Source: Stacks Project, Tag 03Q9, restriction complexes.
(blueprint: lem-weil-pbc-abelian-exchange-cube-comparisons). -/
noncomputable def exchangeCubeTargetComparison
    (sqB : CommSq b f₁ f' jB) (hb : b ≫ g' = p₁ ≫ p₀)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    let K := (DerivedCategory.Plus.singleFunctor _ 0).obj G
    let K₀ := (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((p₀)^*[AddCommGrpCat.{u + 1}]).obj G)
    (D+((jB)^*[AddCommGrpCat.{u + 1}])).obj
      ((D+((g')^*[AddCommGrpCat.{u + 1}]) ⋙ R+((f')_*[AddCommGrpCat.{u + 1}])).obj K) ⟶
    (D+((p₁)^*[AddCommGrpCat.{u + 1}]) ⋙ R+((f₁)_*[AddCommGrpCat.{u + 1}])).obj K₀ :=
  (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sqB).app _ ≫
    (R+((f₁)_*[AddCommGrpCat.{u + 1}])).map
      ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} b g').inv.app _ ≫
        eqToHom (congrArg (fun a ↦ (D+((a)^*[AddCommGrpCat.{u + 1}])).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj G)) hb) ≫
        (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} p₁ p₀).hom.app _ ≫
        (D+((p₁)^*[AddCommGrpCat.{u + 1}])).map
          ((Functor.mapDerivedCategoryPlusSingleFunctor
            ((p₀)^*[AddCommGrpCat.{u + 1}]) 0).hom.app G))

private theorem derivedExchange_transport
    {S T X Y : Scheme.{u}} {f : X ⟶ S} {f' : Y ⟶ T}
    {a a' : T ⟶ S} {b b' : Y ⟶ X}
    (sq : CommSq b f' f a) (sq' : CommSq b' f' f a')
    (ha : a = a') (hb : b = b')
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    eqToHom (congrArg (fun c ↦ (D+((c)^*[AddCommGrpCat.{u + 1}])).obj
        ((R+((f)_*[AddCommGrpCat.{u + 1}])).obj K)) ha) ≫
      (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq').app K =
    (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq).app K ≫
      (R+((f')_*[AddCommGrpCat.{u + 1}])).map
        (eqToHom (congrArg (fun c ↦ (D+((c)^*[AddCommGrpCat.{u + 1}])).obj K) hb)) := by
  subst a' b'
  simp

/-- The two factorizations of the outer derived mate agree after the
inverse-image composition identifications of the commuting cube.

Proof: form the horizontal composite of `sq` and `sqB`, and the horizontal
composite of `sq₀` and `sq₁`. Apply `derivedBaseChangeMapPlus_paste_horiz` to
each composite at `K`. The outer horizontal maps are identified by `h` and
`hb`, so transport one outer square along these equalities; its commutativity
proof agrees with the other by proof irrelevance. Naturality of the
inverse-image composition isomorphisms transports the resulting mate.
Precompose by the inverse of the composition isomorphism for `jB,g`, and
postcompose by the direct-image of the composition isomorphism for `p₁,p₀`.
Cancel each adjacent hom/inv pair using the isomorphism identities and
functoriality. The displayed equality is the remaining composite. This
argument concerns arbitrary complexes and commuting squares, so it needs
no properness, cartesianness, degree, or stalk assumptions; it also applies
to zero complexes and identity cubes.

Source: Stacks Project, Tags 03Q9 and 095T; the first proof step of
`lem-weil-pbc-abelian-exchange-cube-comparisons`, before single-complex naturality.
(blueprint: lem-weil-pbc-abelian-exchange-cube-comparisons). -/
private theorem derivedExchangeCube_pasting
    (sq : CommSq g' f' f g) (sq₀ : CommSq p₀ f₀ f jA)
    (sq₁ : CommSq p₁ f₁ f₀ g₀) (sqB : CommSq b f₁ f' jB)
    (h : jB ≫ g = g₀ ≫ jA) (hb : b ≫ g' = p₁ ≫ p₀)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (D+((jB)^*[AddCommGrpCat.{u + 1}])).map
        ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq).app K) ≫
      (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sqB).app
        ((D+((g')^*[AddCommGrpCat.{u + 1}])).obj K) ≫
      (R+((f₁)_*[AddCommGrpCat.{u + 1}])).map
        ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} b g').inv.app K ≫
          eqToHom (congrArg (fun a ↦ (D+((a)^*[AddCommGrpCat.{u + 1}])).obj K) hb) ≫
          (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} p₁ p₀).hom.app K) =
    (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} jB g).inv.app _ ≫
      eqToHom (congrArg (fun a ↦ (D+((a)^*[AddCommGrpCat.{u + 1}])).obj
        ((R+((f)_*[AddCommGrpCat.{u + 1}])).obj K)) h) ≫
      (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} g₀ jA).hom.app _ ≫
      (D+((g₀)^*[AddCommGrpCat.{u + 1}])).map
        ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq₀).app K) ≫
      (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq₁).app
        ((D+((p₀)^*[AddCommGrpCat.{u + 1}])).obj K) := by
  let outerA : CommSq (b ≫ g') f₁ f (jB ≫ g) := ⟨by
    rw [Category.assoc, sq.w, ← Category.assoc, sqB.w, Category.assoc]⟩
  let outerB : CommSq (p₁ ≫ p₀) f₁ f (g₀ ≫ jA) := ⟨by
    rw [Category.assoc, sq₀.w, ← Category.assoc, sq₁.w, Category.assoc]⟩
  have hpA := NatTrans.congr_app
    (derivedBaseChangeMapPlus_paste_horiz AddCommGrpCat.{u + 1} sq sqB outerA) K
  have hpB := NatTrans.congr_app
    (derivedBaseChangeMapPlus_paste_horiz AddCommGrpCat.{u + 1} sq₀ sq₁ outerB) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj,
    Category.id_comp] at hpA hpB
  have ht := derivedExchange_transport outerA outerB h hb K
  rw [hpA, hpB] at ht
  have hw := congrArg (fun m ↦
    (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} jB g).inv.app
        ((R+((f)_*[AddCommGrpCat.{u + 1}])).obj K) ≫ m ≫
      (R+((f₁)_*[AddCommGrpCat.{u + 1}])).map
        ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} p₁ p₀).hom.app K)) ht
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp, Iso.inv_hom_id_app] at hw
  erw [(R+((f₁)_*[AddCommGrpCat.{u + 1}])).map_id] at hw
  simpa only [Category.comp_id] using hw.symm


/-- Naturality of the stalk comparison in its target morphism.
Source: Stacks Project, Tag 095T, formal functoriality of homology and fibres.
(blueprint: lem-weil-pbc-abelian-exchange-cube-comparisons). -/
private theorem derivedStalkComparison_postcomp
    {Y Z : Scheme.{u}} (a : Z ⟶ Y)
    {k : Type u} [Field k] [IsSepClosed k]
    (t : Spec (.of k) ⟶ Z) (s : Spec (.of k) ⟶ Y) (h : t ≫ a = s)
    (A : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (B C : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (u : (D+((a)^*[AddCommGrpCat.{u + 1}])).obj A ⟶ B) (v : B ⟶ C) (q : ℤ) :
    derivedStalkComparison a t s h A C (u ≫ v) q =
      derivedStalkComparison a t s h A B u q ≫
        (pointSmallEtale t).sheafFiber.map
          ((DerivedCategory.Plus.homologyFunctor _ q).map v) := by
  subst s
  simp [derivedStalkComparison, Functor.map_comp, Category.assoc]

/-- Naturality of the stalk comparison in its source morphism.
Source: Stacks Project, Tag 095T, formal functoriality of inverse image.
(blueprint: lem-weil-pbc-abelian-exchange-cube-comparisons). -/
private theorem derivedStalkComparison_precomp
    {Y Z : Scheme.{u}} (a : Z ⟶ Y)
    {k : Type u} [Field k] [IsSepClosed k]
    (t : Spec (.of k) ⟶ Z) (s : Spec (.of k) ⟶ Y) (h : t ≫ a = s)
    (A B : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (C : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (w : A ⟶ B) (v : (D+((a)^*[AddCommGrpCat.{u + 1}])).obj B ⟶ C) (q : ℤ) :
    (pointSmallEtale s).sheafFiber.map
          ((DerivedCategory.Plus.homologyFunctor _ q).map w) ≫
        derivedStalkComparison a t s h B C v q =
      derivedStalkComparison a t s h A C
        (((D+((a)^*[AddCommGrpCat.{u + 1}])).map w) ≫ v) q := by
  subst s
  simp only [derivedStalkComparison, Functor.map_comp]
  rw [← Category.assoc]
  rw [(upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} a t).inv.naturality
    ((DerivedCategory.Plus.homologyFunctor _ q).map w)]
  simp only [Category.assoc]
  change _ ≫ (pointSmallEtale t).sheafFiber.map
      (((a)^*[AddCommGrpCat.{u + 1}]).map
        ((DerivedCategory.Plus.homologyFunctor _ q).map w)) ≫ _ ≫ _ = _
  rw [← Functor.map_comp_assoc]
  have hn := (Functor.mapDerivedCategoryPlusHomologyFunctorIso
    ((a)^*[AddCommGrpCat.{u + 1}]) q).hom.naturality w
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [hn]
  simp [Functor.map_comp, Category.assoc]

/-- Insert the single-complex comparison by naturality of the local mate. -/
private theorem exchangeCube_derived_square
    (sq : CommSq g' f' f g) (sq₀ : CommSq p₀ f₀ f jA)
    (sq₁ : CommSq p₁ f₁ f₀ g₀) (sqB : CommSq b f₁ f' jB)
    (h : jB ≫ g = g₀ ≫ jA) (hb : b ≫ g' = p₁ ≫ p₀)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    let K := (DerivedCategory.Plus.singleFunctor _ 0).obj G
    let K₀ := (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((p₀)^*[AddCommGrpCat.{u + 1}]).obj G)
    (D+((jB)^*[AddCommGrpCat.{u + 1}])).map
        ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq).app K) ≫
      exchangeCubeTargetComparison sqB hb G =
      exchangeCubeSourceComparison sq₀ h G ≫
        (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq₁).app K₀ := by
  dsimp only
  have hp := derivedExchangeCube_pasting sq sq₀ sq₁ sqB h hb
    ((DerivedCategory.Plus.singleFunctor _ 0).obj G)
  have hn := (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq₁).naturality
    ((Functor.mapDerivedCategoryPlusSingleFunctor
      ((p₀)^*[AddCommGrpCat.{u + 1}]) 0).hom.app G)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  simp only [exchangeCubeSourceComparison, exchangeCubeTargetComparison,
    Functor.map_comp, Category.assoc]
  simp only [Functor.map_comp] at hp
  rw [hn]
  exact (reassoc_of% hp) _

/-- The exchange square commutes after restriction along a commuting cube and on
homology stalks. This is a compatibility assertion only, with no invertibility claim.
Source: Stacks Project, Tags 03Q9 and 095T; formal mate-pasting calculation.
(blueprint: lem-weil-pbc-abelian-exchange-cube-comparisons).

Proof: paste the original square with the square over jB, and paste the square over
jA with the local square over g₀. The resulting outer squares have equal horizontal
maps by h and hb. The horizontal pasting law for the derived base-change map gives
the same outer mate from each factorization. Cancel the inverse-image composition
isomorphisms to get the square between the two comparison morphisms above. Naturality
of the inverse-image/single-complex isomorphism inserts the identification of K₀.
Apply H^q, then the point fibre functor. Naturality of the exact inverse-image/homology
isomorphism and of the inverse-image stalk isomorphism identifies the source with the
stalk at s and gives the displayed square. No cartesianness, properness, torsion, or
strict locality is required; the argument also applies to q = 0 and zero sheaves. -/
theorem exchangeCube_stalk_square
    (sq : CommSq g' f' f g) (sq₀ : CommSq p₀ f₀ f jA)
    (sq₁ : CommSq p₁ f₁ f₀ g₀) (sqB : CommSq b f₁ f' jB)
    (h : jB ≫ g = g₀ ≫ jA) (hb : b ≫ g' = p₁ ≫ p₀)
    {k : Type u} [Field k] [IsSepClosed k]
    (t : Spec (.of k) ⟶ T₀) (s : Spec (.of k) ⟶ T) (ht : t ≫ jB = s)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ) :
    let K := (DerivedCategory.Plus.singleFunctor _ 0).obj G
    let K₀ := (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((p₀)^*[AddCommGrpCat.{u + 1}]).obj G)
    let M₁ := (R+((f)_*[AddCommGrpCat.{u + 1}]) ⋙
      D+((g)^*[AddCommGrpCat.{u + 1}])).obj K
    let M₂ := (D+((g')^*[AddCommGrpCat.{u + 1}]) ⋙
      R+((f')_*[AddCommGrpCat.{u + 1}])).obj K
    let N₁ := (R+((f₀)_*[AddCommGrpCat.{u + 1}]) ⋙
      D+((g₀)^*[AddCommGrpCat.{u + 1}])).obj K₀
    let N₂ := (D+((p₁)^*[AddCommGrpCat.{u + 1}]) ⋙
      R+((f₁)_*[AddCommGrpCat.{u + 1}])).obj K₀
    let H := DerivedCategory.Plus.homologyFunctor _ q
    derivedStalkComparison jB t s ht M₁ N₁ (exchangeCubeSourceComparison sq₀ h G) q ≫
        (pointSmallEtale t).sheafFiber.map
          (H.map ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq₁).app K₀)) =
      (pointSmallEtale s).sheafFiber.map
          ((DerivedCategory.Plus.homologyFunctor _ q).map
            ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq).app K)) ≫
        derivedStalkComparison jB t s ht M₂ N₂
          (exchangeCubeTargetComparison sqB hb G) q := by
  dsimp only
  rw [← derivedStalkComparison_postcomp, derivedStalkComparison_precomp]
  rw [exchangeCube_derived_square sq sq₀ sq₁ sqB h hb G]

end AlgebraicGeometry.Etale
