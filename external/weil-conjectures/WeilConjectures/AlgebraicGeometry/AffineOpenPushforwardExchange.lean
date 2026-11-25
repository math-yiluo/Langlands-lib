/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.AffinePushforwardBaseChangeIsIso
import Mathlib.AlgebraicGeometry.Modules.Tilde

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry

private noncomputable abbrev adj {Y Z : Scheme.{u}} (k : Y ⟶ Z) :=
  Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def square {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (p : X' ⟶ X)
    (h : p ≫ f = f' ≫ g) :
    Scheme.Modules.pushforward p ⋙ Scheme.Modules.pushforward f ⟶
      Scheme.Modules.pushforward f' ⋙ Scheme.Modules.pushforward g :=
  (Scheme.Modules.pushforwardComp p f).hom ≫ (Scheme.Modules.pushforwardCongr h).hom ≫
    (Scheme.Modules.pushforwardComp f' g).inv

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem exchange_unit {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (p : X' ⟶ X)
    (h : p ≫ f = f' ≫ g) (F : X.Modules) :
    (adj g).unit.app ((Scheme.Modules.pushforward f).obj F) ≫
        (Scheme.Modules.pushforward g).map (Scheme.Modules.moduleBaseChangeMap f f' g p h F) =
      (Scheme.Modules.pushforward f).map ((adj p).unit.app F) ≫
        (square f f' g p h).app ((Scheme.Modules.tensorPullback p).obj F) := by
  have ht := ((adj g).homEquiv _ _).apply_symm_apply
    ((Scheme.Modules.pushforward f).map ((adj p).unit.app F) ≫
      (square f f' g p h).app ((Scheme.Modules.tensorPullback p).obj F))
  simpa only [Adjunction.homEquiv_unit, Scheme.Modules.moduleBaseChangeMap, square,
    NatTrans.comp_app, adj, Category.assoc, Functor.id_obj, Functor.comp_obj] using ht

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem exchange_vertical
    {W X S W' X' S' : Scheme.{u}}
    (j : W ⟶ X) (f : X ⟶ S) (j' : W' ⟶ X') (f' : X' ⟶ S')
    (q : W' ⟶ W) (p : X' ⟶ X) (g : S' ⟶ S)
    (hj : q ≫ j = j' ≫ p) (hf : p ≫ f = f' ≫ g)
    (h : q ≫ (j ≫ f) = (j' ≫ f') ≫ g) (F : W.Modules) :
    (Scheme.Modules.tensorPullback g).map ((Scheme.Modules.pushforwardComp j f).hom.app F) ≫
        Scheme.Modules.moduleBaseChangeMap (j ≫ f) (j' ≫ f') g q h F =
      Scheme.Modules.moduleBaseChangeMap f f' g p hf ((Scheme.Modules.pushforward j).obj F) ≫
        (Scheme.Modules.pushforward f').map (Scheme.Modules.moduleBaseChangeMap j j' p q hj F) ≫
        (Scheme.Modules.pushforwardComp j' f').hom.app
          ((Scheme.Modules.tensorPullback q).obj F) := by
  -- Transpose both composites, then use the two defining unit equations.
  apply ((adj g).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  change (Scheme.Modules.pushforwardComp j f).hom.app F ≫
      (adj g).unit.app _ ≫ (Scheme.Modules.pushforward g).map _ =
    ((adj g).unit.app _ ≫ (Scheme.Modules.pushforward g).map _) ≫
      (Scheme.Modules.pushforward g).map _
  erw [exchange_unit (j ≫ f) (j' ≫ f') g q h F,
    exchange_unit f f' g p hf ((Scheme.Modules.pushforward j).obj F)]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.comp_map (Scheme.Modules.pushforward f') (Scheme.Modules.pushforward g),
    ← (square f f' g p hf).naturality_assoc,
    Functor.comp_map, ← Functor.map_comp_assoc, exchange_unit]
  rw [Functor.map_comp]
  -- Pushforward composition is sectionwise identity; restrictions compose.
  apply Scheme.Modules.hom_ext
  intro U
  simp only [square, NatTrans.comp_app, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforward_map_app,
    Scheme.Modules.pushforwardComp_hom_app_app, Scheme.Modules.pushforwardComp_inv_app_app,
    Scheme.Modules.pushforwardCongr_hom_app_app, Scheme.Modules.pushforward_obj_presheaf_map,
    Category.id_comp, Category.comp_id, Category.assoc]
  ext x
  simp only [ConcreteCategory.comp_apply]
  change ((Scheme.Modules.tensorPullback q).obj F).presheaf.map _
      (((adj q).unit.app F).app (j ⁻¹ᵁ f ⁻¹ᵁ U) x) =
    ((Scheme.Modules.tensorPullback q).obj F).presheaf.map _
      (((Scheme.Modules.tensorPullback q).obj F).presheaf.map _
        (((adj q).unit.app F).app (j ⁻¹ᵁ f ⁻¹ᵁ U) x))
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  congr 2

/-- Ordinary exchange is invertible on a quasi-coherent affine-open direct image.
Source: Stacks Project, Tag 02KG; the affine-intersection argument of
`lem-pc-affine-alternating-cech-pinned-mate`.
(blueprint: lem-pc-s3-affine-open-pushforward-exchange).
Proof: Write j for W.ι and form its pullback j' along p = pullback.fst f g.
Since X is separated over the affine scheme Spec A, X is separated and j is affine.
The composite j ≫ f is affine because both its source and target are affine.
The restriction G|W is quasi-coherent. The square for j and p and the outer square
for j ≫ f and g are cartesian, so affinePushforward_baseChange makes their exchange
maps invertible. Vertical pasting of ordinary exchange, proved by transposing under
the tensor-pullback adjunction for g, expresses the outer map (up to pushforward
composition isomorphisms) as the exchange for f on j_*G|W followed by f'_* of
exchange for j. Pushforward preserves the latter isomorphism. Cancel it and the
composition isomorphisms to obtain the assertion. This uses no derived category,
complex, finite-product identification, or localization. -/
theorem affineOpen_pushforward_exchange
    {A B : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec A)
    [IsSeparated f] (g : Spec B ⟶ Spec A)
    (G : X.Modules) [SheafOfModules.IsQuasicoherent.{u} G]
    (W : X.Opens) (hW : IsAffineOpen W) :
    IsIso (Scheme.Modules.moduleBaseChangeMap f (pullback.snd f g) g
      (pullback.fst f g) pullback.condition
      ((Scheme.Modules.pushforward W.ι).obj (G.restrict W.ι))) := by
  let : IsAffine W := hW
  let : IsAffineHom (W.ι ≫ f) := inferInstance
  let : IsAffineHom W.ι := IsAffineHom.of_comp W.ι f
  let p := pullback.fst f g
  let f' := pullback.snd f g
  let q := pullback.fst W.ι p
  let j' := pullback.snd W.ι p
  have sj : IsPullback q j' W.ι p := IsPullback.of_hasPullback W.ι p
  have sf : IsPullback p f' f g := IsPullback.of_hasPullback f g
  have so := sj.paste_vert sf
  let F := G.restrict W.ι
  have : F.IsQuasicoherent := inferInstance
  have := Scheme.Modules.affinePushforward_baseChange_isIso W.ι j' p q sj F
  have := Scheme.Modules.affinePushforward_baseChange_isIso (W.ι ≫ f) (j' ≫ f') g q so F
  have he := exchange_vertical W.ι f j' f' q p g sj.w sf.w so.w F
  have hi : IsIso ((Scheme.Modules.tensorPullback g).map
      ((Scheme.Modules.pushforwardComp W.ι f).hom.app F) ≫
      Scheme.Modules.moduleBaseChangeMap (W.ι ≫ f) (j' ≫ f') g q so.w F) := inferInstance
  rw [he] at hi
  have := hi
  exact (isIso_comp_right_iff _ _).mp hi

end AlgebraicGeometry
