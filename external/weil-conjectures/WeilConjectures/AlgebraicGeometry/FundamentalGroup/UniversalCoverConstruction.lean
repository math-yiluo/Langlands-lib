/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.PathTransport
public import WeilConjectures.AlgebraicGeometry.Limits.AffineOverLimitProperties
public import WeilConjectures.Mathlib.CategoryTheory.Galois.PointedGaloisSmall
public import WeilConjectures.Mathlib.CategoryTheory.Galois.Prorepresentability
public import Mathlib.CategoryTheory.Endomorphism

/-!
# Construction of the universal profinite étale cover

Let `Y` be a connected scheme and `y : Spec K ⟶ Y` a geometric point, `K` separably closed. The
*universal profinite étale cover* of `Y` at `y` is the limit `Ỹ_y = lim A` over the pointed
Galois objects `(A, a)` of the Galois category `FÉt(Y)` with the fibre functor `F_y`
(SGA 1 V.5, Stacks Project Tag 0BN6; Bhatt–Scholze, *The pro-étale topology for schemes*,
§7.4). We index this limit by a small model of the (essentially small) category of pointed
Galois objects, and construct the limit as a scheme affine over `Y`
(`AlgebraicGeometry.Scheme.hasLimit_of_isAffineHom`). Its base point `ỹ : Spec K ⟶ Ỹ_y` is
given by the points `a`.

For `Y` quasi-compact and quasi-separated we show:

- `Ỹ_y ⟶ Y` is weakly étale and surjective, and `Ỹ_y` is connected;
- every finite étale `Y`-scheme `P` splits over `Ỹ_y`: the `Y`-morphisms `Ỹ_y ⟶ P` are in
  bijection with `F_y(P)` via `f ↦ ỹ ≫ f` (`AlgebraicGeometry.Scheme.UniversalCover.toObj` is
  the inverse). Surjectivity is pro-representability of `F_y`; injectivity uses that a
  morphism from a cofiltered limit of qcqs schemes to a scheme locally of finite presentation
  factors through a stage (Stacks Project Tag 01ZC), and that morphisms out of connected objects
  are determined by the image of one point.

A morphism into `Ỹ_y` is determined by its compositions with all `toObj P x`
(`AlgebraicGeometry.Scheme.UniversalCover.hom_ext`); this is how the transport and
functoriality morphisms are compared.
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.Scheme.UniversalCover

open FiniteEtale

attribute [local instance] FiniteEtale.fiberFunctor

variable {Y : Scheme.{u}} [ConnectedSpace Y] {K : Type u} [Field K] [IsSepClosed K]
  (y : Spec (.of K) ⟶ Y)

/-- Pointed Galois finite étale covers form an essentially small category. -/
instance : EssentiallySmall.{u} (PointedGaloisObject (fiber y)) :=
  have := FiniteEtale.essentiallySmall Y
  essentiallySmall_pointedGaloisObject _

/-- The finite étale `Y`-scheme `Y` itself, as a cover. -/
noncomputable abbrev unitObj : Y.FiniteEtale :=
  ⟨MorphismProperty.Over.mk ⊤ (𝟙 Y) inferInstance, inferInstanceAs (IsFinite (𝟙 Y))⟩

/-- There is a pointed Galois cover. -/
instance : Nonempty (PointedGaloisObject (fiber y)) := by
  obtain ⟨A, -, a, h, -⟩ := exists_hom_from_galois_of_fiber (fiber y) unitObj
    (fiberMk y unitObj y (Category.comp_id y))
  exact ⟨⟨A, a, h⟩⟩

/-- Pointed Galois covers form a cofiltered category. -/
instance : IsCofiltered (PointedGaloisObject (fiber y)) where

/-- The small index category of the universal cover: a small model of the category of pointed
Galois objects of `F_y`. -/
abbrev Index : Type u := SmallModel.{u} (PointedGaloisObject (fiber y))

/-- The equivalence between pointed Galois objects and the index category. -/
noncomputable abbrev indexEquiv : PointedGaloisObject (fiber y) ≌ Index y :=
  equivSmallModel _

/-- The index category is cofiltered. -/
instance : IsCofiltered (Index y) := IsCofiltered.of_equivalence (indexEquiv y)

/-- The pointed Galois finite étale `Y`-schemes `A_j` indexed by `Index y`. -/
noncomputable abbrev obj : Index y ⥤ Y.FiniteEtale :=
  (indexEquiv y).inverse ⋙ PointedGaloisObject.incl _

/-- The point `a_j ∈ F_y(A_j)`. -/
noncomputable abbrev point (j : Index y) : (fiber y).obj ((obj y).obj j) :=
  ((indexEquiv y).inverse.obj j).pt

/-- The covers `A_j` are Galois. -/
instance (j : Index y) : IsGalois ((obj y).obj j) := ((indexEquiv y).inverse.obj j).isGalois

/-- The transition maps preserve the points `a_j`. -/
lemma map_point {j j' : Index y} (f : j ⟶ j') :
    (fiber y).map ((obj y).map f) (point y j) = point y j' :=
  ((indexEquiv y).inverse.map f).comp

/-- The underlying diagram of schemes `j ↦ A_j`. -/
@[simps]
noncomputable def diagram : Index y ⥤ Scheme.{u} where
  obj j := ((obj y).obj j).obj.left
  map f := ((obj y).map f).hom.left
  map_id _ := by rw [CategoryTheory.Functor.map_id]; rfl
  map_comp _ _ := by rw [CategoryTheory.Functor.map_comp]; rfl

/-- The structure morphisms `A_j ⟶ Y`. -/
noncomputable abbrev p (j : Index y) : (diagram y).obj j ⟶ Y := ((obj y).obj j).obj.hom

/-- The transition maps are `Y`-morphisms. -/
lemma map_p {j j' : Index y} (f : j ⟶ j') : (diagram y).map f ≫ p y j' = p y j :=
  hom_left_comp _

/-- The covers `A_j` are finite over `Y`. -/
instance (j : Index y) : IsFinite (p y j) := ((obj y).obj j).property

/-- The covers `A_j` are étale over `Y`. -/
instance (j : Index y) : Etale (p y j) := ((obj y).obj j).obj.prop

/-- The transition maps are affine. -/
instance {j j' : Index y} (f : j ⟶ j') : IsAffineHom ((diagram y).map f) := by
  have : IsAffineHom ((diagram y).map f ≫ p y j') := by rw [map_p]; infer_instance
  exact IsAffineHom.of_comp _ (p y j')

/-- The limit `lim A_j` exists, the `A_j` being affine over `Y`. -/
instance : HasLimit (diagram y) := hasLimit_of_isAffineHom _ (p y) (map_p y)

/-- The **universal profinite étale cover** `Ỹ_y = lim A_j`. -/
noncomputable abbrev cover : Scheme.{u} := limit (diagram y)

/-- A chosen index. -/
noncomputable abbrev j₀ : Index y := (IsCofiltered.nonempty (C := Index y)).some

/-- The projection `Ỹ_y ⟶ Y`. -/
noncomputable def proj : cover y ⟶ Y := limit.π (diagram y) (j₀ y) ≫ p y (j₀ y)

/-- The projections `Ỹ_y ⟶ A_j` lie over `Y`. -/
@[reassoc (attr := simp)]
lemma π_p (j : Index y) : limit.π (diagram y) j ≫ p y j = proj y :=
  have : CategoryTheory.IsConnected (Index y) := IsCofiltered.isConnected _
  constant_of_preserves_morphisms (fun j ↦ limit.π (diagram y) j ≫ p y j)
    (fun j j' f ↦ by
      rw [← limit.w (diagram y) f, Category.assoc, map_p]) j (j₀ y)

/-- The base point `ỹ : Spec K ⟶ Ỹ_y`, given by the points `a_j`. -/
noncomputable def pt : Spec (.of K) ⟶ cover y :=
  limit.lift (diagram y)
    { pt := Spec (.of K)
      π :=
        { app j := (point y j).left
          naturality j j' f := by
            exact (Category.id_comp _).trans
              (congrArg CommaMorphism.left (map_point y f)).symm } }

/-- The base point maps to the points `a_j`. -/
@[reassoc (attr := simp)]
lemma pt_π (j : Index y) : pt y ≫ limit.π (diagram y) j = (point y j).left :=
  limit.lift_π _ _

/-- The base point `ỹ` lies over `y`. -/
@[reassoc (attr := simp)]
lemma pt_proj : pt y ≫ proj y = y := by
  rw [proj, pt_π_assoc]
  exact fiber_left_comp y _

/-- Every point of the fibre of a finite étale `Y`-scheme is the image of the point of some
`A_j`: pro-representability of the fibre functor by the pointed Galois objects. -/
lemma exists_hom_point (P : Y.FiniteEtale) (x : (fiber y).obj P) :
    ∃ (j : Index y) (g : (obj y).obj j ⟶ P), (fiber y).map g (point y j) = x := by
  obtain ⟨A, f, a, h, hfa⟩ := exists_hom_from_galois_of_fiber (fiber y) P x
  let e := (indexEquiv y).unitIso.inv.app ⟨A, a, h⟩
  refine ⟨(indexEquiv y).functor.obj ⟨A, a, h⟩, e.val ≫ f, ?_⟩
  rw [CategoryTheory.Functor.map_comp, FintypeCat.comp_apply]
  exact (congrArg ((fiber y).map f) e.comp).trans hfa

/-- The `Y`-morphism `Ỹ_y ⟶ P` corresponding to a point `x ∈ F_y(P)`: it sends `ỹ` to `x`. -/
noncomputable def toObj (P : Y.FiniteEtale) (x : (fiber y).obj P) : cover y ⟶ P.obj.left :=
  limit.π (diagram y) (exists_hom_point y P x).choose ≫
    (exists_hom_point y P x).choose_spec.choose.hom.left

/-- `toObj P x` is a `Y`-morphism. -/
@[reassoc (attr := simp)]
lemma toObj_hom (P : Y.FiniteEtale) (x : (fiber y).obj P) :
    toObj y P x ≫ P.obj.hom = proj y := by
  rw [toObj, Category.assoc, hom_left_comp]
  exact π_p y _

/-- `toObj P x` sends `ỹ` to `x`. -/
@[reassoc (attr := simp)]
lemma pt_toObj (P : Y.FiniteEtale) (x : (fiber y).obj P) : pt y ≫ toObj y P x = x.left := by
  rw [toObj, pt_π_assoc, ← fiber_map_left, (exists_hom_point y P x).choose_spec.choose_spec]


/-- The structure morphisms `A_j ⟶ Y` as a natural transformation to the constant diagram. -/
noncomputable def pNatTrans : diagram y ⟶ (Functor.const (Index y)).obj Y where
  app := p y
  naturality _ _ f := (map_p y f).trans (Category.comp_id _).symm

/-- `Ỹ_y` is weakly étale over `Y`: it is a cofiltered limit of affine étale `Y`-schemes. -/
instance weaklyEtale_proj : WeaklyEtale (proj y) :=
  weaklyEtale_of_isLimit (diagram y) (limit.isLimit _) (p y) (map_p y) (proj y) (π_p y)

/-- `Ỹ_y` is surjective over `Y`: the `A_j` are nonempty finite étale over the connected `Y`. -/
lemma surjective_proj : Function.Surjective (proj y) :=
  surjective_of_isLimit (diagram y) (limit.isLimit _) (p y) (map_p y) (proj y) (π_p y)
    fun j ↦ (surjective_of_nonempty_fiber y ((obj y).obj j) ⟨point y j⟩).surj

/-- `Ỹ_y` is affine over `Y`: the limit legs are affine and the stages are finite over `Y`. -/
instance isAffineHom_proj : IsAffineHom (proj y) := by
  have : IsAffineHom (limit.π (diagram y) (j₀ y)) :=
    isAffineHom_π_app (diagram y) (limit.cone _) (limit.isLimit _) (j₀ y)
  exact inferInstanceAs (IsAffineHom (limit.π (diagram y) (j₀ y) ≫ p y (j₀ y)))

/-- The projection `Ỹ_y ⟶ Y` is quasi-compact. -/
instance quasiCompact_proj : QuasiCompact (proj y) := inferInstance

section QCQS

variable [CompactSpace Y] [QuasiSeparatedSpace Y]

/-- The covers `A_j` are quasi-compact. -/
instance (j : Index y) : CompactSpace ((diagram y).obj j) :=
  QuasiCompact.compactSpace_of_compactSpace (p y j)

/-- The covers `A_j` are quasi-separated. -/
instance (j : Index y) : QuasiSeparatedSpace ((diagram y).obj j) :=
  quasiSeparatedSpace_of_quasiSeparated (p y j)

/-- `Ỹ_y` is connected: it is a cofiltered limit of the connected qcqs schemes `A_j`. -/
instance connectedSpace_cover : ConnectedSpace (cover y) :=
  have (j : Index y) : ConnectedSpace ((diagram y).obj j) :=
    connectedSpace_of_isConnected ((obj y).obj j)
  connectedSpace_of_isLimit (diagram y) (limit.isLimit _)

/-- A `Y`-morphism from `Ỹ_y` to a finite étale `Y`-scheme factors through some `A_j`
(Stacks Project Tag 01ZC, `Hom_Y(lim A_j, P) = colim Hom_Y(A_j, P)` for `P` locally of finite
presentation). -/
lemma exists_factor (P : Y.FiniteEtale) (f : cover y ⟶ P.obj.left)
    (hf : f ≫ P.obj.hom = proj y) :
    ∃ (j : Index y) (g : (obj y).obj j ⟶ P), limit.π (diagram y) j ≫ g.hom.left = f := by
  have : Etale P.obj.hom := P.obj.prop
  obtain ⟨j, g, hg, hgp⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (diagram y) (pNatTrans y) P.obj.hom (limit.cone _) (limit.isLimit _) f (by
      ext j
      simp [pNatTrans, hf])
  exact ⟨j, ObjectProperty.homMk (MorphismProperty.Over.homMk g hgp), hg⟩

/-- Two `Y`-morphisms from `Ỹ_y` to a finite étale `Y`-scheme agreeing at `ỹ` are equal. -/
lemma eq_of_pt_comp_eq (P : Y.FiniteEtale) {f₁ f₂ : cover y ⟶ P.obj.left}
    (h₁ : f₁ ≫ P.obj.hom = proj y) (h₂ : f₂ ≫ P.obj.hom = proj y) (h : pt y ≫ f₁ = pt y ≫ f₂) :
    f₁ = f₂ := by
  obtain ⟨i₁, g₁, rfl⟩ := exists_factor y P f₁ h₁
  obtain ⟨i₂, g₂, rfl⟩ := exists_factor y P f₂ h₂
  obtain ⟨k, a, b, -⟩ := IsCofilteredOrEmpty.cone_objs i₁ i₂
  have e₁ : limit.π (diagram y) i₁ ≫ g₁.hom.left =
      limit.π (diagram y) k ≫ ((obj y).map a ≫ g₁).hom.left := by
    rw [← limit.w (diagram y) a, Category.assoc]
    rfl
  have e₂ : limit.π (diagram y) i₂ ≫ g₂.hom.left =
      limit.π (diagram y) k ≫ ((obj y).map b ≫ g₂).hom.left := by
    rw [← limit.w (diagram y) b, Category.assoc]
    rfl
  rw [e₁, e₂] at h ⊢
  have : (obj y).map a ≫ g₁ = (obj y).map b ≫ g₂ := by
    refine evaluation_injective_of_isConnected (fiber y) _ P (point y k) (fiber_ext y ?_)
    change (point y k).left ≫ _ = (point y k).left ≫ _
    rw [← pt_π_assoc, ← pt_π_assoc]
    exact h
  rw [this]

/-- `toObj P x` is the unique `Y`-morphism `Ỹ_y ⟶ P` sending `ỹ` to `x`. -/
lemma eq_toObj (P : Y.FiniteEtale) (x : (fiber y).obj P) (f : cover y ⟶ P.obj.left)
    (hf : f ≫ P.obj.hom = proj y) (hx : pt y ≫ f = x.left) : f = toObj y P x :=
  eq_of_pt_comp_eq y P hf (toObj_hom y P x) (by rw [hx, pt_toObj])

/-- The projection to a stage `A_j`, followed by a morphism `A_j ⟶ P`, is `toObj`. -/
lemma π_comp_eq_toObj (j : Index y) {P : Y.FiniteEtale} (g : (obj y).obj j ⟶ P) :
    limit.π (diagram y) j ≫ g.hom.left = toObj y P ((fiber y).map g (point y j)) :=
  eq_toObj y P _ _ (by rw [Category.assoc, hom_left_comp]; exact π_p y j)
    (by rw [pt_π_assoc, fiber_map_left])

/-- The projection to a stage `A_j` is `toObj A_j a_j`. -/
lemma π_eq_toObj (j : Index y) :
    limit.π (diagram y) j = toObj y ((obj y).obj j) (point y j) := by
  refine (Category.comp_id _).symm.trans ((π_comp_eq_toObj y j (𝟙 _)).trans ?_)
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- `toObj` is natural in the finite étale `Y`-scheme. -/
@[reassoc]
lemma toObj_comp {P Q : Y.FiniteEtale} (g : P ⟶ Q) (x : (fiber y).obj P) :
    toObj y P x ≫ g.hom.left = toObj y Q ((fiber y).map g x) :=
  eq_toObj y Q _ _ (by rw [Category.assoc, hom_left_comp, toObj_hom])
    (by rw [pt_toObj_assoc, fiber_map_left])

/-- **Morphisms into `Ỹ_y` are determined by their compositions with all `toObj P x`.** -/
lemma hom_ext {T : Scheme.{u}} {h₁ h₂ : T ⟶ cover y}
    (h : ∀ (P : Y.FiniteEtale) (x : (fiber y).obj P), h₁ ≫ toObj y P x = h₂ ≫ toObj y P x) :
    h₁ = h₂ :=
  limit.hom_ext fun j ↦ by rw [π_eq_toObj]; exact h _ _

/-- **Every finite étale `Y`-scheme splits over `Ỹ_y`**: `f ↦ ỹ ≫ f` is a bijection between
`Hom_Y(Ỹ_y, P)` and `F_y(P)`. -/
theorem bijective_fiber (P : Y.FiniteEtale) :
    Function.Bijective fun f : {f : cover y ⟶ P.obj.left // f ≫ P.obj.hom = proj y} ↦
      fiberMk y P (pt y ≫ f.1) (by rw [Category.assoc, f.2]; exact pt_proj y) :=
  ⟨fun f₁ f₂ h ↦ Subtype.ext (eq_of_pt_comp_eq y P f₁.2 f₂.2 (congrArg CommaMorphism.left h)),
    fun x ↦ ⟨⟨toObj y P x, toObj_hom y P x⟩, fiber_ext y (pt_toObj y P x)⟩⟩


section Transport

variable {y} {z w : Spec (.of K) ⟶ Y}

/-- The transport `Ỹ_y ⟶ Ỹ_z` along a path `τ : F_y ≅ F_z`: its component at `(A, a)` is the
`Y`-morphism `Ỹ_y ⟶ A` corresponding to `τ⁻¹ a`. -/
noncomputable def transportHom (τ : fiber y ≅ fiber z) : cover y ⟶ cover z :=
  limit.lift (diagram z)
    { pt := cover y
      π :=
        { app j := toObj y ((obj z).obj j) (τ.inv.app _ (point z j))
          naturality j j' f := (Category.id_comp _).trans (by
            change _ = toObj y _ _ ≫ ((obj z).map f).hom.left
            rw [toObj_comp, ← map_point z f]
            congr 1
            exact ConcreteCategory.congr_hom (τ.inv.naturality ((obj z).map f)) _) } }

/-- The transport along `τ` followed by the `Y`-morphism corresponding to `x ∈ F_z(P)` is the
`Y`-morphism corresponding to `τ⁻¹ x ∈ F_y(P)`. -/
@[reassoc (attr := simp)]
lemma transportHom_toObj (τ : fiber y ≅ fiber z) (P : Y.FiniteEtale) (x : (fiber z).obj P) :
    transportHom τ ≫ toObj z P x = toObj y P (τ.inv.app P x) := by
  obtain ⟨j, g, rfl⟩ := exists_hom_point z P x
  rw [← π_comp_eq_toObj z j g, ← Category.assoc, transportHom, limit.lift_π]
  change toObj y _ _ ≫ g.hom.left = _
  rw [toObj_comp]
  congr 1
  exact (ConcreteCategory.congr_hom (τ.inv.naturality g) _).symm

/-- The transport is a `Y`-morphism. -/
@[reassoc (attr := simp)]
lemma transportHom_proj (τ : fiber y ≅ fiber z) : transportHom τ ≫ proj z = proj y := by
  rw [proj, ← Category.assoc, transportHom, limit.lift_π]
  exact toObj_hom y _ _

omit [ConnectedSpace Y] [CompactSpace Y] [QuasiSeparatedSpace Y] in
/-- `τ⁻¹ (τ x) = x`. -/
lemma inv_app_hom_app (τ : fiber y ≅ fiber z) (P : Y.FiniteEtale) (x : (fiber y).obj P) :
    τ.inv.app P (τ.hom.app P x) = x :=
  ConcreteCategory.congr_hom (τ.hom_inv_id_app P) x

/-- The transport isomorphism `Ỹ_y ≅ Ỹ_z` along a path `τ : F_y ≅ F_z`. -/
@[simps]
noncomputable def transport (τ : fiber y ≅ fiber z) : cover y ≅ cover z where
  hom := transportHom τ
  inv := transportHom τ.symm
  hom_inv_id := hom_ext y fun P x ↦ by
    rw [Category.assoc, transportHom_toObj, transportHom_toObj, Category.id_comp]
    congr 1
    exact inv_app_hom_app τ P x
  inv_hom_id := hom_ext z fun P x ↦ by
    rw [Category.assoc, transportHom_toObj, transportHom_toObj, Category.id_comp]
    congr 1
    exact inv_app_hom_app τ.symm P x

/-- The transport along the trivial path is the identity. -/
lemma transport_refl (y : Spec (.of K) ⟶ Y) : transport (Iso.refl (fiber y)) = Iso.refl _ :=
  Iso.ext (hom_ext y fun P x ↦ by
    rw [transport_hom, transportHom_toObj, Iso.refl_hom, Category.id_comp]
    rfl)

/-- The transport is compatible with composition of paths. -/
lemma transport_trans (τ : fiber y ≅ fiber z) (τ' : fiber z ≅ fiber w) :
    transport (τ ≪≫ τ') = transport τ ≪≫ transport τ' :=
  Iso.ext (hom_ext w fun P x ↦ by
    rw [transport_hom, Iso.trans_hom, transport_hom, transport_hom, Category.assoc,
      transportHom_toObj, transportHom_toObj, transportHom_toObj]
    rfl)

/-- The transport along the reparametrisation path `F_{a ≫ y} ≅ F_y` sends the point over
`a ≫ y` to the reparametrised point `a ≫ ỹ`. -/
lemma pt_transport_reparam (a : Spec (.of K) ≅ Spec (.of K)) (y : Spec (.of K) ⟶ Y) :
    pt (a.hom ≫ y) ≫ (transport (fiberReparamIso a y)).hom = a.hom ≫ pt y :=
  hom_ext y fun P x ↦ by
    rw [Category.assoc, transport_hom, transportHom_toObj, pt_toObj, Category.assoc, pt_toObj,
      fiberReparamIso_inv_app_left]

end Transport

section Map

variable {Y' : Scheme.{u}} [ConnectedSpace Y'] [CompactSpace Y'] [QuasiSeparatedSpace Y']
  (f : Y' ⟶ Y)

/-- The point `(x, y)` of `f^* P` over `y` corresponding to a point `x` of `P` over `y ≫ f`. -/
noncomputable abbrev pullbackPoint (y : Spec (.of K) ⟶ Y') (P : Y.FiniteEtale)
    (x : (fiber (y ≫ f)).obj P) : (fiber y).obj ((FiniteEtale.pullback f).obj P) :=
  (pullbackFiberIso f y).inv.app P x

/-- The projection `f^* P = P ×_{Y,f} Y' ⟶ P`. -/
noncomputable abbrev pullbackFst (P : Y.FiniteEtale) :
    ((FiniteEtale.pullback f).obj P).obj.left ⟶ P.obj.left :=
  Limits.pullback.fst P.obj.hom f

omit [ConnectedSpace Y] [CompactSpace Y] [QuasiSeparatedSpace Y] [ConnectedSpace Y']
  [CompactSpace Y'] [QuasiSeparatedSpace Y'] in
/-- Base change of morphisms is compatible with the projections `f^* P ⟶ P`. -/
@[reassoc]
lemma pullback_map_pullbackFst {P Q : Y.FiniteEtale} (g : P ⟶ Q) :
    ((FiniteEtale.pullback f).map g).hom.left ≫ pullbackFst f Q = pullbackFst f P ≫ g.hom.left :=
  by simp [pullbackFst]

omit [ConnectedSpace Y] [CompactSpace Y] [QuasiSeparatedSpace Y] [ConnectedSpace Y']
  [CompactSpace Y'] [QuasiSeparatedSpace Y'] in
/-- The projection `f^* P ⟶ P` lies over `f`. -/
@[reassoc]
lemma pullbackFst_hom (P : Y.FiniteEtale) :
    pullbackFst f P ≫ P.obj.hom = ((FiniteEtale.pullback f).obj P).obj.hom ≫ f :=
  Limits.pullback.condition

omit [ConnectedSpace Y] [CompactSpace Y] [QuasiSeparatedSpace Y] [ConnectedSpace Y']
  [CompactSpace Y'] [QuasiSeparatedSpace Y'] in
/-- The point `(x, y)` of `f^* P` projects to `x`. -/
@[reassoc (attr := simp)]
lemma pullbackPoint_left_pullbackFst (y : Spec (.of K) ⟶ Y') (P : Y.FiniteEtale)
    (x : (fiber (y ≫ f)).obj P) : (pullbackPoint f y P x).left ≫ pullbackFst f P = x.left := by
  rw [pullbackPoint, pullbackFiberIso_inv_app_left]
  exact Limits.pullback.lift_fst _ _ _

omit [ConnectedSpace Y] [CompactSpace Y] [QuasiSeparatedSpace Y] [ConnectedSpace Y']
  [CompactSpace Y'] [QuasiSeparatedSpace Y'] in
/-- The points `(x, y)` are natural in `P`. -/
lemma pullbackPoint_naturality (y : Spec (.of K) ⟶ Y') {P Q : Y.FiniteEtale} (g : P ⟶ Q)
    (x : (fiber (y ≫ f)).obj P) :
    (fiber y).map ((FiniteEtale.pullback f).map g) (pullbackPoint f y P x) =
      pullbackPoint f y Q ((fiber (y ≫ f)).map g x) :=
  (ConcreteCategory.congr_hom ((pullbackFiberIso f y).inv.naturality g) x).symm

/-- The morphism `Ỹ_y ⟶ Ỹ_{y ≫ f}` over a morphism `f : Y' ⟶ Y`: its component at
`(A, a)` is the `Y'`-morphism `Ỹ_y ⟶ f^* A` corresponding to `(a, y)`, followed by
`f^* A ⟶ A`. -/
noncomputable def map (y : Spec (.of K) ⟶ Y') : cover y ⟶ cover (y ≫ f) :=
  limit.lift (diagram (y ≫ f))
    { pt := cover y
      π :=
        { app j := toObj y _ (pullbackPoint f y _ (point (y ≫ f) j)) ≫ pullbackFst f _
          naturality j j' g := (Category.id_comp _).trans (by
            change _ = (toObj y _ _ ≫ pullbackFst f _) ≫ ((obj (y ≫ f)).map g).hom.left
            rw [Category.assoc, ← pullback_map_pullbackFst, toObj_comp_assoc,
              pullbackPoint_naturality, map_point]) } }

/-- `map f y` followed by the `Y`-morphism corresponding to `x ∈ F_{y ≫ f}(P)` is the
`Y'`-morphism `Ỹ_y ⟶ f^* P` corresponding to `(x, y)`, followed by `f^* P ⟶ P`. -/
@[reassoc (attr := simp)]
lemma map_toObj (y : Spec (.of K) ⟶ Y') (P : Y.FiniteEtale) (x : (fiber (y ≫ f)).obj P) :
    map f y ≫ toObj (y ≫ f) P x = toObj y _ (pullbackPoint f y P x) ≫ pullbackFst f P := by
  obtain ⟨j, g, rfl⟩ := exists_hom_point (y ≫ f) P x
  rw [← π_comp_eq_toObj (y ≫ f) j g, ← Category.assoc, map, limit.lift_π]
  change (toObj y _ _ ≫ pullbackFst f _) ≫ g.hom.left = _
  rw [Category.assoc, ← pullback_map_pullbackFst, toObj_comp_assoc, pullbackPoint_naturality]

omit [CompactSpace Y] [QuasiSeparatedSpace Y] in
/-- `map f y` lies over `f`. -/
lemma map_proj (y : Spec (.of K) ⟶ Y') : map f y ≫ proj (y ≫ f) = proj y ≫ f := by
  rw [proj, ← Category.assoc, map, limit.lift_π]
  change (toObj y _ _ ≫ pullbackFst f _) ≫ p (y ≫ f) _ = _
  rw [Category.assoc, pullbackFst_hom, toObj_hom_assoc]

/-- `map f y` sends `ỹ` to the base point over `y ≫ f`. -/
lemma pt_map (y : Spec (.of K) ⟶ Y') : pt y ≫ map f y = pt (y ≫ f) :=
  hom_ext (y ≫ f) fun P x ↦ by
    rw [Category.assoc, map_toObj, pt_toObj_assoc, pullbackPoint_left_pullbackFst, pt_toObj]

/-- `map f` is compatible with the transports along `τ` and along the induced path. -/
lemma map_transport {y z : Spec (.of K) ⟶ Y'} (τ : fiber y ≅ fiber z) :
    map f y ≫ (transport (pullbackPathIso f τ)).hom = (transport τ).hom ≫ map f z :=
  hom_ext (z ≫ f) fun P x ↦ by
    rw [Category.assoc, transport_hom, transportHom_toObj, map_toObj, Category.assoc,
      transport_hom, map_toObj, transportHom_toObj_assoc]
    congr 2
    simp only [pullbackPathIso, pullbackPoint, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
      Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, FintypeCat.comp_apply]
    exact ConcreteCategory.congr_hom ((pullbackFiberIso f y).hom_inv_id_app P) _
end Map


section Graph

omit [CompactSpace Y] [QuasiSeparatedSpace Y] in
/-- A compatible family of points `c_j ∈ F_y(A_j)` is the family of images of the points `a_j`
under an endomorphism of the fibre functor (pro-representability of `F_y`). -/
lemma exists_end_of_compatible (c : ∀ j, (fiber y).obj ((obj y).obj j))
    (hc : ∀ {j j'} (f : j ⟶ j'), (fiber y).map ((obj y).map f) (c j) = c j') :
    ∃ η : fiber y ⟶ fiber y, ∀ j, η.app _ (point y j) = c j := by
  let e := indexEquiv y
  let s : (PointedGaloisObject.incl (fiber y) ⋙ fiber y ⋙ FintypeCat.incl).sections :=
    ⟨fun A ↦ (fiber y).map (e.unitIso.inv.app A).val (c (e.functor.obj A)), fun {A B} φ ↦ by
      change (fiber y).map φ.val ((fiber y).map (e.unitIso.inv.app A).val _) =
        (fiber y).map (e.unitIso.inv.app B).val _
      rw [← hc (e.functor.map φ)]
      have h := congrArg PointedGaloisObject.Hom.val (e.unitIso.inv.naturality φ)
      exact congrArg (fun g ↦ (fiber y).map g (c (e.functor.obj A))) h.symm⟩
  refine ⟨(homEquivSectionsFibers (fiber y) (fiber y)).symm s, fun j ↦ ?_⟩
  refine (homEquivSectionsFibers_symm_app _ _ s (e.inverse.obj j)).trans ?_
  change (fiber y).map (e.unitInv.app (e.inverse.obj j)).val _ = _
  rw [Equivalence.unitInv_app_inverse]
  exact hc _

include y in
omit [CompactSpace Y] [QuasiSeparatedSpace Y] in
/-- **Graph decomposition** of a Galois cover `A`: the morphism
`∐_{σ ∈ Aut A} A ⟶ A ×_Y A`, `(σ, z) ↦ (σ z, z)`, is an isomorphism
(`AlgebraicGeometry.Scheme.FiniteEtale.isIso_sigmaDesc_of_existsUnique`). -/
lemma isIso_graphDesc (P : Y.FiniteEtale) [IsGalois P] :
    IsIso (Sigma.desc fun m : ULift.{u + 1} (Aut P) ↦
      Limits.pullback.lift (f := P.obj.hom) (g := P.obj.hom)
        m.down.asIso.hom.hom.left (𝟙 P.obj.left)
        (by rw [Category.id_comp]; exact hom_left_comp m.down.asIso.hom)) := by
  have : Finite (ULift.{u + 1} (Aut P)) := Finite.of_equiv _ Equiv.ulift.symm
  refine isIso_sigmaDesc_of_existsUnique (M := ULift.{u + 1} (Aut P)) y P
    (fun m ↦ m.down.asIso.hom) fun a b ↦ ?_
  obtain ⟨σ, hσ, hu⟩ := (evaluation_aut_bijective_of_isGalois (fiber y) P a).existsUnique b
  exact ⟨⟨σ⟩, hσ, fun m hm ↦ ULift.ext (hu m.down hm)⟩

include y in
omit [CompactSpace Y] [QuasiSeparatedSpace Y] in
/-- Every point of `A ×_Y A`, for a Galois cover `A`, is of the form `(σ z, z)`. -/
lemma exists_aut_of_mem_pullback (P : Y.FiniteEtale) [IsGalois P]
    (q : (Limits.pullback P.obj.hom P.obj.hom : Scheme.{u})) :
    ∃ (σ : Aut P) (z : P.obj.left), (Limits.pullback.lift (f := P.obj.hom) (g := P.obj.hom)
      σ.asIso.hom.hom.left (𝟙 P.obj.left)
        (by rw [Category.id_comp]; exact hom_left_comp σ.asIso.hom)).base z = q := by
  have := isIso_graphDesc y P
  set Φ := Sigma.desc fun m : ULift.{u + 1} (Aut P) ↦
      Limits.pullback.lift (f := P.obj.hom) (g := P.obj.hom)
        m.down.asIso.hom.hom.left (𝟙 P.obj.left)
        (by rw [Category.id_comp]; exact hom_left_comp m.down.asIso.hom)
  obtain ⟨m, z, hz⟩ := (sigmaOpenCover fun _ : ULift.{u + 1} (Aut P) ↦ P.obj.left).exists_eq
    ((inv Φ).base q)
  refine ⟨m.down, z, ?_⟩
  rw [sigmaOpenCover_f] at hz
  rw [← Sigma.ι_comp_desc (fun m : ULift.{u + 1} (Aut P) ↦ Limits.pullback.lift (f := P.obj.hom)
    (g := P.obj.hom) m.down.asIso.hom.hom.left (𝟙 P.obj.left)
      (by rw [Category.id_comp]; exact hom_left_comp m.down.asIso.hom)) m, Scheme.Hom.comp_apply]
  erw [hz]
  rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
  rfl

include y in
omit [CompactSpace Y] [QuasiSeparatedSpace Y] in
/-- The automorphism `σ` in `(σ z, z)` is determined by the point. -/
lemma aut_eq_of_pullback_lift_eq (P : Y.FiniteEtale) [IsGalois P] (σ σ' : Aut P)
    (z z' : P.obj.left)
    (h : (Limits.pullback.lift (f := P.obj.hom) (g := P.obj.hom) σ.asIso.hom.hom.left (𝟙 P.obj.left)
      (by rw [Category.id_comp]; exact hom_left_comp σ.asIso.hom)).base z =
      (Limits.pullback.lift (f := P.obj.hom) (g := P.obj.hom) σ'.asIso.hom.hom.left (𝟙 P.obj.left)
        (by rw [Category.id_comp]; exact hom_left_comp σ'.asIso.hom)).base z') : σ = σ' := by
  have := isIso_graphDesc y P
  set Φ := Sigma.desc fun m : ULift.{u + 1} (Aut P) ↦
      Limits.pullback.lift (f := P.obj.hom) (g := P.obj.hom)
        m.down.asIso.hom.hom.left (𝟙 P.obj.left)
        (by rw [Category.id_comp]; exact hom_left_comp m.down.asIso.hom)
  have e (τ : Aut P) (w : P.obj.left) : (Limits.pullback.lift (f := P.obj.hom) (g := P.obj.hom)
      τ.asIso.hom.hom.left (𝟙 P.obj.left)
        (by rw [Category.id_comp]; exact hom_left_comp τ.asIso.hom)).base w =
      Φ.base ((Sigma.ι (fun _ : ULift.{u + 1} (Aut P) ↦ P.obj.left) ⟨τ⟩).base w) := by
    rw [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]
  rw [e, e] at h
  have h' := (sigmaι_eq_iff _ _ _ _ _).mp (((ConcreteCategory.bijective_of_isIso Φ.base).1) h)
  exact congrArg ULift.down (Sigma.mk.inj_iff.mp h').1

/-- **Every point of `Ỹ_y ×_Y Ỹ_y` lies on the graph of the transport along a loop**: for every
point `q` there are `g ∈ π₁(Y, y) = Aut F_y` and `x ∈ Ỹ_y` with `q = (x, g x)`. Indeed
`Ỹ_y ×_Y Ỹ_y = lim A_j ×_Y A_j` and `A_j ×_Y A_j = ∐_{σ ∈ Aut A_j} A_j` for Galois `A_j`; the
components containing the images of `q` form a compatible family, i.e. an element of
`lim Aut A_j = π₁(Y, y)`. -/
theorem exists_graph (q : (Limits.pullback (proj y) (proj y) : Scheme.{u})) :
    ∃ (g : Aut (fiber y)) (x : cover y),
      (Limits.pullback.lift (f := proj y) (g := proj y) (𝟙 _) (transport (g).asIso).hom
        (by rw [Category.id_comp, transport_hom, transportHom_proj])).base x = q := by
  have hc := isLimitPairCone (diagram y) (limit.isLimit _) (p y) (map_p y) (proj y) (π_p y)
  let c := pairCone (diagram y) (p y) (map_p y) (proj y) (π_p y)
  have hfst (j : Index y) : c.π.app j ≫ Limits.pullback.fst _ _ =
      Limits.pullback.fst _ _ ≫ limit.π (diagram y) j := Limits.pullback.lift_fst _ _ _
  have hsnd (j : Index y) : c.π.app j ≫ Limits.pullback.snd _ _ =
      Limits.pullback.snd _ _ ≫ limit.π (diagram y) j := Limits.pullback.lift_snd _ _ _
  let gr (j : Index y) (σ : Aut ((obj y).obj j)) :
      (diagram y).obj j ⟶ Limits.pullback (p y j) (p y j) :=
    Limits.pullback.lift (f := p y j) (g := p y j) σ.asIso.hom.hom.left (𝟙 _)
      (by rw [Category.id_comp]; exact hom_left_comp σ.asIso.hom)
  choose σ z hσz₀ using fun j ↦ exists_aut_of_mem_pullback y ((obj y).obj j) ((c.π.app j).base q)
  have hσz (j : Index y) : (gr j (σ j)).base (z j) = (c.π.app j).base q := hσz₀ j
  have hσ {j j' : Index y} (f : j ⟶ j') :
      (obj y).map f ≫ (σ j').asIso.hom = (σ j).asIso.hom ≫ (obj y).map f := by
    let φ := (obj y).map f
    have hgr : gr j (σ j) ≫ (pairDiagram (diagram y) (p y) (map_p y)).map f =
        φ.hom.left ≫ gr j' (autMap φ (σ j)) := by
      refine Limits.pullback.hom_ext ?_ ?_
      · simp only [gr, Category.assoc, Limits.pullback.lift_fst, Limits.pullback.lift_fst_assoc]
        exact (congrArg (fun ψ ↦ ψ.hom.left) (comp_autMap φ (σ j))).symm
      · simp only [gr, Category.assoc, Limits.pullback.lift_snd,
          Limits.pullback.lift_snd_assoc]
        exact (Category.id_comp _).trans (Category.comp_id _).symm
    have : σ j' = autMap φ (σ j) := by
      refine aut_eq_of_pullback_lift_eq y _ _ _ (z j') (φ.hom.left.base (z j)) ?_
      change (gr j' (σ j')).base (z j') = (gr j' (autMap φ (σ j))).base (φ.hom.left.base (z j))
      have e1 := congrArg (fun h ↦ h.base (z j)) hgr
      have e2 := congrArg (fun h ↦ h.base q) (c.w f)
      simp only [Scheme.Hom.comp_apply] at e1 e2
      rw [hσz j']
      exact e2.symm.trans ((congrArg _ (hσz j)).symm.trans e1)
    rw [this]
    exact comp_autMap φ (σ j)
  have hσ' {j j' : Index y} (f : j ⟶ j') :
      (σ j).asIso.inv ≫ (obj y).map f = (obj y).map f ≫ (σ j').asIso.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hσ f, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  obtain ⟨η, hη⟩ := exists_end_of_compatible y (fun j ↦ (fiber y).map (σ j).asIso.inv (point y j))
    fun {j j'} f ↦ by
      rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp, hσ' f,
        CategoryTheory.Functor.map_comp, ConcreteCategory.comp_apply, map_point]
  have : IsIso η := isIso_of_fiberFunctor (fiber y) (fiber y) η
  let g : Aut (fiber y) := Aut.of (asIso η).symm
  have hinvhom (j : Index y) : (σ j).asIso.inv.hom.left ≫ (σ j).asIso.hom.hom.left = 𝟙 _ :=
    congrArg (fun ψ ↦ ψ.hom.left) (σ j).asIso.inv_hom_id
  have hhominv (j : Index y) : (σ j).asIso.hom.hom.left ≫ (σ j).asIso.inv.hom.left = 𝟙 _ :=
    congrArg (fun ψ ↦ ψ.hom.left) (σ j).asIso.hom_inv_id
  refine ⟨g, (Limits.pullback.fst (proj y) (proj y)).base q, ext_of_isLimit _ hc fun j ↦ ?_⟩
  have key : Limits.pullback.lift (f := proj y) (g := proj y) (𝟙 _) (transport g.asIso).hom
      (by rw [Category.id_comp, transport_hom, transportHom_proj]) ≫ c.π.app j =
      limit.π (diagram y) j ≫ (σ j).asIso.inv.hom.left ≫ gr j (σ j) := by
    refine Limits.pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hfst, Limits.pullback.lift_fst_assoc, Category.id_comp]
      simp only [gr, Category.assoc, Limits.pullback.lift_fst]
      rw [hinvhom j]
      exact (Category.comp_id _).symm
    · rw [Category.assoc, hsnd, Limits.pullback.lift_snd_assoc]
      simp only [gr, Category.assoc, Limits.pullback.lift_snd]
      have h2 := π_comp_eq_toObj y j (σ j).asIso.inv
      rw [← hη j] at h2
      refine Eq.trans ?_ ((h2.symm.trans (Category.comp_id _).symm).trans (Category.assoc _ _ _))
      rw [π_eq_toObj y j, transport_hom, transportHom_toObj]
      rfl
  have h1 : (limit.π (diagram y) j).base ((Limits.pullback.fst (proj y) (proj y)).base q) =
      (σ j).asIso.hom.hom.left.base (z j) := by
    have e := congrArg (fun h ↦ h.base q) (hfst j)
    simp only [Scheme.Hom.comp_apply] at e
    refine e.symm.trans
      ((congrArg (Limits.pullback.fst (p y j) (p y j)).base (hσz j)).symm.trans ?_)
    rw [← Scheme.Hom.comp_apply]
    simp only [gr, Limits.pullback.lift_fst]
    rfl
  have e := congrArg (fun h ↦ h.base ((Limits.pullback.fst (proj y) (proj y)).base q)) key
  simp only [Scheme.Hom.comp_apply] at e
  refine e.trans ((congrArg (gr j (σ j)).base ?_).trans (hσz j))
  rw [h1]
  have e3 := congrArg (fun h ↦ h.base (z j)) (hhominv j)
  simp only [Scheme.Hom.comp_apply] at e3
  exact e3

/-- **The point `(ỹ, g ỹ)` of `Ỹ_y ×_Y Ỹ_y` depends continuously on `g ∈ π₁(Y, y)`**: its image
in `A_j ×_Y A_j` only depends on `g⁻¹ a_j`, which is locally constant in `g`, and the preimages
of opens of the `A_j ×_Y A_j` form a basis of the topology of `Ỹ_y ×_Y Ỹ_y`. -/
theorem continuous_graph (x : Spec (.of K)) :
    Continuous fun g : Aut (fiber y) ↦ (Limits.pullback.lift (f := proj y) (g := proj y) (pt y)
      (pt y ≫ (transport (g).asIso).hom)
      (by rw [Category.assoc, transport_hom, transportHom_proj])).base x := by
  have hc := isLimitPairCone (diagram y) (limit.isLimit _) (p y) (map_p y) (proj y) (π_p y)
  refine (isBasis_preimage_isAffineOpen _ _ hc).continuous_iff.mpr ?_
  rintro _ ⟨_, ⟨j, V, -, rfl⟩, rfl⟩
  let R (c : (fiber y).obj ((obj y).obj j)) : (Limits.pullback (p y j) (p y j) : Scheme.{u}) :=
    (Limits.pullback.lift (point y j).left c.left
      ((fiber_left_comp y _).trans (fiber_left_comp y c).symm)).base x
  have key (g : Aut (fiber y)) : Limits.pullback.lift (f := proj y) (g := proj y) (pt y)
      (pt y ≫ (transport g.asIso).hom) (by rw [Category.assoc, transport_hom, transportHom_proj]) ≫
        (pairCone (diagram y) (p y) (map_p y) (proj y) (π_p y)).π.app j =
      Limits.pullback.lift (point y j).left (g.asIso.inv.app _ (point y j)).left
        ((fiber_left_comp y _).trans (fiber_left_comp y _).symm) := by
    refine Limits.pullback.hom_ext ?_ ?_
    · rw [Category.assoc, Limits.pullback.lift_fst]
      refine (Limits.pullback.lift_fst_assoc _ _ _ _).trans ?_
      exact (pt_π y j).trans (Limits.pullback.lift_fst _ _ _).symm
    · rw [Category.assoc, Limits.pullback.lift_snd]
      refine (Limits.pullback.lift_snd_assoc _ _ _ _).trans ?_
      change pt y ≫ (transport g.asIso).hom ≫ limit.π (diagram y) j = _
      rw [π_eq_toObj, transport_hom, transportHom_toObj, pt_toObj]
      exact (Limits.pullback.lift_snd _ _ _).symm
  have hcont : Continuous fun g : Aut (fiber y) ↦ g.asIso.inv.app ((obj y).obj j) (point y j) :=
    Continuous.congr ((continuous_of_discreteTopology
      (f := fun σ : Aut ((fiber y).obj ((obj y).obj j)) ↦
      σ.asIso.inv (point y j))).comp ((continuous_apply ((obj y).obj j)).comp
      (continuous_induced_dom (f := autEmbedding (fiber y))))) fun _ ↦ rfl
  convert (isOpen_discrete {c | R c ∈ V}).preimage hcont using 1
  ext g
  change _ ∈ V ↔ R _ ∈ V
  simp only [R]
  rw [← key g]
  exact Iff.rfl

omit [CompactSpace Y] [QuasiSeparatedSpace Y] in
/-- Two endomorphisms of the fibre functor agreeing at the points `a_j` agree. -/
lemma natTrans_ext_point {η η' : fiber y ⟶ fiber y}
    (h : ∀ j, η.app ((obj y).obj j) (point y j) = η'.app ((obj y).obj j) (point y j)) :
    η = η' := by
  ext P x
  obtain ⟨j, φ, rfl⟩ := exists_hom_point y P x
  have e₁ := ConcreteCategory.congr_hom (η.naturality φ) (point y j)
  have e₂ := ConcreteCategory.congr_hom (η'.naturality φ) (point y j)
  simp only [FintypeCat.comp_apply] at e₁ e₂
  rw [e₁, e₂, h j]

omit [CompactSpace Y] [QuasiSeparatedSpace Y] in
/-- The automorphism of the Galois cover `A_j` through which a loop `g` acts on the point `a_j`:
the unique `σ` with `σ⁻¹ a_j = g⁻¹ a_j`. -/
lemma existsUnique_autAt (j : Index y) (g : Aut (fiber y)) :
    ∃! σ : Aut ((obj y).obj j),
      (fiber y).map σ.asIso.inv (point y j) = g.asIso.inv.app ((obj y).obj j) (point y j) := by
  obtain ⟨τ, hτ, hu⟩ := (evaluation_aut_bijective_of_isGalois (fiber y) ((obj y).obj j)
    (point y j)).existsUnique (g.asIso.inv.app ((obj y).obj j) (point y j))
  refine ⟨τ⁻¹, hτ, fun σ hσ ↦ ?_⟩
  simpa only [inv_inv] using congrArg Inv.inv (hu σ⁻¹ hσ)

/-- The automorphism of `A_j` through which a loop acts on the point `a_j`. -/
noncomputable def autAt (j : Index y) (g : Aut (fiber y)) : Aut ((obj y).obj j) :=
  (existsUnique_autAt y j g).exists.choose

omit [CompactSpace Y] [QuasiSeparatedSpace Y] in
/-- The defining property of `autAt`. -/
lemma autAt_spec (j : Index y) (g : Aut (fiber y)) :
    (fiber y).map (autAt y j g).asIso.inv (point y j) =
      g.asIso.inv.app ((obj y).obj j) (point y j) :=
  (existsUnique_autAt y j g).exists.choose_spec

omit [CompactSpace Y] [QuasiSeparatedSpace Y] in
/-- A loop acts on the point `a_j` through `autAt`. -/
lemma hom_app_point (j : Index y) (g : Aut (fiber y)) :
    g.asIso.hom.app ((obj y).obj j) (point y j) =
      (fiber y).map (autAt y j g).asIso.hom (point y j) := by
  have e := ConcreteCategory.congr_hom (g.asIso.inv.naturality (autAt y j g).asIso.hom) (point y j)
  simp only [FintypeCat.comp_apply] at e
  rw [← autAt_spec] at e
  have e₁ := ConcreteCategory.congr_hom
    ((fiber y).mapIso ((autAt y j g)).asIso).inv_hom_id (point y j)
  simp only [Functor.mapIso_inv, Functor.mapIso_hom, FintypeCat.comp_apply,
    FintypeCat.id_apply] at e₁
  rw [e₁] at e
  calc g.asIso.hom.app ((obj y).obj j) (point y j)
      = g.asIso.hom.app _
          (g.asIso.inv.app _ ((fiber y).map (autAt y j g).asIso.hom (point y j))) := by rw [e]
    _ = _ := inv_app_hom_app g.asIso.symm _ _

/-- The graph `x ↦ (x, g x)` of the transport along a loop. -/
noncomputable abbrev loopGraph (g : Aut (fiber y)) :
    cover y ⟶ Limits.pullback (proj y) (proj y) :=
  Limits.pullback.lift (f := proj y) (g := proj y) (𝟙 _) (transport (g).asIso).hom
    (by rw [Category.id_comp, transport_hom, transportHom_proj])

/-- The graph of the transport along a loop `g` at the stage `A_j`: the graph of `autAt j g`. -/
lemma loopGraph_comp_pairCone (g : Aut (fiber y)) (j : Index y) :
    loopGraph y g ≫ (pairCone (diagram y) (p y) (map_p y) (proj y) (π_p y)).π.app j =
      limit.π (diagram y) j ≫ (autAt y j g).asIso.inv.hom.left ≫
        Limits.pullback.lift (f := p y j) (g := p y j) (autAt y j g).asIso.hom.hom.left (𝟙 _)
          (by rw [Category.id_comp]; exact hom_left_comp (autAt y j g).asIso.hom) := by
  have hinvhom : (autAt y j g).asIso.inv.hom.left ≫ (autAt y j g).asIso.hom.hom.left = 𝟙 _ :=
    congrArg (fun ψ ↦ ψ.hom.left) (autAt y j g).asIso.inv_hom_id
  refine Limits.pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, Limits.pullback.lift_fst,
      Limits.pullback.lift_fst_assoc, Category.id_comp]
    rw [hinvhom]
    exact (Category.comp_id _).symm
  · simp only [Category.assoc, Limits.pullback.lift_snd,
      Limits.pullback.lift_snd_assoc, Category.comp_id]
    have h2 := π_comp_eq_toObj y j (autAt y j g).asIso.inv
    rw [autAt_spec] at h2
    rw [h2]
    change (transport g.asIso).hom ≫ limit.π (diagram y) j = _
    rw [π_eq_toObj y j, transport_hom, transportHom_toObj]

/-- **The loop of a point of `Ỹ_y ×_Y Ỹ_y` is unique**: the graphs of the transports along
distinct loops are disjoint. -/
lemma eq_of_loopGraph_eq {g g' : Aut (fiber y)} {x x' : cover y}
    (h : (loopGraph y g).base x = (loopGraph y g').base x') : g = g' := by
  have hj (j : Index y) : autAt y j g = autAt y j g' := by
    have e : (loopGraph y g ≫ (pairCone (diagram y) (p y) (map_p y) (proj y) (π_p y)).π.app j).base
        x = (loopGraph y g' ≫ (pairCone (diagram y) (p y) (map_p y) (proj y) (π_p y)).π.app j).base
          x' := by
      simp only [Scheme.Hom.comp_apply, h]
    rw [loopGraph_comp_pairCone, loopGraph_comp_pairCone] at e
    simp only [Scheme.Hom.comp_apply] at e
    exact aut_eq_of_pullback_lift_eq y _ _ _ _ _ e
  have hinv : g.asIso.inv = g'.asIso.inv := natTrans_ext_point y fun j ↦ by
    rw [← autAt_spec, ← autAt_spec, hj j]
  exact Aut.ext (Iso.ext (by rw [← Iso.inv_eq_inv]; exact hinv))

/-- The loop `g ∈ π₁(Y, y)` of a point `q = (x, g x)` of `Ỹ_y ×_Y Ỹ_y`. -/
noncomputable def loop (q : (Limits.pullback (proj y) (proj y) : Scheme.{u})) : Aut (fiber y) :=
  (exists_graph y q).choose

/-- The loop of `(x, g x)` is `g`. -/
lemma loop_loopGraph (g : Aut (fiber y)) (x : cover y) : loop y ((loopGraph y g).base x) = g :=
  eq_of_loopGraph_eq y (exists_graph y ((loopGraph y g).base x)).choose_spec.choose_spec

/-- The automorphism of `A_j ×_Y A_j = ∐_{σ ∈ Aut A_j} A_j` indexing the summand of a point. -/
noncomputable def pairIndex (j : Index y)
    (w : (Limits.pullback (p y j) (p y j) : Scheme.{u})) : Aut ((obj y).obj j) :=
  (exists_aut_of_mem_pullback y ((obj y).obj j) w).choose

omit [CompactSpace Y] [QuasiSeparatedSpace Y] in
/-- The summand index is locally constant. -/
lemma isLocallyConstant_pairIndex (j : Index y) : IsLocallyConstant (pairIndex y j) := by
  let gr (σ : Aut ((obj y).obj j)) : (diagram y).obj j ⟶ Limits.pullback (p y j) (p y j) :=
    Limits.pullback.lift (f := p y j) (g := p y j) σ.asIso.hom.hom.left (𝟙 _)
      (by rw [Category.id_comp]; exact hom_left_comp σ.asIso.hom)
  have : IsIso (Sigma.desc fun m : ULift.{u + 1} (Aut ((obj y).obj j)) ↦ gr m.down) :=
    isIso_graphDesc y ((obj y).obj j)
  have hgr (σ : Aut ((obj y).obj j)) : IsOpenImmersion (gr σ) := by
    rw [← Sigma.ι_comp_desc (fun m : ULift.{u + 1} (Aut ((obj y).obj j)) ↦ gr m.down) ⟨σ⟩]
    infer_instance
  have h (σ : Aut ((obj y).obj j)) : pairIndex y j ⁻¹' {σ} = Set.range (gr σ).base := by
    ext w
    constructor
    · intro hw
      have := (exists_aut_of_mem_pullback y ((obj y).obj j) w).choose_spec.choose_spec
      rw [Set.mem_preimage, Set.mem_singleton_iff] at hw
      refine ⟨(exists_aut_of_mem_pullback y ((obj y).obj j) w).choose_spec.choose, ?_⟩
      rw [← hw]
      exact this
    · rintro ⟨z, rfl⟩
      exact aut_eq_of_pullback_lift_eq y _ _ _ _ _
        (exists_aut_of_mem_pullback y ((obj y).obj j) ((gr σ).base z)).choose_spec.choose_spec
  intro s
  rw [← Set.biUnion_preimage_singleton]
  exact isOpen_biUnion fun σ _ ↦ h σ ▸ (gr σ).isOpenEmbedding.isOpen_range

/-- The automorphism of `A_j` of the loop of a point is the summand index of its image in
`A_j ×_Y A_j`. -/
lemma autAt_loop (j : Index y) (q : (Limits.pullback (proj y) (proj y) : Scheme.{u})) :
    autAt y j (loop y q) = pairIndex y j
      (((pairCone (diagram y) (p y) (map_p y) (proj y) (π_p y)).π.app j).base q) := by
  obtain ⟨x, hx⟩ := (exists_graph y q).choose_spec
  have e := congrArg (fun h ↦ h.base x) (loopGraph_comp_pairCone y (loop y q) j)
  simp only [Scheme.Hom.comp_apply] at e
  change (loopGraph y (loop y q)).base x = q at hx
  rw [hx] at e
  have hw := (exists_aut_of_mem_pullback y ((obj y).obj j)
    (((pairCone (diagram y) (p y) (map_p y) (proj y) (π_p y)).π.app j).base q)).choose_spec
  replace hw := hw.choose_spec
  exact aut_eq_of_pullback_lift_eq y _ _ _ _ _ (e.symm.trans hw.symm)

/-- **The loop of a point of `Ỹ_y ×_Y Ỹ_y` depends continuously on the point.** -/
theorem continuous_loop : Continuous (loop y) := by
  refine continuous_induced_rng.2 (continuous_pi fun P ↦ ?_)
  refine IsLocallyConstant.continuous ?_
  have hx (x : (fiber y).obj P) : IsLocallyConstant fun q ↦ (loop y q).asIso.hom.app P x := by
    obtain ⟨j, φ, rfl⟩ := exists_hom_point y P x
    have h (q : (Limits.pullback (proj y) (proj y) : Scheme.{u})) :
        (loop y q).asIso.hom.app P ((fiber y).map φ (point y j)) = (fiber y).map φ ((fiber y).map
          (pairIndex y j (((pairCone (diagram y) (p y) (map_p y) (proj y)
            (π_p y)).π.app j).base q)).asIso.hom (point y j)) := by
      have e := ConcreteCategory.congr_hom ((loop y q).asIso.hom.naturality φ) (point y j)
      simp only [FintypeCat.comp_apply] at e
      rw [e, hom_app_point, autAt_loop]
    simp only [h]
    exact (((isLocallyConstant_pairIndex y j).comp_continuous
      (((pairCone (diagram y) (p y) (map_p y) (proj y) (π_p y)).π.app j).base.hom.continuous)).comp
        fun σ ↦ (fiber y).map φ ((fiber y).map σ.asIso.hom (point y j)))
  rw [IsLocallyConstant.iff_eventually_eq]
  intro q₀
  filter_upwards [Filter.eventually_all.2 fun x ↦ (IsLocallyConstant.iff_eventually_eq _).1
    (hx x) q₀] with q hq
  change Aut.of ((loop y q).asIso.app P) = Aut.of ((loop y q₀).asIso.app P)
  exact Aut.ext (Iso.ext (ConcreteCategory.hom_ext _ _ hq))

end Graph

end QCQS

end AlgebraicGeometry.Scheme.UniversalCover
