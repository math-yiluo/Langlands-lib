/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Topology.LocallyConstant.Basic
public import WeilConjectures.AlgebraicGeometry.Sites.PointFunctions

/-!
# The étale sheaf of `Λ`-valued functions on points

For a scheme `X` and a module `M` over a ring `Λ`, the presheaf on the small étale site of `X`
sending an étale `X`-scheme `V` to the `Λ`-module `V → M` of all functions on the underlying set
of `V` is a sheaf. The constant sheaf `M` embeds into it. Consequently the sections of the
constant sheaf over a connected étale `X`-scheme are `M`, and over a scheme all of whose étale
schemes are discrete (the spectrum of a field) the constant sheaf is the sheaf of all functions.

These are the `ModuleCat` versions of `WeilConjectures.AlgebraicGeometry.Sites.PointFunctions`
and `WeilConjectures.AlgebraicGeometry.Sites.ConstantSheafSections`.

## Main statements

- `AlgebraicGeometry.Scheme.mono_moduleConstantSheafToPointFunctionSheaf`: the constant sheaf
  embeds into the sheaf of functions on points.
- `AlgebraicGeometry.Scheme.surjective_toSheafify_app_of_connectedSpace`: over a connected
  étale `X`-scheme every section of the constant sheaf is constant.
- `AlgebraicGeometry.Scheme.isIso_moduleConstantSheafToPointFunctionSheaf`: if every étale
  `X`-scheme is discrete, the constant sheaf is the sheaf of all functions on points.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) {Λ : Type (u + 1)} [CommRing Λ] (M : ModuleCat.{u + 1} Λ)

/-- The presheaf of `Λ`-modules on the small étale site of `X` sending an étale `X`-scheme `V`
to the module of all functions from the underlying set of `V` to `M`. -/
noncomputable def modulePointFunctionPresheaf : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ where
  obj V := ModuleCat.of Λ (V.unop.left → M)
  map {V W} φ := ModuleCat.ofHom
    { toFun D y := D (φ.unop.left y)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }

/-- **`Λ`-valued functions on points form an étale sheaf.** -/
theorem isSheaf_modulePointFunctionPresheaf :
    Presheaf.IsSheaf X.smallEtaleTopology (X.modulePointFunctionPresheaf M) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget (s := CategoryTheory.forget (ModuleCat.{u + 1} Λ)),
    isSheaf_iff_isSheaf_of_type]
  intro V S hS x hx
  choose W g w hg hgw using exists_of_mem_smallEtaleTopology hS
  have key : ∀ {W' : X.Etale} (g' : W' ⟶ V) (hg' : S g') (w' : W'.left) (v : V.left),
      g'.left w' = v → (x g' hg' : W'.left → M) w' = (x (g v) (hg v) : _ → M) (w v) := by
    intro W' g' hg' w' v hv
    obtain ⟨Z, p₁, p₂, z, hp, hz₁, hz₂⟩ :=
      exists_eq_of_apply_eq g' (g v) w' (w v) (by rw [hv, hgw])
    have h : (x g' hg' : W'.left → M) (p₁.left z) = (x (g v) (hg v) : _ → M) (p₂.left z) :=
      congrFun (hx p₁ p₂ hg' (hg v) hp) z
    rw [← hz₁, ← hz₂]
    exact h
  refine ⟨fun v ↦ (x (g v) (hg v) : _ → M) (w v), fun W' g' hg' ↦ ?_, fun t ht ↦ ?_⟩
  · funext w'
    exact (key g' hg' w' _ rfl).symm
  · funext v
    have h : t ((g v).left (w v)) = (x (g v) (hg v) : _ → M) (w v) :=
      congrFun (ht (g v) (hg v)) (w v)
    rw [← h, hgw]

/-- The étale sheaf `V ↦ (V → M)` of all `M`-valued functions on points. -/
noncomputable def modulePointFunctionSheaf : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  ⟨X.modulePointFunctionPresheaf M, X.isSheaf_modulePointFunctionPresheaf M⟩

/-- The map from the constant presheaf `M` to `V ↦ (V → M)`, sending `m` to the constant
function `m`. -/
noncomputable def moduleConstToPointFunctionPresheaf :
    (Functor.const X.Etaleᵒᵖ).obj M ⟶ X.modulePointFunctionPresheaf M where
  app V := ModuleCat.ofHom
    { toFun m _ := m
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }

/-- The map from the constant sheaf `M` to the sheaf of functions on points. -/
noncomputable def moduleConstantSheafToPointFunctionSheaf :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M ⟶
      X.modulePointFunctionSheaf M :=
  ⟨sheafifyLift _ (X.moduleConstToPointFunctionPresheaf M)
    (X.isSheaf_modulePointFunctionPresheaf M)⟩

/-- The constant section `m` of the constant sheaf maps to the constant function `m`. -/
lemma moduleConstantSheafToPointFunctionSheaf_app_toSheafify (V : X.Etale) (m : M) :
    (X.moduleConstantSheafToPointFunctionSheaf M).hom.app (op V)
      ((CategoryTheory.toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)).app
        (op V) m) = fun _ ↦ m := by
  have h := toSheafify_sheafifyLift X.smallEtaleTopology (X.moduleConstToPointFunctionPresheaf M)
    (X.isSheaf_modulePointFunctionPresheaf M)
  exact congrArg (fun φ ↦ (φ.app (op V)).hom m) h

/-- On geometric stalks, the map from the constant sheaf `M` to the sheaf of functions on points
is injective. -/
lemma injective_sheafFiber_map_moduleConstantSheafToPointFunctionSheaf (x : X) :
    Function.Injective ((X.uliftPointSmallEtale x).sheafFiber.map
      (X.moduleConstantSheafToPointFunctionSheaf M)) := by
  let Φ := X.uliftPointSmallEtale x
  let T : X.Etale := Etale.mk (𝟙 X)
  have hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale _
  let t₀ : Φ.fiber.obj T := (Φ.uniqueFiberObj T hT).default
  have hcomp : (Φ.sheafFiberConstantSheafIso M).inv ≫
      Φ.sheafFiber.map (X.moduleConstantSheafToPointFunctionSheaf M) =
      (X.moduleConstToPointFunctionPresheaf M).app (op T) ≫
        Φ.toPresheafFiber T t₀ (X.modulePointFunctionPresheaf M) := by
    have h₁ : (Φ.presheafFiberConstIso M).inv =
        Φ.toPresheafFiber T t₀ ((Functor.const X.Etaleᵒᵖ).obj M) := by
      have h := Φ.toPresheafFiber_presheafFiberConstIso_hom M T t₀
      calc (Φ.presheafFiberConstIso M).inv = 𝟙 _ ≫ (Φ.presheafFiberConstIso M).inv :=
            (Category.id_comp _).symm
        _ = _ := by rw [← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    change ((Φ.presheafFiberConstIso M).inv ≫ Φ.presheafFiber.map
      (CategoryTheory.toSheafify _ _)) ≫ Φ.presheafFiber.map (sheafifyLift _ _ _) = _
    rw [Category.assoc, ← Functor.map_comp, toSheafify_sheafifyLift, h₁,
      Φ.toPresheafFiber_naturality]
    rfl
  have hinj : Function.Injective ((X.moduleConstToPointFunctionPresheaf M).app (op T) ≫
      Φ.toPresheafFiber T t₀ (X.modulePointFunctionPresheaf M)) := by
    intro m m' hm
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hm
    obtain ⟨W, g, w, -, hg⟩ := (Φ.toPresheafFiber_eq_iff' _ _ _ _).1 hm
    exact congrFun hg (w.down.left (IsLocalRing.closedPoint _))
  rw [← hcomp] at hinj
  intro a b hab
  have e (c) : ((Φ.sheafFiberConstantSheafIso M).inv ≫
      Φ.sheafFiber.map (X.moduleConstantSheafToPointFunctionSheaf M))
        ((Φ.sheafFiberConstantSheafIso M).hom c) =
      Φ.sheafFiber.map (X.moduleConstantSheafToPointFunctionSheaf M) c := by
    rw [ConcreteCategory.comp_apply, Iso.hom_inv_id_apply]
  exact (Φ.sheafFiberConstantSheafIso M).toLinearEquiv.injective
    (hinj ((e a).trans (hab.trans (e b).symm)))

/-- The constant sheaf `M` embeds into the sheaf of functions on points. -/
instance mono_moduleConstantSheafToPointFunctionSheaf :
    Mono (X.moduleConstantSheafToPointFunctionSheaf M) := by
  have hmono := (isConservativeFamilyOfPoints_ulift_pointSmallEtale X).jointlyReflectMonomorphisms
    (ModuleCat.{u + 1} Λ)
  refine @JointlyReflectMonomorphisms.mono _ _ _ _ _ _ hmono _ _ _ (fun Φ ↦ ?_)
  obtain ⟨-, ⟨x⟩⟩ := Φ
  exact (ModuleCat.mono_iff_injective _).2
    (X.injective_sheafFiber_map_moduleConstantSheafToPointFunctionSheaf M x)

/-- **Sections of a constant sheaf over a connected étale scheme are constant.** -/
theorem surjective_toSheafify_app_of_connectedSpace (V : X.Etale) [ConnectedSpace V.left] :
    Function.Surjective
      ((CategoryTheory.toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)).app
        (op V)) := by
  let ψ := (X.moduleConstantSheafToPointFunctionSheaf M).hom.app (op V)
  have hψ : Function.Injective ψ := by
    have : Mono ((sheafToPresheaf _ _).map (X.moduleConstantSheafToPointFunctionSheaf M)) :=
      Functor.map_mono _ _
    have : Mono ψ := (NatTrans.mono_iff_mono_app _).1 this (op V)
    exact (ModuleCat.mono_iff_injective _).1 this
  obtain ⟨x₀⟩ := ‹ConnectedSpace V.left›.toNonempty
  intro σ
  let D : V.left → M := ψ σ
  have hloc : IsLocallyConstant D := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    obtain ⟨W, g, w, ⟨m, hm⟩, hgw⟩ := exists_of_mem_smallEtaleTopology
      (Presheaf.imageSieve_mem X.smallEtaleTopology
        (CategoryTheory.toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)) σ) x
    have hD (w' : W.left) : D (g.left w') = m := by
      have h₁ := congrArg
        (fun s ↦ (X.moduleConstantSheafToPointFunctionSheaf M).hom.app (op W) s w') hm
      have h₂ := NatTrans.naturality_apply
        (X.moduleConstantSheafToPointFunctionSheaf M).hom g.op σ
      simp only at h₁
      rw [moduleConstantSheafToPointFunctionSheaf_app_toSheafify] at h₁
      exact (congrFun h₂ w').symm.trans h₁.symm
    have : Etale g.left := by
      have : Etale (g.left ≫ V.hom) := by
        rw [show g.left ≫ V.hom = W.hom from CategoryTheory.Over.w ((Etale.forget X).map g)]
        exact W.prop
      exact Etale.of_comp g.left V.hom
    refine ⟨Set.range g.left, g.left.isOpenMap.isOpen_range, ⟨w, hgw⟩, ?_⟩
    rintro _ ⟨w', rfl⟩
    rw [hD, ← hgw, hD]
  refine ⟨D x₀, hψ ?_⟩
  rw [moduleConstantSheafToPointFunctionSheaf_app_toSheafify]
  funext x
  exact hloc.apply_eq_of_preconnectedSpace x₀ x

/-- Over a nonempty étale scheme, distinct elements of `M` give distinct constant sections. -/
theorem injective_toSheafify_app_of_nonempty (V : X.Etale) [Nonempty V.left] :
    Function.Injective
      ((CategoryTheory.toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)).app
        (op V)) := by
  obtain ⟨x₀⟩ := ‹Nonempty V.left›
  intro m m' h
  have := congrArg ((X.moduleConstantSheafToPointFunctionSheaf M).hom.app (op V)) h
  rw [moduleConstantSheafToPointFunctionSheaf_app_toSheafify,
    moduleConstantSheafToPointFunctionSheaf_app_toSheafify] at this
  exact congrFun this x₀

/-- On a connected scheme the constant sheaf functor for `Λ`-modules is fully faithful. -/
noncomputable def fullyFaithfulModuleConstantSheaf (Λ : Type (u + 1)) [CommRing Λ]
    [ConnectedSpace X] : (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).FullyFaithful :=
  let adj := constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X)
  have : IsIso adj.unit := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun M ↦ ?_
    have : ConnectedSpace (Etale.mk (𝟙 X)).left := ‹ConnectedSpace X›
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨X.injective_toSheafify_app_of_nonempty M (Etale.mk (𝟙 X)),
      X.surjective_toSheafify_app_of_connectedSpace M (Etale.mk (𝟙 X))⟩
  adj.fullyFaithfulLOfIsIsoUnit

instance (Λ : Type (u + 1)) [CommRing Λ] [ConnectedSpace X] :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).Full :=
  (fullyFaithfulModuleConstantSheaf X Λ).full

instance (Λ : Type (u + 1)) [CommRing Λ] [ConnectedSpace X] :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).Faithful :=
  (fullyFaithfulModuleConstantSheaf X Λ).faithful

end AlgebraicGeometry.Scheme
