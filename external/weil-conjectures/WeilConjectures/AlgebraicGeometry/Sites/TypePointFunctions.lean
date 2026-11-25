/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.LocallyConstant.Basic
public import WeilConjectures.AlgebraicGeometry.Sites.PointFunctions

/-!
# Sections of constant étale sheaves of sets over connected schemes

For a set `T`, the presheaf on the small étale site of `X` sending `V` to the set of all
functions `V → T` is a sheaf, into which the constant sheaf `T` embeds. Consequently, over a
connected scheme the global sections of the constant sheaf of sets `T` are `T`.

These are the `Type`-valued versions of
`WeilConjectures.AlgebraicGeometry.Sites.ModulePointFunctions`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (T : Type (u + 1))

/-- The presheaf of sets on the small étale site of `X` sending `V` to the set of functions
`V → T`. -/
def typePointFunctionPresheaf : X.Etaleᵒᵖ ⥤ Type (u + 1) where
  obj V := V.unop.left → T
  map {V W} φ := TypeCat.ofHom fun D y ↦ D (φ.unop.left y)

/-- **Functions on points form an étale sheaf of sets.** -/
theorem isSheaf_typePointFunctionPresheaf :
    Presheaf.IsSheaf X.smallEtaleTopology (X.typePointFunctionPresheaf T) := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro V S hS x hx
  choose W g w hg hgw using exists_of_mem_smallEtaleTopology hS
  have key : ∀ {W' : X.Etale} (g' : W' ⟶ V) (hg' : S g') (w' : W'.left) (v : V.left),
      g'.left w' = v → (x g' hg' : W'.left → T) w' = (x (g v) (hg v) : _ → T) (w v) := by
    intro W' g' hg' w' v hv
    obtain ⟨Z, p₁, p₂, z, hp, hz₁, hz₂⟩ :=
      exists_eq_of_apply_eq g' (g v) w' (w v) (by rw [hv, hgw])
    have h : (x g' hg' : W'.left → T) (p₁.left z) = (x (g v) (hg v) : _ → T) (p₂.left z) :=
      congrFun (hx p₁ p₂ hg' (hg v) hp) z
    rw [← hz₁, ← hz₂]
    exact h
  refine ⟨fun v ↦ (x (g v) (hg v) : _ → T) (w v), fun W' g' hg' ↦ ?_, fun t ht ↦ ?_⟩
  · funext w'
    exact (key g' hg' w' _ rfl).symm
  · funext v
    have h : t ((g v).left (w v)) = (x (g v) (hg v) : _ → T) (w v) :=
      congrFun (ht (g v) (hg v)) (w v)
    rw [← h, hgw]

/-- The étale sheaf `V ↦ (V → T)` of all functions on points. -/
def typePointFunctionSheaf : Sheaf X.smallEtaleTopology (Type (u + 1)) :=
  ⟨X.typePointFunctionPresheaf T, X.isSheaf_typePointFunctionPresheaf T⟩

/-- The map from the constant presheaf `T` to `V ↦ (V → T)`. -/
def typeConstToPointFunctionPresheaf :
    (Functor.const X.Etaleᵒᵖ).obj T ⟶ X.typePointFunctionPresheaf T where
  app V := TypeCat.ofHom fun t _ ↦ t

/-- The map from the constant sheaf `T` to the sheaf of functions on points. -/
noncomputable def typeConstantSheafToPointFunctionSheaf :
    (constantSheaf X.smallEtaleTopology (Type (u + 1))).obj T ⟶ X.typePointFunctionSheaf T :=
  ⟨sheafifyLift _ (X.typeConstToPointFunctionPresheaf T) (X.isSheaf_typePointFunctionPresheaf T)⟩

lemma typeConstantSheafToPointFunctionSheaf_app_toSheafify (V : X.Etale) (t : T) :
    (X.typeConstantSheafToPointFunctionSheaf T).hom.app (op V)
      ((CategoryTheory.toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj T)).app
        (op V) t) = fun _ ↦ t := by
  have h := toSheafify_sheafifyLift X.smallEtaleTopology (X.typeConstToPointFunctionPresheaf T)
    (X.isSheaf_typePointFunctionPresheaf T)
  exact ConcreteCategory.congr_hom (congrArg (fun φ ↦ φ.app (op V)) h) t

/-- On geometric stalks, the map from the constant sheaf to functions on points is injective. -/
lemma injective_sheafFiber_map_typeConstantSheafToPointFunctionSheaf (x : X) :
    Function.Injective ((X.uliftPointSmallEtale x).sheafFiber.map
      (X.typeConstantSheafToPointFunctionSheaf T)) := by
  let Φ := X.uliftPointSmallEtale x
  let V₀ : X.Etale := Etale.mk (𝟙 X)
  have hT : IsTerminal V₀ := MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale _
  let t₀ : Φ.fiber.obj V₀ := (Φ.uniqueFiberObj V₀ hT).default
  have hcomp : (Φ.sheafFiberConstantSheafIso T).inv ≫
      Φ.sheafFiber.map (X.typeConstantSheafToPointFunctionSheaf T) =
      (X.typeConstToPointFunctionPresheaf T).app (op V₀) ≫
        Φ.toPresheafFiber V₀ t₀ (X.typePointFunctionPresheaf T) := by
    have h₁ : (Φ.presheafFiberConstIso T).inv =
        Φ.toPresheafFiber V₀ t₀ ((Functor.const X.Etaleᵒᵖ).obj T) := by
      have h := Φ.toPresheafFiber_presheafFiberConstIso_hom T V₀ t₀
      calc (Φ.presheafFiberConstIso T).inv = 𝟙 _ ≫ (Φ.presheafFiberConstIso T).inv :=
            (Category.id_comp _).symm
        _ = _ := by rw [← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    change ((Φ.presheafFiberConstIso T).inv ≫ Φ.presheafFiber.map
      (CategoryTheory.toSheafify _ _)) ≫ Φ.presheafFiber.map (sheafifyLift _ _ _) = _
    rw [Category.assoc, ← Functor.map_comp, toSheafify_sheafifyLift, h₁,
      Φ.toPresheafFiber_naturality]
    rfl
  have hinj : Function.Injective ((X.typeConstToPointFunctionPresheaf T).app (op V₀) ≫
      Φ.toPresheafFiber V₀ t₀ (X.typePointFunctionPresheaf T)) := by
    intro m m' hm
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hm
    obtain ⟨W, g, w, -, hg⟩ := (Φ.toPresheafFiber_eq_iff' _ _ _ _).1 hm
    exact congrFun hg (w.down.left (IsLocalRing.closedPoint _))
  rw [← hcomp] at hinj
  intro a b hab
  have e (c) : ((Φ.sheafFiberConstantSheafIso T).inv ≫
      Φ.sheafFiber.map (X.typeConstantSheafToPointFunctionSheaf T))
        ((Φ.sheafFiberConstantSheafIso T).hom c) =
      Φ.sheafFiber.map (X.typeConstantSheafToPointFunctionSheaf T) c := by
    rw [ConcreteCategory.comp_apply, Iso.hom_inv_id_apply]
  exact (Φ.sheafFiberConstantSheafIso T).toEquiv.injective
    (hinj ((e a).trans (hab.trans (e b).symm)))

/-- The constant sheaf of sets `T` embeds into the sheaf of functions on points. -/
instance mono_typeConstantSheafToPointFunctionSheaf :
    Mono (X.typeConstantSheafToPointFunctionSheaf T) := by
  have hmono := (isConservativeFamilyOfPoints_ulift_pointSmallEtale X).jointlyReflectMonomorphisms
    (Type (u + 1))
  refine @JointlyReflectMonomorphisms.mono _ _ _ _ _ _ hmono _ _ _ (fun Φ ↦ ?_)
  obtain ⟨-, ⟨x⟩⟩ := Φ
  exact (mono_iff_injective _).2
    (X.injective_sheafFiber_map_typeConstantSheafToPointFunctionSheaf T x)

/-- **Sections of a constant sheaf of sets over a connected étale scheme.** -/
theorem bijective_typeToSheafify_app_of_connectedSpace (V : X.Etale) [ConnectedSpace V.left] :
    Function.Bijective
      ((CategoryTheory.toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj T)).app
        (op V)) := by
  let ψ := (X.typeConstantSheafToPointFunctionSheaf T).hom.app (op V)
  have hψ : Function.Injective ψ := by
    have : Mono ((sheafToPresheaf _ _).map (X.typeConstantSheafToPointFunctionSheaf T)) :=
      Functor.map_mono _ _
    have : Mono ψ := (NatTrans.mono_iff_mono_app _).1 this (op V)
    exact (mono_iff_injective _).1 this
  obtain ⟨x₀⟩ := ‹ConnectedSpace V.left›.toNonempty
  refine ⟨fun m m' h ↦ ?_, fun σ ↦ ?_⟩
  · exact congrFun ((typeConstantSheafToPointFunctionSheaf_app_toSheafify X T V m).symm.trans
      ((congrArg ψ h).trans (typeConstantSheafToPointFunctionSheaf_app_toSheafify X T V m'))) x₀
  let D : V.left → T := ψ σ
  have hloc : IsLocallyConstant D := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    obtain ⟨W, g, w, ⟨m, hm⟩, hgw⟩ := exists_of_mem_smallEtaleTopology
      (Presheaf.imageSieve_mem X.smallEtaleTopology
        (CategoryTheory.toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj T)) σ) x
    have hD (w' : W.left) : D (g.left w') = m := by
      have h₁ := congrArg
        (fun s ↦ (X.typeConstantSheafToPointFunctionSheaf T).hom.app (op W) s w') hm
      have h₂ := NatTrans.naturality_apply
        (X.typeConstantSheafToPointFunctionSheaf T).hom g.op σ
      simp only at h₁
      rw [typeConstantSheafToPointFunctionSheaf_app_toSheafify] at h₁
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
  rw [typeConstantSheafToPointFunctionSheaf_app_toSheafify]
  funext x
  exact hloc.apply_eq_of_preconnectedSpace x₀ x

/-- On a connected scheme the constant sheaf functor for sets is fully faithful: its unit
`T ⟶ Γ(X, T_X)` is a bijection. -/
noncomputable def fullyFaithfulTypeConstantSheaf [ConnectedSpace X] :
    (constantSheaf X.smallEtaleTopology (Type (u + 1))).FullyFaithful :=
  let adj := constantSheafAdj X.smallEtaleTopology (Type (u + 1))
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X)
  have : IsIso adj.unit := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun T ↦ ?_
    rw [isIso_iff_bijective]
    have : ConnectedSpace (Etale.mk (𝟙 X)).left := ‹ConnectedSpace X›
    exact X.bijective_typeToSheafify_app_of_connectedSpace T (Etale.mk (𝟙 X))
  adj.fullyFaithfulLOfIsIsoUnit

instance [ConnectedSpace X] : (constantSheaf X.smallEtaleTopology (Type (u + 1))).Full :=
  (fullyFaithfulTypeConstantSheaf X).full

instance [ConnectedSpace X] : (constantSheaf X.smallEtaleTopology (Type (u + 1))).Faithful :=
  (fullyFaithfulTypeConstantSheaf X).faithful

end AlgebraicGeometry.Scheme
