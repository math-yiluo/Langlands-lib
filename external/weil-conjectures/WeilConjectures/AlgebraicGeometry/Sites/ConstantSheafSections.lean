/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import WeilConjectures.AlgebraicGeometry.Sites.PointFunctions
public import WeilConjectures.AlgebraicGeometry.Sites.StalkwiseCokernel

/-!
# Global sections of a constant étale sheaf

The map from a constant étale sheaf `M` on a scheme `X` to the sheaf `V ↦ (V → M)` of functions
on points is a monomorphism. Consequently the global sections of the constant sheaf `M` on a
connected scheme are `M`: a global section is a function `X → M` which is locally constant, the
images of étale morphisms being open, hence constant.

## Main statements

- `AlgebraicGeometry.Scheme.mono_constantSheafToPointFunctionSheaf`: the constant sheaf embeds
  into the sheaf of functions on points.
- `AlgebraicGeometry.Scheme.bijective_toSheafify_app_terminal`: for `X` connected, the global
  sections of the constant sheaf `M` are `M`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (M : AddCommGrpCat.{u + 1})

/-- On geometric stalks, the map from the constant sheaf `M` to the sheaf of functions on points
is injective: on the stalk `M` of the constant sheaf it is `m ↦` the germ of the constant
function `m`. -/
lemma injective_sheafFiber_map_constantSheafToPointFunctionSheaf (x : X) :
    Function.Injective ((X.uliftPointSmallEtale x).sheafFiber.map
      (X.constantSheafToPointFunctionSheaf M)) := by
  let Φ := X.uliftPointSmallEtale x
  let T : X.Etale := Etale.mk (𝟙 X)
  have hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale _
  let t₀ : Φ.fiber.obj T := (Φ.uniqueFiberObj T hT).default
  have hcomp : (Φ.sheafFiberConstantSheafIso M).inv ≫
      Φ.sheafFiber.map (X.constantSheafToPointFunctionSheaf M) =
      (X.constToPointFunctionPresheaf M).app (op T) ≫
        Φ.toPresheafFiber T t₀ (X.pointFunctionPresheaf M) := by
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
  have hinj : Function.Injective ((X.constToPointFunctionPresheaf M).app (op T) ≫
      Φ.toPresheafFiber T t₀ (X.pointFunctionPresheaf M)) := by
    intro m m' hm
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hm
    obtain ⟨W, g, w, -, hg⟩ := (Φ.toPresheafFiber_eq_iff' _ _ _ _).1 hm
    exact congrFun hg (w.down.left (IsLocalRing.closedPoint _))
  rw [← hcomp] at hinj
  intro a b hab
  have e (c) : ((Φ.sheafFiberConstantSheafIso M).inv ≫
      Φ.sheafFiber.map (X.constantSheafToPointFunctionSheaf M))
        ((Φ.sheafFiberConstantSheafIso M).hom c) =
      Φ.sheafFiber.map (X.constantSheafToPointFunctionSheaf M) c := by
    rw [ConcreteCategory.comp_apply, Iso.hom_inv_id_apply]
  exact (Φ.sheafFiberConstantSheafIso M).addCommGroupIsoToAddEquiv.injective
    (hinj ((e a).trans (hab.trans (e b).symm)))

/-- The constant étale sheaf `M` embeds into the sheaf `V ↦ (V → M)` of functions on points. -/
instance mono_constantSheafToPointFunctionSheaf :
    Mono (X.constantSheafToPointFunctionSheaf M) :=
  mono_of_injective_sheafFiber _ (X.injective_sheafFiber_map_constantSheafToPointFunctionSheaf M)

/-- The constant section `m` of the constant sheaf maps to the constant function `m`. -/
lemma constantSheafToPointFunctionSheaf_app_toSheafify (V : X.Etale) (m : M) :
    (X.constantSheafToPointFunctionSheaf M).hom.app (op V)
      ((CategoryTheory.toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)).app
        (op V) m) = fun _ ↦ m := by
  have h := toSheafify_sheafifyLift X.smallEtaleTopology (X.constToPointFunctionPresheaf M)
    (X.isSheaf_pointFunctionPresheaf M)
  exact congrArg (fun φ ↦ (φ.app (op V)).hom m) h

/-- **Global sections of a constant étale sheaf on a connected scheme.** For a connected scheme
`X`, the map from `M` to the sections over `X` of the constant étale sheaf `M` is bijective: a
section is a function on the points of `X` which is constant near each point, since it is
locally constant on an étale cover and étale maps are open; hence it is constant. -/
theorem bijective_toSheafify_app_terminal [ConnectedSpace X] :
    Function.Bijective
      ((CategoryTheory.toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)).app
        (op (Etale.mk (𝟙 X)))) := by
  let T : X.Etale := Etale.mk (𝟙 X)
  let ψ := (X.constantSheafToPointFunctionSheaf M).hom.app (op T)
  have hψ : Function.Injective ψ := by
    have : Mono ((sheafToPresheaf _ _).map (X.constantSheafToPointFunctionSheaf M)) :=
      Functor.map_mono _ _
    have : Mono ψ := (NatTrans.mono_iff_mono_app _).1 this (op T)
    exact (AddCommGrpCat.mono_iff_injective _).1 this
  obtain ⟨x₀⟩ := ‹ConnectedSpace X›.toNonempty
  refine ⟨fun m m' h ↦ ?_, fun σ ↦ ?_⟩
  · exact congrFun ((constantSheafToPointFunctionSheaf_app_toSheafify X M T m).symm.trans
      ((congrArg ψ h).trans (constantSheafToPointFunctionSheaf_app_toSheafify X M T m'))) x₀
  · let D : X → M := ψ σ
    have hloc : IsLocallyConstant D := by
      rw [IsLocallyConstant.iff_exists_open]
      intro x
      obtain ⟨W, g, w, ⟨m, hm⟩, hgw⟩ := exists_of_mem_smallEtaleTopology
        (Presheaf.imageSieve_mem X.smallEtaleTopology
          (CategoryTheory.toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)) σ) x
      have hD (w' : W.left) : D (g.left w') = m := by
        have h₁ := congrArg (fun s ↦ (X.constantSheafToPointFunctionSheaf M).hom.app (op W) s w') hm
        have h₂ := NatTrans.naturality_apply (X.constantSheafToPointFunctionSheaf M).hom g.op σ
        simp only at h₁
        rw [constantSheafToPointFunctionSheaf_app_toSheafify] at h₁
        exact (congrFun h₂ w').symm.trans h₁.symm
      have hgW : g.left = W.hom := by
        have := CategoryTheory.Over.w ((Etale.forget X).map g)
        simp only at this
        exact (Category.comp_id _).symm.trans this
      refine ⟨Set.range g.left, ?_, ⟨w, hgw⟩, ?_⟩
      · rw [hgW]
        exact W.hom.isOpenMap.isOpen_range
      · rintro _ ⟨w', rfl⟩
        rw [hD, ← hgw, hD]
    refine ⟨D x₀, hψ ?_⟩
    rw [constantSheafToPointFunctionSheaf_app_toSheafify]
    funext x
    exact hloc.apply_eq_of_preconnectedSpace x₀ x

end AlgebraicGeometry.Scheme
