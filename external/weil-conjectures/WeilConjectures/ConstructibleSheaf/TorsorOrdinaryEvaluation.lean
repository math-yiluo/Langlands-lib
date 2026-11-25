/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.TorsorSectionRepresentation
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import Mathlib.Algebra.Module.ZMod

/-! # Ordinary locally constant evaluation on a torsor

Source: Stacks Project, Tags 0DV5 (3), 0DV6 and 0A3R; sites.tex, Example
constant-sheaf and Tags 04TR and 04TS. Fixed-cover adaptation to arbitrary modules.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry
open Etale

private def uliftZModLinear {ℓ : ℕ} {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module (ULift.{u + 1} (ZMod ℓ)) M] [Module (ULift.{u + 1} (ZMod ℓ)) N]
    (f : M →+ N) : M →ₗ[ULift.{u + 1} (ZMod ℓ)] N where
  __ := f
  map_smul' r x := by
    let : Module (ZMod ℓ) M := Module.compHom M ULift.ringEquiv.symm.toRingHom
    let : Module (ZMod ℓ) N := Module.compHom N ULift.ringEquiv.symm.toRingHom
    exact ZMod.map_smul f r.down x

/-- Ordinary evaluation exists without imposing deck equivariance.
Source: Stacks Project, Tags 0DV5 (3), 0DV6 and 0A3R; sites.tex, Example
constant-sheaf and Tags 04TR and 04TS. Fixed-cover adaptation to arbitrary modules.
(blueprint: lem-weil-pbc-torsor-ordinary-evaluation)

Proof: For the etale map Y to V, inverse image identifies with restriction to
Y's small etale site. Under the supplied trivialization, a section over an etale
Y-object U is a locally constant A-valued function on U: constant presheaf sections
are locally constant sections, and sheafification glues these on etale covers.
Etale maps are open, so the glued constant labels give locally constant functions
on the underlying space. Conversely their open fibres give the required gluing.
These identifications preserve addition, scalars, and restriction. Since Y is
nonempty and connected, evaluation identifies the global sections of this constant
sheaf with A. Invert this isomorphism to identify A with F(Y); under this identification
a global section x restricts to the constant function with value x. For each W,
restrict s to U=W times_V Y, considered over Y, and read it as a locally constant
F(Y)-valued function. This defines the linear map beta_W. Restriction along W' to W
commutes with this construction, giving the naturality equation. For W=Y, restriction
along the diagonal is the original section s, giving the diagonal equation. The
empty object has the unique zero function; the construction also covers zero
coefficients and the identity torsor. No equivariance is imposed at this step. -/
theorem Scheme.GaloisCover.exists_ordinarySectionEvaluation
    {V : Scheme.{u}} [ConnectedSpace V] (ℓ : ℕ) [Fact ℓ.Prime]
    (P : Type u) [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V) [ConnectedSpace c.P]
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
    (A : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
    (h : Nonempty ((c.π)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))].obj F ≅
      (constantSheaf c.P.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj A)) :
    ∃ β : ∀ W : V.Etaleᵒᵖ, F.obj.obj W →ₗ[ULift.{u + 1} (ZMod ℓ)]
      LocallyConstant (c.sectionSpace W.unop) (F.obj.obj (op c.sectionObject)),
      (∀ (W W' : V.Etaleᵒᵖ) (f : W ⟶ W') (s : F.obj.obj W)
        (x : c.sectionSpace W'.unop),
      β W' (F.obj.map f s) x = β W s (c.sectionRestriction f.unop x)) ∧
      (∀ (s : F.obj.obj (op c.sectionObject)) (y : c.P),
      β (op c.sectionObject) s
        (pullback.lift (f := c.π) (g := c.π) (𝟙 c.P) (𝟙 c.P) (by simp) y) = s) := by
  classical
  let R := ULift.{u + 1} (ZMod ℓ)
  let C := ModuleCat.{u + 1} R
  let U := CategoryTheory.forget₂ C AddCommGrpCat.{u + 1}
  have : PreservesColimitsOfSize.{u + 1, u + 1} U :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, u + 1, u + 1} R
  have : c.P.smallEtaleTopology.PreservesSheafification U :=
    GrothendieckTopology.instPreservesSheafification c.P.smallEtaleTopology U
  let D := MorphismProperty.Over.map ⊤ c.etale
  let Q := c.π.Etale
  let adj := MorphismProperty.Over.mapPullbackAdj @AlgebraicGeometry.Etale ⊤
    c.π c.etale trivial
  let T : c.P.Etale := Scheme.Etale.mk (𝟙 c.P)
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  obtain ⟨e⟩ := h
  -- Restriction, forgetting coefficients, and the constant-function comparison.
  let k : (sheafCompose c.P.smallEtaleTopology U).obj
      ((localizationRestriction C c.π c.etale).obj F) ≅
      Scheme.Etale.continuousMapSheaf c.P A :=
    (sheafCompose c.P.smallEtaleTopology U).mapIso
      ((upperStarIsoLocalizationRestriction C c.π c.etale).app F).symm ≪≫
    (sheafCompose c.P.smallEtaleTopology U).mapIso e ≪≫
    (constantCommuteCompose c.P.smallEtaleTopology U).app A ≪≫
    Scheme.Etale.constantSheafIsoContinuousMapSheaf c.P A
  let t : D.obj T ≅ c.sectionObject :=
    MorphismProperty.Over.isoMk (Iso.refl _) (by
      change (𝟙 c.P) ≫ c.π = (𝟙 c.P) ≫ c.π
      rfl)
  obtain ⟨y₀⟩ := ‹ConnectedSpace c.P›.toNonempty
  let ev : C(c.P, A) ≃+ A :=
    { toFun := fun f ↦ f y₀
      invFun := ContinuousMap.const _
      left_inv := by
        intro f
        ext y
        exact ((IsLocallyConstant.iff_continuous f).2 f.continuous).apply_eq_of_preconnectedSpace
          y₀ y
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  -- Connectedness identifies the coefficient group with the sections over the cover.
  let b : F.obj.obj (op c.sectionObject) ≃+ A :=
    ((F.obj.mapIso t.op).toLinearEquiv.toAddEquiv).trans
      (((((sheafToPresheaf _ _).mapIso k).app (op T)).addCommGroupIsoToAddEquiv).trans ev)
  let a₀ (W : V.Etaleᵒᵖ) : F.obj.obj W →+ C(c.sectionSpace W.unop, A) :=
    (k.hom.hom.app (op (Q.obj W.unop))).hom.comp
      (F.obj.map (adj.counit.app W.unop).op).hom.toAddMonoidHom
  let a (W : V.Etaleᵒᵖ) :
      F.obj.obj W →+ LocallyConstant (c.sectionSpace W.unop) A :=
    { toFun := fun s ↦
        let f := a₀ W s
        ⟨f, (IsLocallyConstant.iff_continuous f).2 f.continuous⟩
      map_zero' := by
        ext x
        change a₀ W 0 x = 0
        rw [map_zero]
        rfl
      map_add' := by
        intro s s'
        ext x
        change a₀ W (s + s') x = a₀ W s x + a₀ W s' x
        rw [map_add]
        rfl }
  -- Every additive map between these torsion groups is linear over the lifted ZMod.
  let β (W : V.Etaleᵒᵖ) : F.obj.obj W →ₗ[R]
      LocallyConstant (c.sectionSpace W.unop) (F.obj.obj (op c.sectionObject)) :=
    uliftZModLinear (ℓ := ℓ)
      ((LocallyConstant.mapAddMonoidHom b.symm.toAddMonoidHom).comp (a W))
  refine ⟨β, ?_, ?_⟩
  · intro W W' f s x
    change b.symm (a₀ W' (F.obj.map f s) x) =
      b.symm (a₀ W s (c.sectionRestriction f.unop x))
    congr 1
    have hn := ConcreteCategory.congr_hom
      (k.hom.hom.naturality (Q.map f.unop).op)
      (F.obj.map (adj.counit.app W.unop).op s)
    have hc : (adj.counit.app W'.unop) ≫ f.unop =
        D.map (Q.map f.unop) ≫ (adj.counit.app W.unop) :=
      (adj.counit.naturality f.unop).symm
    have hF : F.obj.map (adj.counit.app W'.unop).op (F.obj.map f s) =
        F.obj.map (D.map (Q.map f.unop)).op
          (F.obj.map (adj.counit.app W.unop).op s) := by
      have hm := congrArg
        (fun g : D.obj (Q.obj W'.unop) ⟶ W.unop ↦ F.obj.map g.op) hc
      simp only [op_comp, Functor.map_comp] at hm
      exact ConcreteCategory.congr_hom hm s
    have hval : a₀ W' (F.obj.map f s) =
        (a₀ W s).comp (Q.map f.unop).left.base.hom := by
      change (k.hom.hom.app (op (Q.obj W'.unop))).hom
        ((F.obj.map (adj.counit.app W'.unop).op).hom ((F.obj.map f).hom s)) = _
      rw [hF]
      exact hn
    exact congrArg (fun g : C(c.sectionSpace W'.unop, A) ↦ g x) hval
  · intro s y
    let δ : T ⟶ Q.obj c.sectionObject :=
      MorphismProperty.Over.homMk
        (pullback.lift (f := c.π) (g := c.π) (𝟙 c.P) (𝟙 c.P) (by simp))
        (by
          change pullback.lift (f := c.π) (g := c.π) (𝟙 c.P) (𝟙 c.P) _ ≫
            pullback.snd c.π c.π = 𝟙 c.P
          exact pullback.lift_snd _ _ _)
    have hd : D.map δ ≫ adj.counit.app c.sectionObject = t.hom := by
      apply MorphismProperty.Over.Hom.ext
      change pullback.lift (f := c.π) (g := c.π) (𝟙 c.P) (𝟙 c.P) _ ≫
        pullback.fst c.π c.π = 𝟙 c.P
      simp
    have hn := ConcreteCategory.congr_hom (k.hom.hom.naturality δ.op)
      (F.obj.map (adj.counit.app c.sectionObject).op s)
    have hF : F.obj.map (D.map δ).op
        (F.obj.map (adj.counit.app c.sectionObject).op s) =
        F.obj.map t.hom.op s := by
      have hm := congrArg (fun g : D.obj T ⟶ c.sectionObject ↦ F.obj.map g.op) hd
      simp only [op_comp, Functor.map_comp] at hm
      exact ConcreteCategory.congr_hom hm s
    have hv : (show C(c.P, A) from k.hom.hom.app (op T)
        (F.obj.map t.hom.op s)) =
        (a₀ (op c.sectionObject) s).comp δ.left.base.hom := by
      rw [← hF]
      exact hn
    change b.symm (a₀ (op c.sectionObject) s
      (pullback.lift (f := c.π) (g := c.π) (𝟙 c.P) (𝟙 c.P) _ y)) = s
    apply b.injective
    rw [b.apply_symm_apply]
    have hy := congrArg (fun g : C(c.P, A) ↦ g y) hv
    change (show C(c.P, A) from k.hom.hom.app (op T)
      (F.obj.map t.hom.op s)) y = a₀ (op c.sectionObject) s (δ.left y) at hy
    refine hy.symm.trans ?_
    let g : C(c.P, A) := k.hom.hom.app (op T) (F.obj.map t.hom.op s)
    exact ((IsLocallyConstant.iff_continuous g).2 g.continuous).apply_eq_of_preconnectedSpace
      y y₀

end AlgebraicGeometry
