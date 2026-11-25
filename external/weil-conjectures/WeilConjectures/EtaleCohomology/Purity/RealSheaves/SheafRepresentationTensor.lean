/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentation
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationFunctor

/-!
# The lisse sheaf–representation equivalence is a tensor equivalence

The lisse sheaf–representation equivalence (`definition-weil-representation--1`,
subsection `definition-weil-representation--1`) between lisse Weil sheaves on the curve
`C₀` and lisse representations of the Weil group `W(C₀)` is the functor `ℱ ↦ (ℱ_η̄, ρ_ℱ)`, the Weil
fundamental representation (`situation-weil`), and it is a tensor equivalence:

* the underlying representation of `e ℱ` is, naturally in `ℱ`, the Weil fundamental
  representation `ℱ ↦ (ℱ_t, ρ_ℱ)` on the stalk at the base point
  (`AlgebraicGeometry.WeilGroup.fundamentalRepFunctor`), up to the universe lift;
* there is an isomorphism of bifunctors `e (ℱ ⊗ 𝒢) ≅ e ℱ ⊗ e 𝒢`, which corresponds under this
  identification to the identification `(ℱ ⊗ 𝒢)_t ≅ ℱ_t ⊗ 𝒢_t` of the stalks
  (`AlgebraicGeometry.WeilGroup.fundamentalRepTensorIso`);
* the constant sheaf `ℚ̄_ℓ` goes to the trivial representation on `ℚ̄_ℓ`.

## Main statements

- `AlgebraicGeometry.WeilGroup.exists_equivalence_isLisse_tensor_of_lisseMonodromy`: for a
  monodromy of lisse sheaves on the geometric curve which is an equivalence at the base point.
- `AlgebraicGeometry.WeilGroup.exists_equivalence_isLisse_tensor`: for some choice of monodromy
  and base point.

Exactness is `AlgebraicGeometry.WeilGroup.isLisse_shortExact_iff`; the compatibilities with
stalks at closed points, duals and global sections are
`AlgebraicGeometry.WeilGroup.exists_equivalence_isLisse_of_lisseMonodromy`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilGroup

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} [C.Over (Spec (.of K))]
  [IsCurve (C ↘ Spec (.of K))] [SmoothOfRelativeDimension 1 (C ↘ Spec (.of K))]
  [GeometricallyConnected (C ↘ Spec (.of K))] (W : WeilGroup (C ↘ Spec (.of K))) (l : ℕ)
  [Fact l.Prime] [Fact (ringChar K ≠ l)]

omit [SmoothOfRelativeDimension 1 (C ↘ Spec (.of K))] [GeometricallyConnected (C ↘ Spec (.of K))] in
/-- Blueprint `definition-weil-representation--1` (subsection
`definition-weil-representation--1`): the lisse sheaf–representation equivalence is the
tensor functor `ℱ ↦ (ℱ_η̄, ρ_ℱ)`.

For a monodromy `M` of lisse sheaves on the geometric curve which is an equivalence at the base
point `t` of the base point data `B` (`proposition-lattices-representations-normal-scheme`), there
is an equivalence `e` between lisse Weil sheaves on `C₀` and lisse representations of `W(C₀)` such
that
* (`η`) the representation `e ℱ` is, naturally in `ℱ`, the Weil fundamental representation
  `(ℱ_t, ρ_ℱ)` of `situation-weil`
  (`AlgebraicGeometry.WeilGroup.fundamentalRepFunctor`; up to the universe lift
  `Rep.uliftFunctor`, the stalks living in a larger universe);
* (`τ`) `e` is compatible with tensor products: there is an isomorphism of bifunctors
  `e (ℱ ⊗ 𝒢) ≅ e ℱ ⊗ e 𝒢`, natural in `ℱ` and `𝒢`, which is, via `η`, the identification
  `(ℱ ⊗ 𝒢)_t ≅ ℱ_t ⊗ 𝒢_t` of `AlgebraicGeometry.WeilGroup.fundamentalRepTensorIso`;
* `e` sends the constant sheaf `ℚ̄_ℓ` to the trivial representation on `ℚ̄_ℓ`.
Exactness is `AlgebraicGeometry.WeilGroup.isLisse_shortExact_iff`. -/
theorem exists_equivalence_isLisse_tensor_of_lisseMonodromy
    (M : ProEtale.LisseMonodromy l (C ↘ Spec (.of K)).geometricFiber K) (B : BasePointData W)
    (hM : M.IsEquivalenceAt B.t) :
    ∃ (e : LisseWeilSheaf K l C ≌ (W.isLisseRep l).FullSubcategory)
      (η : e.functor ⋙ ObjectProperty.ι _ ⋙ Rep.uliftFunctor.{u, u + 1} (PadicAlgCl l) W.carrier ≅
        fundamentalRepFunctor M B.weilMonodromyData)
      (τ : LisseWeilSheaf.tensor K l C ⋙ e.functor ⋙ ObjectProperty.ι _ ≅
        (e.functor ⋙ ObjectProperty.ι _).prod (e.functor ⋙ ObjectProperty.ι _) ⋙
          Rep.tprodFunctor.{u} (PadicAlgCl l) W.carrier),
      (∀ (F G : LisseWeilSheaf K l C)
          (v : (e.functor.obj ((LisseWeilSheaf.tensor K l C).obj (F, G))).obj.V),
        ((fundamentalRepTensorIso M B.weilMonodromyData).hom.app (F, G)).hom
            ((η.hom.app ((LisseWeilSheaf.tensor K l C).obj (F, G))).hom (ULift.up v)) =
          TensorProduct.map
            ((η.hom.app F).hom.toLinearMap ∘ₗ ULift.moduleEquiv.symm.toLinearMap)
            ((η.hom.app G).hom.toLinearMap ∘ₗ ULift.moduleEquiv.symm.toLinearMap)
            ((τ.hom.app (F, G)).hom v)) ∧
      Nonempty ((e.functor.obj (LisseWeilSheaf.unit K l C)).obj.ρ.Equiv
        (Representation.trivial (PadicAlgCl l) W.carrier (PadicAlgCl l))) := by
  set D := B.weilMonodromyData
  obtain ⟨e, f, hf, hnat⟩ := Representation.exists_equivalence_of_realization_natural
    W.geometric.subtype
    (fun X : LisseWeilSheaf K l C ↦
      ProEtale.LisseMonodromy.StalkSpace B.t (X.obj.toLisse X.property))
    (fun X ↦ fundamentalRep M D X.obj X.property)
    (fun X ↦ fundamentalRep_isContinuousOn D X.obj X.property hM)
    (fun {X Y : LisseWeilSheaf K l C} (f : X ⟶ Y) ↦ stalkMap f.hom X.property Y.property)
    (fun X ↦ stalkMap_id X.property) (fun f g ↦ stalkMap_comp f.hom g.hom _ _ _)
    (fun {X Y : LisseWeilSheaf K l C} (f : X ⟶ Y) w v ↦ stalkMap_fundamentalRep D f.hom _ _ w v)
    (fun f f' h ↦ stalkMap_injective M hM f f' h)
    (fun φ hφ ↦ exists_stalkMap_eq D hM φ hφ)
    (fun V _ _ _ ρ hρ ↦ exists_fundamentalRep_linearEquiv D hM V ρ hρ) (W.isLisseRep l) fun X ↦
      ⟨fun ⟨h₁, h₂⟩ ↦ ⟨h₁, fun φ v ↦ h₂.continuous_apply φ v⟩,
        fun ⟨h₁, h₂⟩ ↦ ⟨h₁, WeilGroup.IsLisse.of_continuous_apply fun φ v ↦ h₂ φ v⟩⟩
  -- `e X` is the Weil fundamental representation of `X`
  let fR (X : LisseWeilSheaf K l C) :
      (e.functor.obj X).obj.ρ.Equiv (fundamentalRep M D X.obj X.property) :=
    .mk (f X) fun g ↦ LinearMap.ext (hf X g)
  have key {X Y : LisseWeilSheaf K l C} (φ : X ⟶ Y) (a) :
      (e.functor.map φ).hom.hom ((f X).symm a) =
        (f Y).symm (stalkMap φ.hom X.property Y.property a) := by
    rw [LinearEquiv.eq_symm_apply, hnat, LinearEquiv.apply_symm_apply]
  let η : e.functor ⋙ ObjectProperty.ι _ ⋙ Rep.uliftFunctor.{u, u + 1} (PadicAlgCl l) W.carrier ≅
      fundamentalRepFunctor M D :=
    NatIso.ofComponents (fun X ↦ Rep.mkIso (.mk (ULift.moduleEquiv.trans (f X)) fun g ↦
      LinearMap.ext fun x ↦ hf X g x.down)) fun {X Y} φ ↦
      Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x ↦ hnat φ x.down))
  -- the tensor structure
  let τe (X : LisseWeilSheaf K l C × LisseWeilSheaf K l C) :
      (e.functor.obj ((LisseWeilSheaf.tensor K l C).obj X)).obj.ρ.Equiv
        ((e.functor.obj X.1).obj.ρ.tprod (e.functor.obj X.2).obj.ρ) :=
    ((fR ((LisseWeilSheaf.tensor K l C).obj X)).trans (fundamentalRepTensorEquiv M D X.1 X.2)).trans
      (Representation.Equiv.tprodCongr (fR X.1) (fR X.2)).symm
  have hτe (X : LisseWeilSheaf K l C × LisseWeilSheaf K l C)
      (v : (e.functor.obj ((LisseWeilSheaf.tensor K l C).obj X)).obj.V) :
      τe X v = (TensorProduct.congr (f X.1) (f X.2)).symm
        (fundamentalRepTensorEquiv M D X.1 X.2 (f ((LisseWeilSheaf.tensor K l C).obj X) v)) :=
    rfl
  have hmap {X Y : LisseWeilSheaf K l C × LisseWeilSheaf K l C} (φ : X ⟶ Y) (y) :
      (TensorProduct.congr (f Y.1) (f Y.2)).symm
          (TensorProduct.map (stalkMap φ.1.hom X.1.property Y.1.property)
            (stalkMap φ.2.hom X.2.property Y.2.property) y) =
        TensorProduct.map (e.functor.map φ.1).hom.hom.toLinearMap
          (e.functor.map φ.2).hom.hom.toLinearMap
          ((TensorProduct.congr (f X.1) (f X.2)).symm y) := by
    induction y using TensorProduct.inductionOn with
    | tmul a b =>
      simp only [TensorProduct.map_tmul, TensorProduct.congr_symm_tmul,
        Representation.IntertwiningMap.coe_toLinearMap, key]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  let τ : LisseWeilSheaf.tensor K l C ⋙ e.functor ⋙ ObjectProperty.ι _ ≅
      (e.functor ⋙ ObjectProperty.ι _).prod (e.functor ⋙ ObjectProperty.ι _) ⋙
        Rep.tprodFunctor.{u} (PadicAlgCl l) W.carrier :=
    NatIso.ofComponents (fun X ↦ Rep.mkIso (τe X)) fun {X Y} φ ↦
      Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun v ↦ by
        have h : τe Y ((e.functor.map ((LisseWeilSheaf.tensor K l C).map φ)).hom.hom v) =
            TensorProduct.map (e.functor.map φ.1).hom.hom.toLinearMap
              (e.functor.map φ.2).hom.hom.toLinearMap (τe X v) := by
          rw [hτe, hτe, hnat, ← hmap]
          congr 1
          exact fundamentalRepTensorEquiv_naturality M D φ.1 φ.2 _
        exact h))
  refine ⟨e, η, τ, fun F G v ↦ ?_, ⟨(fR _).trans (fundamentalRepUnitEquiv M D)⟩⟩
  have hη (X : LisseWeilSheaf K l C) :
      (η.hom.app X).hom.toLinearMap ∘ₗ ULift.moduleEquiv.symm.toLinearMap = (f X).toLinearMap :=
    rfl
  rw [hη, hη]
  exact ((TensorProduct.congr (f F) (f G)).apply_symm_apply
    (fundamentalRepTensorEquiv M D F G (f ((LisseWeilSheaf.tensor K l C).obj (F, G)) v))).symm

/-- Blueprint `definition-weil-representation--1` (subsection
`definition-weil-representation--1`): the lisse sheaf–representation equivalence is the
tensor functor `ℱ ↦ (ℱ_η̄, ρ_ℱ)`, for some monodromy `M` of lisse sheaves on the geometric curve and
some base point data `B`; see
`AlgebraicGeometry.WeilGroup.exists_equivalence_isLisse_tensor_of_lisseMonodromy` for the properties
of `e`, `η` and `τ`. -/
theorem exists_equivalence_isLisse_tensor :
    ∃ (M : ProEtale.LisseMonodromy l (C ↘ Spec (.of K)).geometricFiber K) (B : BasePointData W)
      (e : LisseWeilSheaf K l C ≌ (W.isLisseRep l).FullSubcategory)
      (η : e.functor ⋙ ObjectProperty.ι _ ⋙ Rep.uliftFunctor.{u, u + 1} (PadicAlgCl l) W.carrier ≅
        fundamentalRepFunctor M B.weilMonodromyData)
      (τ : LisseWeilSheaf.tensor K l C ⋙ e.functor ⋙ ObjectProperty.ι _ ≅
        (e.functor ⋙ ObjectProperty.ι _).prod (e.functor ⋙ ObjectProperty.ι _) ⋙
          Rep.tprodFunctor.{u} (PadicAlgCl l) W.carrier),
      (∀ (F G : LisseWeilSheaf K l C)
          (v : (e.functor.obj ((LisseWeilSheaf.tensor K l C).obj (F, G))).obj.V),
        ((fundamentalRepTensorIso M B.weilMonodromyData).hom.app (F, G)).hom
            ((η.hom.app ((LisseWeilSheaf.tensor K l C).obj (F, G))).hom (ULift.up v)) =
          TensorProduct.map
            ((η.hom.app F).hom.toLinearMap ∘ₗ ULift.moduleEquiv.symm.toLinearMap)
            ((η.hom.app G).hom.toLinearMap ∘ₗ ULift.moduleEquiv.symm.toLinearMap)
            ((τ.hom.app (F, G)).hom v)) ∧
      Nonempty ((e.functor.obj (LisseWeilSheaf.unit K l C)).obj.ρ.Equiv
        (Representation.trivial (PadicAlgCl l) W.carrier (PadicAlgCl l))) := by
  have : ConnectedSpace (C ↘ Spec (.of K)).geometricFiber :=
    GeometricallyConnected.geometrically_connectedSpace (f := C ↘ Spec (.of K))
      (Scheme.specAlgebraicClosure K).hom (C ↘ Spec (.of K)).geometricFiberProj
      (C ↘ Spec (.of K)).geometricFiberToAlgebraicClosure (IsPullback.of_hasPullback _ _)
  have : Smooth (C ↘ Spec (.of K)) := SmoothOfRelativeDimension.smooth 1 _
  have : Smooth (C ↘ Spec (.of K)).geometricFiberToAlgebraicClosure :=
    inferInstanceAs (Smooth (Limits.pullback.snd _ _))
  have := IsRegular.of_smooth (C ↘ Spec (.of K)).geometricFiberToAlgebraicClosure
  obtain ⟨M, hM⟩ := ProEtale.exists_lisseMonodromy (l := l)
    (Y := (C ↘ Spec (.of K)).geometricFiber) (Ω := K)
  obtain ⟨B⟩ := nonempty_basePointData W
  exact ⟨M, B, exists_equivalence_isLisse_tensor_of_lisseMonodromy W l M B (hM B.t)⟩

end AlgebraicGeometry.WeilGroup
