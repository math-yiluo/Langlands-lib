/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Coinvariants
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalSystems
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationData
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationDual
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationSections
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationStalk
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationTensor
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyExists
public import WeilConjectures.WeilSheaf.GeometricCoinvariants

/-!
# Lisse Weil sheaves and lisse Weil representations

Let `C₀` be a smooth geometrically connected curve over the finite field `K` with Weil group
`W = W(C₀)` (`AlgebraicGeometry.WeilGroup`). This file connects the two sides of the purity theorem
for real sheaves: the sheaf side, lisse Weil sheaves `AlgebraicGeometry.WeilSheaf` on `C₀` with
their geometric stalks, local Frobenius, global sections and geometric coinvariants, and the
representation side, lisse representations of `W(C₀)`.

The lisse sheaf–representation equivalence (`definition-weil-representation--1`,
`AlgebraicGeometry.WeilGroup.exists_equivalence_isLisse`) sends a lisse Weil sheaf `ℱ` to its
Weil fundamental representation `(V, ρ) = (ℱ_η̄, ρ_ℱ)`. From it we deduce that every lisse
representation `ρ` of `W(C₀)` is the fundamental representation of a lisse Weil sheaf `ℱ`
whose local Frobenius at a closed point `x` has the characteristic polynomial of
`ρ (Frob_x)`, and whose geometric coinvariants `Γ(C̄, ℱ^∨)^∨`
(`AlgebraicGeometry.WeilSheaf.geometricCoinvariants`) are the coinvariants `V_{π₁(C)}` with the
Frobenius induced by the degree-one lift `γ`
(`AlgebraicGeometry.WeilGroup.exists_weilSheaf_of_isLisse`).

## Main statements

- `AlgebraicGeometry.WeilGroup.exists_equivalence_isLisse`: the lisse sheaf–representation
  equivalence.
- `AlgebraicGeometry.WeilGroup.exists_weilSheaf_of_isLisse`: the lisse Weil sheaf of a lisse
  representation, with its stalks and its geometric coinvariants.

The natural forms of the identification of the equivalence with the Weil fundamental
representation and of its tensor compatibility (an isomorphism of bifunctors, and the unit) are
`AlgebraicGeometry.WeilGroup.exists_equivalence_isLisse_tensor_of_lisseMonodromy` in
`WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentationTensor`.

## Implementation notes

The Weil fundamental representation of `situation-weil` is the geometric
generic stalk `ℱ_η̄` with the monodromy action of `π₁(C₀, η̄)` extended to the Weil group by the
Weil structure. It is constructed in
`WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentation`
(`AlgebraicGeometry.WeilGroup.fundamentalRep`) from a monodromy of lisse sheaves on the geometric
curve (`AlgebraicGeometry.ProEtale.LisseMonodromy`,
`proposition-lattices-representations-normal-scheme`), at a base point which depends on choices; the
equivalence is therefore existentially quantified, and the fact that it *is* the Weil fundamental
representation is recorded by the properties of it that the blueprint uses: at a closed point `x`,
the stalk `ℱ_x̄` with its local Frobenius `F_x` is `V` with `ρ (Frob_x)` (the stalk at `x̄` being
transported to the base point along a path, which carries the geometric Frobenius of `κ(x)` to
the Frobenius element `Frob_x` of `W(C₀)`); the equivalence is compatible with duals (it is a
tensor equivalence); and the global sections `H⁰(C̄, ℱ)` are the invariants `V ^ {π₁(C)}` with
the Frobenius `ρ (γ)`, which is `lemma-degree-zero-top-cohomology--1` for `U₀ = C₀`. The last clause
is a consequence of the equivalence in the blueprint (`lemma-degree-zero-top-cohomology--1`); it is
recorded with it here because the functor, being existentially quantified, can only be described
through its properties.
-/

@[expose] public section

universe u

open CategoryTheory

namespace FrobeniusModule

variable {k : Type*} [Field k]

/-- If a Frobenius module `M` is identified with the dual `N^∨` of a finite-dimensional space
`N` with an automorphism `T`, so that the Frobenius of `M` becomes the inverse transpose of
`T`, then the dual Frobenius module `M^∨` is `N` with `T`. -/
theorem exists_linearEquiv_dual_of_linearEquiv_dual (M : FrobeniusModule k) {N : Type*}
    [AddCommGroup N] [Module k N] [FiniteDimensional k N] (T : N ≃ₗ[k] N)
    (c : M.carrier ≃ₗ[k] Module.Dual k N) (hc : ∀ m n, c (M.frobenius m) (T n) = c m n) :
    ∃ f : M.dual.carrier ≃ₗ[k] N, ∀ φ, f (M.dual.frobenius φ) = T (f φ) := by
  refine ⟨c.dualMap.symm.trans (Module.evalEquiv k N).symm, fun φ ↦ ?_⟩
  apply (Module.evalEquiv k N).injective
  refine LinearMap.ext fun ψ ↦ ?_
  have key : M.frobenius.symm (c.symm ψ) = c.symm (ψ ∘ₗ T.toLinearMap) := by
    rw [LinearEquiv.symm_apply_eq, LinearEquiv.symm_apply_eq]
    refine LinearMap.ext fun n ↦ ?_
    have h := hc (c.symm (ψ ∘ₗ T.toLinearMap)) (T.symm n)
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
    rw [h, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply]
  rw [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, LinearEquiv.trans_apply,
    Module.evalEquiv_apply, Module.Dual.eval_apply, ← LinearEquiv.coe_toLinearMap T,
    ← LinearMap.comp_apply, Module.apply_evalEquiv_symm_apply, LinearEquiv.dualMap_symm]
  change (show Module.Dual k M.carrier from M.dual.frobenius φ) (c.symm ψ) =
    (show Module.Dual k M.carrier from φ) (c.symm (ψ ∘ₗ T.toLinearMap))
  rw [dual_frobenius_apply, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, key]

/-- Dualising invariant sections of a contragredient representation gives coinvariants,
compatibly with the action of a group element. -/
private theorem exists_linearEquiv_dual_of_invariants {G : Type*} [Group G] {V V' : Type*}
    [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [AddCommGroup V'] [Module k V'] (ρ : Representation k G V)
    (ρ' : Representation k G V') (H : Subgroup G) [H.Normal] (γ : G)
    (b : ρ'.Equiv ρ.dual) (M : FrobeniusModule k)
    (a : M.carrier ≃ₗ[k] Representation.invariants (ρ'.comp H.subtype))
    (ha : ∀ v, (a (M.frobenius v) : V') = ρ' γ (a v)) :
    ∃ f : M.dual.carrier ≃ₗ[k] Representation.Coinvariants (ρ.comp H.subtype),
      ∀ v, f (M.dual.frobenius v) = ρ.toCoinvariants H γ (f v) := by
  let bL := b.toLinearEquiv
  have hb (g : G) (u) : bL (ρ' g u) = ρ.dual g (bL u) :=
    Representation.IntertwiningMap.isIntertwining _ _ b.toIntertwiningMap g u
  have hdual (g : G) (φ : Module.Dual k V) (w) : ρ.dual g φ w = φ (ρ g⁻¹ w) := by
    rw [Representation.dual_apply]
    rfl
  -- the linear forms coming from invariants of `ρ'` are invariant
  have hinv (u : Representation.invariants (ρ'.comp H.subtype)) (h : H) (w) :
      bL u.1 (ρ h w) = bL u.1 w := by
    have h1 : ρ' ((h⁻¹ : H) : G) u.1 = u.1 := u.2 h⁻¹
    have h2 := congrArg (fun z ↦ bL z w) h1
    rw [hb, hdual, Subgroup.coe_inv, inv_inv] at h2
    exact h2
  have hmk (h : H) (v : V) : Representation.Coinvariants.mk (ρ.comp H.subtype) (ρ h v) =
      Representation.Coinvariants.mk (ρ.comp H.subtype) v :=
    Representation.Coinvariants.mk_self_apply _ h v
  -- invariant linear forms on `V` are the linear forms on the coinvariants
  let toF : Representation.invariants (ρ'.comp H.subtype) →ₗ[k]
      Module.Dual k (Representation.Coinvariants (ρ.comp H.subtype)) :=
    { toFun u := Representation.Coinvariants.lift (ρ.comp H.subtype) (bL u.1)
        (fun h ↦ LinearMap.ext fun v ↦ by
          simp only [LinearMap.comp_apply, MonoidHom.comp_apply, Subgroup.coe_subtype]
          rw [hinv u h])
      map_add' u u' := Representation.Coinvariants.hom_ext (LinearMap.ext fun v ↦ by
        simp [Representation.Coinvariants.lift_mk])
      map_smul' r u := Representation.Coinvariants.hom_ext (LinearMap.ext fun v ↦ by
        simp [Representation.Coinvariants.lift_mk]) }
  have htoF (u) (v : V) : toF u (Representation.Coinvariants.mk _ v) = bL u.1 v :=
    rfl
  let invF : Module.Dual k (Representation.Coinvariants (ρ.comp H.subtype)) →ₗ[k]
      Representation.invariants (ρ'.comp H.subtype) :=
    { toFun φ := ⟨bL.symm (φ ∘ₗ Representation.Coinvariants.mk _), fun h ↦ by
        change ρ' (h : G) _ = _
        apply bL.injective
        rw [hb, LinearEquiv.apply_symm_apply]
        refine LinearMap.ext fun w ↦ ?_
        rw [hdual]
        simp only [LinearMap.comp_apply]
        rw [← Subgroup.coe_inv, hmk]⟩
      map_add' φ φ' := Subtype.ext (by simp [LinearMap.add_comp])
      map_smul' r φ := Subtype.ext (by simp [LinearMap.smul_comp]) }
  let d : Representation.invariants (ρ'.comp H.subtype) ≃ₗ[k]
      Module.Dual k (Representation.Coinvariants (ρ.comp H.subtype)) :=
    LinearEquiv.ofLinearMap toF invF
    (LinearMap.ext fun φ ↦ Representation.Coinvariants.hom_ext (LinearMap.ext fun v ↦ by
      change bL (bL.symm _) v = _
      rw [LinearEquiv.apply_symm_apply]
      simp))
    (LinearMap.ext fun u ↦ Subtype.ext (by
      change bL.symm (toF u ∘ₗ Representation.Coinvariants.mk _) = u.1
      rw [LinearEquiv.symm_apply_eq]
      refine LinearMap.ext fun v ↦ ?_
      simp only [LinearMap.comp_apply, htoF]))
  -- the Frobenius `ρ (γ)` on the coinvariants
  let Q := ρ.toCoinvariants H
  let T := LinearEquiv.ofBijective (Q γ) (Q.apply_bijective γ)
  have hc (m : M.carrier) (n : Representation.Coinvariants (ρ.comp H.subtype)) :
      (a.trans d) (M.frobenius m) (T n) = (a.trans d) m n := by
    refine Representation.Coinvariants.induction_on n fun v ↦ ?_
    change toF (a _) (Q γ (Representation.Coinvariants.mk _ v)) =
      toF (a m) (Representation.Coinvariants.mk _ v)
    rw [Representation.toCoinvariants_mk, htoF, htoF, ha, hb, hdual, ρ.inv_self_apply]
  exact exists_linearEquiv_dual_of_linearEquiv_dual M T (a.trans d) hc

end FrobeniusModule

namespace AlgebraicGeometry

namespace WeilGroup

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} [C.Over (Spec (.of K))]
  [IsCurve (C ↘ Spec (.of K))] [SmoothOfRelativeDimension 1 (C ↘ Spec (.of K))]
  [GeometricallyConnected (C ↘ Spec (.of K))] (W : WeilGroup (C ↘ Spec (.of K))) (l : ℕ)
  [Fact l.Prime] [Fact (ringChar K ≠ l)]

/-- Blueprint `definition-weil-representation--1` (subsection
`definition-weil-representation--1`): The lisse sheaf–representation equivalence.

The functor `ℱ ↦ (V, ρ) = (ℱ_η̄, ρ_ℱ)`, sending a lisse Weil sheaf on the curve `C₀` to its Weil
fundamental representation (`situation-weil`), is an exact tensor
equivalence between lisse Weil sheaves on `C₀` and lisse representations of `W(C₀)`
(`AlgebraicGeometry.WeilGroup.isLisseRep`). The functor `e.functor` is the Weil fundamental
representation:

* at every closed point `x`, the geometric stalk `ℱ_x̄` with its local Frobenius `F_x` is
  isomorphic to `V` with `ρ (Frob_x)`, `Frob_x = W.frobenius x` being a Frobenius element at `x`
  (`situation-weil`, the stalk at `x̄` transported to the base point along a
  path);
* it is compatible with duals: the representation of `ℱ^∨` is the contragredient of that of `ℱ`;
* the global sections `H⁰(C̄, ℱ)` are the invariants `V ^ {π₁(C)}`, compatibly with the
  Frobenius `ρ (γ)` of the degree-one lift `γ` (`lemma-degree-zero-top-cohomology--1`, for
  `U₀ = C₀`; for a general open `U₀ ⊆ C₀` see
  `AlgebraicGeometry.WeilGroup.exists_globalSections_upperStar_linearEquiv_invariants`);
* it is compatible with tensor products: the representation of `ℱ ⊗ 𝒢` is the tensor product of
  those of `ℱ` and `𝒢`.

It is exact, as is any equivalence between these abelian categories
(`AlgebraicGeometry.WeilGroup.isLisse_shortExact_iff`). -/
theorem exists_equivalence_isLisse_of_lisseMonodromy
    (M : ProEtale.LisseMonodromy l (C ↘ Spec (.of K)).geometricFiber K) (B : BasePointData W)
    (hM : M.IsEquivalenceAt B.t) :
    ∃ e : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse) ≌
        ObjectProperty.FullSubcategory (W.isLisseRep l),
      (∀ (F : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse))
          (x : C.finitePoints),
        ∃ f : (F.obj.stalk x).carrier ≃ₗ[PadicAlgCl l] (e.functor.obj F).obj.V,
          ∀ v, f ((F.obj.stalk x).frobenius v) = (e.functor.obj F).obj.ρ (W.frobenius x) (f v)) ∧
      (∀ F : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse),
        Nonempty ((e.functor.obj ⟨F.obj.dual F.property, F.property.dual⟩).obj.ρ.Equiv
          (e.functor.obj F).obj.ρ.dual)) ∧
      (∀ F : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse),
        ∃ f : F.obj.globalSections.carrier ≃ₗ[PadicAlgCl l]
            Representation.invariants ((e.functor.obj F).obj.ρ.comp W.geometric.subtype),
          ∀ v, (f (F.obj.globalSections.frobenius v) : (e.functor.obj F).obj.V) =
            (e.functor.obj F).obj.ρ W.frobeniusLift (f v)) ∧
      (∀ F G : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse),
        Nonempty ((e.functor.obj ⟨F.obj.tensorObj G.obj F.property,
            F.property.tensorObj G.property⟩).obj.ρ.Equiv
          ((e.functor.obj F).obj.ρ.tprod (e.functor.obj G).obj.ρ))) ∧
      ∀ F : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse),
        ∃ f : (e.functor.obj F).obj.V ≃ₗ[PadicAlgCl l]
            ProEtale.LisseMonodromy.StalkSpace B.t (F.obj.toLisse F.property),
          ∀ g v, f ((e.functor.obj F).obj.ρ g v) =
            fundamentalRep M B.weilMonodromyData F.obj F.property g (f v) := by
  have : ConnectedSpace (C ↘ Spec (.of K)).geometricFiber :=
    GeometricallyConnected.geometrically_connectedSpace (f := C ↘ Spec (.of K))
      (Scheme.specAlgebraicClosure K).hom (C ↘ Spec (.of K)).geometricFiberProj
      (C ↘ Spec (.of K)).geometricFiberToAlgebraicClosure (IsPullback.of_hasPullback _ _)
  have : Smooth (C ↘ Spec (.of K)) := SmoothOfRelativeDimension.smooth 1 _
  have : Smooth (C ↘ Spec (.of K)).geometricFiberToAlgebraicClosure :=
    inferInstanceAs (Smooth (Limits.pullback.snd _ _))
  have := IsRegular.of_smooth (C ↘ Spec (.of K)).geometricFiberToAlgebraicClosure
  have : CompactSpace (C ↘ Spec (.of K)).geometricFiber := inferInstance
  obtain ⟨e, he⟩ := exists_equivalence_fundamentalRep M B.weilMonodromyData hM
  choose f hf using he
  set D := B.weilMonodromyData
  have hf' (F : LisseWeilSheaf K l C) (g : W.carrier) (w) :
      (f F).symm (fundamentalRep M D F.obj F.property g w) =
        (e.functor.obj F).obj.ρ g ((f F).symm w) := by
    rw [LinearEquiv.symm_apply_eq, hf, LinearEquiv.apply_symm_apply]
  refine ⟨e, fun F x ↦ ?_, fun F ↦ ?_, fun F ↦ ?_, fun F G ↦ ?_, fun F ↦ ⟨f F, hf F⟩⟩
  · -- the stalk at `x̄`, transported to the base point along a path `π`
    obtain ⟨π⟩ := PreGaloisCategory.nonempty_iso_of_fiberFunctor
      (Scheme.FiniteEtale.fiber ((C ↘ Spec (.of K)).geometricFiberPointOfFinitePoint x))
      (Scheme.FiniteEtale.fiber B.t)
    set h := Aut.of (B.frobeniusLoop x π ≪≫ (B.frobPathPow _).symm)
    set m := (C ↘ Spec (.of K)).degreeOver x.1
    obtain ⟨c, hc⟩ := isConj_iff.mp (B.isConj_frobenius x π)
    set ρ := (e.functor.obj F).obj.ρ
    have key (v : (F.obj.stalk x).carrier) :
        M.monoLinear π (F.obj.toLisse F.property) ((F.obj.stalk x).frobenius v) =
          fundamentalRep M D F.obj F.property (B.frobLift ^ m * B.geomHom h)
            (M.monoLinear π _ v) := by
      rw [monoLinear_stalk_frobenius, map_mul, ← B.geomEquiv_apply h, Module.End.mul_apply,
        fundamentalRep_geometric, show B.geomEquiv = D.geomEquiv from rfl,
        ContinuousMulEquiv.symm_apply_apply, map_pow, show B.frobLift = D.frobLift from rfl,
        fundamentalRep_frobLift]
      rw [LinearEquiv.coe_pow, Module.End.pow_apply, LinearEquiv.coe_toLinearMap]
      rfl
    let r : (e.functor.obj F).obj.V ≃ₗ[PadicAlgCl l] (e.functor.obj F).obj.V :=
      LinearEquiv.ofLinearMap (ρ c⁻¹) (ρ c)
        (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)
        (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
    refine ⟨(WeilCoefficients.linearEquivOfIso ((M.mono π).app (F.obj.toLisse F.property))).trans
      ((f F).symm.trans r), fun v ↦ ?_⟩
    change ρ c⁻¹ ((f F).symm (M.monoLinear π _ ((F.obj.stalk x).frobenius v))) =
      ρ (W.frobenius x) (ρ c⁻¹ ((f F).symm (M.monoLinear π _ v)))
    rw [key, hf', ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, ← hc]
    congr 2
    group
  · -- duals
    obtain ⟨b⟩ := nonempty_equiv_fundamentalRep_dual (M := M) D F.obj F.property
    let fF : (e.functor.obj F).obj.ρ.Equiv (fundamentalRep M D F.obj F.property) :=
      .mk (f F) fun g ↦ LinearMap.ext (hf F g)
    let fd : (e.functor.obj ⟨F.obj.dual F.property, F.property.dual⟩).obj.ρ.Equiv
        (fundamentalRep M D (F.obj.dual F.property) F.property.dual) :=
      .mk (f _) fun g ↦ LinearMap.ext (hf _ g)
    let dF : (fundamentalRep M D F.obj F.property).dual.Equiv (e.functor.obj F).obj.ρ.dual :=
      .mk (f F).dualMap fun g ↦ LinearMap.ext fun φ ↦ LinearMap.ext fun w ↦ by
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.dualMap_apply,
          Representation.dual_apply, Module.Dual.transpose_apply, hf]
    exact ⟨(fd.trans b).trans dF⟩
  · -- global sections
    obtain ⟨a, ha⟩ := exists_globalSections_linearEquiv_invariants (M := M) D hM F.obj
      F.property
      W.frobeniusLift W.deg_frobeniusLift
    have hinv (w) : w ∈ Representation.invariants
        ((fundamentalRep M D F.obj F.property).comp W.geometric.subtype) ↔
        (f F).symm w ∈ Representation.invariants
          ((e.functor.obj F).obj.ρ.comp W.geometric.subtype) := by
      simp only [Representation.mem_invariants, MonoidHom.comp_apply, ← hf',
        (f F).symm.injective.eq_iff]
    let s := (f F).symm.ofSubmodules
      (Representation.invariants ((fundamentalRep M D F.obj F.property).comp W.geometric.subtype))
      (Representation.invariants ((e.functor.obj F).obj.ρ.comp W.geometric.subtype)) (by
        ext w
        simp only [Submodule.mem_map, LinearEquiv.coe_coe]
        constructor
        · rintro ⟨w, hw, rfl⟩
          exact (hinv w).1 hw
        · intro hw
          exact ⟨f F w, (hinv _).2 (by rwa [LinearEquiv.symm_apply_apply]),
            LinearEquiv.symm_apply_apply _ _⟩)
    refine ⟨a.trans s, fun v ↦ ?_⟩
    change (f F).symm (a (F.obj.globalSections.frobenius v) : _) = _
    rw [ha, hf']
    rfl
  · -- tensor products
    obtain ⟨b⟩ := nonempty_equiv_fundamentalRep_tensorObj D F.obj G.obj F.property G.property
    let fF : (e.functor.obj F).obj.ρ.Equiv (fundamentalRep M D F.obj F.property) :=
      .mk (f F) fun g ↦ LinearMap.ext (hf F g)
    let fG : (e.functor.obj G).obj.ρ.Equiv (fundamentalRep M D G.obj G.property) :=
      .mk (f G) fun g ↦ LinearMap.ext (hf G g)
    let fT : (e.functor.obj ⟨F.obj.tensorObj G.obj F.property,
        F.property.tensorObj G.property⟩).obj.ρ.Equiv
        (fundamentalRep M D (F.obj.tensorObj G.obj F.property)
          (F.property.tensorObj G.property)) :=
      .mk (f _) fun g ↦ LinearMap.ext (hf _ g)
    exact ⟨(fT.trans b).trans (Representation.Equiv.tprodCongr fF.symm fG.symm)⟩

/-- Blueprint `definition-weil-representation--1` (subsection
`definition-weil-representation--1`): The lisse sheaf–representation equivalence, for
some monodromy of lisse sheaves on the geometric curve and some base point data; see
`AlgebraicGeometry.WeilGroup.exists_equivalence_isLisse_of_lisseMonodromy` for the properties. -/
theorem exists_equivalence_isLisse :
    ∃ e : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse) ≌
        ObjectProperty.FullSubcategory (W.isLisseRep l),
      (∀ (F : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse))
          (x : C.finitePoints),
        ∃ f : (F.obj.stalk x).carrier ≃ₗ[PadicAlgCl l] (e.functor.obj F).obj.V,
          ∀ v, f ((F.obj.stalk x).frobenius v) = (e.functor.obj F).obj.ρ (W.frobenius x) (f v)) ∧
      (∀ F : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse),
        Nonempty ((e.functor.obj ⟨F.obj.dual F.property, F.property.dual⟩).obj.ρ.Equiv
          (e.functor.obj F).obj.ρ.dual)) ∧
      (∀ F : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse),
        ∃ f : F.obj.globalSections.carrier ≃ₗ[PadicAlgCl l]
            Representation.invariants ((e.functor.obj F).obj.ρ.comp W.geometric.subtype),
          ∀ v, (f (F.obj.globalSections.frobenius v) : (e.functor.obj F).obj.V) =
            (e.functor.obj F).obj.ρ W.frobeniusLift (f v)) ∧
      (∀ F G : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse),
        Nonempty ((e.functor.obj ⟨F.obj.tensorObj G.obj F.property,
            F.property.tensorObj G.property⟩).obj.ρ.Equiv
          ((e.functor.obj F).obj.ρ.tprod (e.functor.obj G).obj.ρ))) := by
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
  obtain ⟨e, h₁, h₂, h₃, h₄, -⟩ := exists_equivalence_isLisse_of_lisseMonodromy W l M B (hM B.t)
  exact ⟨e, h₁, h₂, h₃, h₄⟩

/-- The linear isomorphism underlying an isomorphism of representations. -/
private noncomputable def repLinearEquivOfIso {k G : Type*} [CommRing k] [Monoid G]
    {A B : Rep.{u} k G} (e : A ≅ B) : A.V ≃ₗ[k] B.V :=
  LinearEquiv.ofLinearMap e.hom.hom.toLinearMap e.inv.hom.toLinearMap
    (LinearMap.ext fun b ↦ by
      change (e.inv ≫ e.hom).hom b = b
      rw [e.inv_hom_id]
      rfl)
    (LinearMap.ext fun a ↦ by
      change (e.hom ≫ e.inv).hom a = a
      rw [e.hom_inv_id]
      rfl)

private theorem repLinearEquivOfIso_apply {k G : Type*} [CommRing k] [Monoid G]
    {A B : Rep.{u} k G} (e : A ≅ B) (a : A.V) : repLinearEquivOfIso e a = e.hom.hom a :=
  rfl

variable {W l}

/-- A lisse representation `ρ` of `W(C₀)` is the Weil fundamental representation of a lisse Weil
sheaf `ℱ` on `C₀`: the local Frobenius `F_x` on the stalk `ℱ_x̄` has the characteristic
polynomial of `ρ (Frob_x)` at every closed point `x`, and the geometric coinvariants
`Γ(C̄, ℱ^∨)^∨` of `ℱ` are the coinvariants `V_{π₁(C)}` of `ρ`, with the Frobenius induced by
`ρ (γ)`.

The sheaf is the image of `ρ` under the inverse of the equivalence
`AlgebraicGeometry.WeilGroup.exists_equivalence_isLisse`. Its stalks are described by that
equivalence. For the coinvariants: the global sections `Γ(C̄, ℱ^∨)` are the invariants of the
representation of `ℱ^∨`, which is the contragredient `ρ^∨`, and the `π₁(C)`-invariant linear
forms on `V` are the linear forms on `V_{π₁(C)}`; dualising gives `V_{π₁(C)}` back, with the
Frobenius `ρ (γ)`. -/
theorem exists_weilSheaf_of_isLisse {V : Type u} [AddCommGroup V] [Module (PadicAlgCl l) V]
    [FiniteDimensional (PadicAlgCl l) V] {ρ : Representation (PadicAlgCl l) W.carrier V}
    (hρ : W.IsLisse l ρ) :
    ∃ (F : WeilSheaf K l C) (hF : F.IsLisse),
      (∀ x : C.finitePoints, (F.stalk x).frobeniusEnd.charpoly = (ρ (W.frobenius x)).charpoly) ∧
      ∃ f : (F.geometricCoinvariants hF).carrier ≃ₗ[PadicAlgCl l]
          Representation.Coinvariants (ρ.comp W.geometric.subtype),
        ∀ v, f ((F.geometricCoinvariants hF).frobenius v) =
          ρ.toCoinvariants W.geometric W.frobeniusLift (f v) := by
  obtain ⟨e, hst, hdu, hse, -⟩ := W.exists_equivalence_isLisse l
  let X : ObjectProperty.FullSubcategory (W.isLisseRep l) := ⟨Rep.of ρ, inferInstance, hρ⟩
  set F := e.inverse.obj X
  set ρF := (e.functor.obj F).obj.ρ
  let ψ : (e.functor.obj F).obj.V ≃ₗ[PadicAlgCl l] V :=
    repLinearEquivOfIso ((ObjectProperty.ι _).mapIso (e.counitIso.app X))
  have hψ (g : W.carrier) (v : (e.functor.obj F).obj.V) : ψ (ρF g v) = ρ g (ψ v) :=
    Rep.hom_comm_apply ((ObjectProperty.ι _).mapIso (e.counitIso.app X)).hom g v
  refine ⟨F.obj, F.property, fun x ↦ ?_, ?_⟩
  · obtain ⟨f, hf⟩ := hst F x
    refine LinearMap.charpoly_eq_of_comp_eq (f.trans ψ) (LinearMap.ext fun v ↦ ?_)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, FrobeniusModule.frobeniusEnd_apply,
      LinearEquiv.coe_toLinearMap, LinearEquiv.trans_apply, hf, hψ, LinearEquiv.trans_apply]
  · let Fd : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse) :=
      ⟨F.obj.dual F.property, F.property.dual⟩
    obtain ⟨a, ha⟩ := hse Fd
    obtain ⟨b⟩ := hdu F
    -- Transport the contragredient once, before passing to invariants and coinvariants.
    let dψ : ρF.dual.Equiv ρ.dual :=
      .mk ψ.symm.dualMap fun g ↦ LinearMap.ext fun φ ↦ LinearMap.ext fun v ↦ by
        change φ (ρF g⁻¹ (ψ.symm v)) = φ (ψ.symm (ρ g⁻¹ v))
        congr 1
        apply ψ.injective
        rw [hψ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact FrobeniusModule.exists_linearEquiv_dual_of_invariants ρ (e.functor.obj Fd).obj.ρ
      W.geometric W.frobeniusLift (b.trans dψ) Fd.obj.globalSections a ha

end WeilGroup

end AlgebraicGeometry
