/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationDual
public import WeilConjectures.Mathlib.RepresentationTheory.Intertwining
public import WeilConjectures.WeilSheaf.StalkTensor
public import WeilConjectures.WeilSheaf.StalkTensorTrace

/-!
# The Weil fundamental representation of a tensor product

For lisse Weil sheaves `ℱ` and `𝒢`, the tensor product `ℱ ⊗ 𝒢 = [ℱ^∨, 𝒢]` is lisse, and the
evaluation pairing `(ℱ ⊗ 𝒢)_t × (ℱ^∨)_t → 𝒢_t` of the stalks at the base point identifies
`(ℱ ⊗ 𝒢)_t` with `Hom((ℱ^∨)_t, 𝒢_t)`, equivariantly for the Weil fundamental representations.
Since the Weil fundamental representation of `ℱ^∨` is the contragredient of that of `ℱ`, the
Weil fundamental representation of `ℱ ⊗ 𝒢` is the tensor product of those of `ℱ` and `𝒢`
(`AlgebraicGeometry.WeilGroup.nonempty_equiv_fundamentalRep_tensorObj`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal

namespace AlgebraicGeometry

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} [C.Over (Spec (.of K))]
  {l : ℕ} [Fact l.Prime] [Fact (ringChar K ≠ l)]

namespace WeilGroup

open ProEtale Scheme.FiniteEtale

variable [IsCurve (C ↘ Spec (.of K))] {W : WeilGroup (C ↘ Spec (.of K))}
  (M : LisseMonodromy l (C ↘ Spec (.of K)).geometricFiber K)
  {B : BasePointData W}

/-- The evaluation pairing `(ℱ ⊗ 𝒢)_t × (ℱ^∨)_t → 𝒢_t` of the stalks at the base point
intertwines the Frobenius `Φ` of the Weil fundamental representations: the transport along `β`
preserves it (`AlgebraicGeometry.ProEtale.LisseMonodromy.mono_evaluationPairing`), and so do the
monoidal identification `G_{t ≫ Fr} ≅ ((Fr⁻¹)_* G)_t` and the Weil structures
(`AlgebraicGeometry.ProEtaleWeilSheaf.ihom_evaluation_str`). -/
lemma evaluationPairing_frobStalkIso_tensorObj (F G : WeilSheaf K l C) (hF : F.IsLisse)
    (hG : G.IsLisse)
    (d : (stalkFunctor l B.t).obj ((AdicSheaf.ihom (F.dual hF).obj.carrier).obj G.obj.carrier).X)
    (v : (stalkFunctor l B.t).obj (F.dual hF).obj.carrier.X) :
    Mod.evaluationPairing (stalkFunctor l B.t) (F.dual hF).obj.carrier G.obj.carrier
        ((frobStalkIso M B (F.tensorObj G hF) (hF.tensorObj hG)).hom.hom d)
        ((frobStalkIso M B (F.dual hF) hF.dual).hom.hom v) =
      (frobStalkIso M B G hG).hom.hom
        (Mod.evaluationPairing (stalkFunctor l B.t) (F.dual hF).obj.carrier G.obj.carrier d v) := by
  have h := pairing_monoidalTransport (stalkFrobTransport K C l B.t).hom
    (F.tensorObj G hF).obj.str.hom.hom (F.dual hF).obj.str.hom.hom G.obj.str.hom.hom
    (Mod.evaluation (F.dual hF).obj.carrier G.obj.carrier)
    (ProEtaleWeilSheaf.ihom_evaluation_str (F.dual hF).obj G.obj)
  have h' := congrArg (fun f ↦ f.hom
    (((M.mono B.frobPath).hom.app ⟨_, hF.tensorObj hG⟩).hom d ⊗ₜ
      ((M.mono B.frobPath).hom.app ((F.dual hF).toLisse hF.dual)).hom v)) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul] at h'
  have e := M.mono_evaluationPairing B.frobPath ((F.dual hF).toLisse hF.dual) (G.toLisse hG)
    (hF.tensorObj hG) d v
  rw [Mod.evaluationPairing_apply, Mod.evaluationPairing_apply] at e
  rw [Mod.evaluationPairing_apply, Mod.evaluationPairing_apply, frobStalkIso_hom_eq,
    frobStalkIso_hom_eq, frobStalkIso_hom_eq]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  refine h'.trans ?_
  erw [e]
  rfl

variable (B) in
/-- The linear map `(ℱ ⊗ 𝒢)_t → Hom((ℱ^∨)_t, 𝒢_t)` induced by the evaluation pairing of the
stalks at the base point. -/
noncomputable def tensorStalkLinearMap (F G : WeilSheaf K l C) (hF : F.IsLisse)
    (hG : G.IsLisse) :
    LisseMonodromy.StalkSpace B.t ((F.tensorObj G hF).toLisse (hF.tensorObj hG)) →ₗ[PadicAlgCl l]
      (LisseMonodromy.StalkSpace B.t ((F.dual hF).toLisse hF.dual) →ₗ[PadicAlgCl l]
        LisseMonodromy.StalkSpace B.t (G.toLisse hG)) :=
  WeilCoefficients.homLinearMap
    (Mod.evaluationPairing (stalkFunctor l B.t) (F.dual hF).obj.carrier G.obj.carrier)

lemma tensorStalkLinearMap_apply (F G : WeilSheaf K l C) (hF : F.IsLisse) (hG : G.IsLisse) (d v) :
    tensorStalkLinearMap B F G hF hG d v =
      Mod.evaluationPairing (stalkFunctor l B.t) (F.dual hF).obj.carrier G.obj.carrier d v :=
  rfl

/-- The map `(ℱ ⊗ 𝒢)_t → Hom((ℱ^∨)_t, 𝒢_t)` is bijective, `ℱ^∨` being lisse
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.bijective_evaluationPairing_of_lisse`). -/
lemma bijective_tensorStalkLinearMap (F G : WeilSheaf K l C) (hF : F.IsLisse) (hG : G.IsLisse) :
    Function.Bijective (tensorStalkLinearMap B F G hF hG) :=
  WeilCoefficients.bijective_homLinearMap
    (IsAdicLisseSheaf.bijective_evaluationPairing_of_lisse hF.dual _ B.t)

/-- The evaluation pairing of the stalks at the base point is equivariant for the geometric
fundamental representations: transport along a loop preserves it. -/
lemma tensorStalkLinearMap_rep (F G : WeilSheaf K l C) (hF : F.IsLisse) (hG : G.IsLisse)
    (g : Aut (fiber B.t)) (d v) :
    tensorStalkLinearMap B F G hF hG (M.rep B.t _ g d) (M.rep B.t _ g v) =
      M.rep B.t (G.toLisse hG) g (tensorStalkLinearMap B F G hF hG d v) :=
  M.mono_evaluationPairing g.asIso ((F.dual hF).toLisse hF.dual) (G.toLisse hG)
    (hF.tensorObj hG) d v

/-- The evaluation pairing of the stalks at the base point is equivariant for the Frobenius
`Φ`. -/
lemma tensorStalkLinearMap_frobStalk (F G : WeilSheaf K l C) (hF : F.IsLisse) (hG : G.IsLisse)
    (d v) :
    tensorStalkLinearMap B F G hF hG (frobStalk M B _ (hF.tensorObj hG) d)
        (frobStalk M B _ hF.dual v) =
      frobStalk M B G hG (tensorStalkLinearMap B F G hF hG d v) :=
  evaluationPairing_frobStalkIso_tensorObj M F G hF hG d v

omit [Finite K] [Fact (ringChar K ≠ l)] [IsCurve (C ↘ Spec (.of K))] in
/-- A linear map `S : V → Hom(V', W')` such that `S (ρ g d) (ρ' g v) = σ g (S d v)` intertwines
`ρ g` with `linHom ρ' σ g`. -/
lemma apply_eq_linHom_of_equivariant {G V V' W' : Type*} [Group G] [AddCommGroup V]
    [Module (PadicAlgCl l) V] [AddCommGroup V'] [Module (PadicAlgCl l) V'] [AddCommGroup W']
    [Module (PadicAlgCl l) W'] (ρ : Representation (PadicAlgCl l) G V)
    (ρ' : Representation (PadicAlgCl l) G V') (σ : Representation (PadicAlgCl l) G W')
    (S : V →ₗ[PadicAlgCl l] V' →ₗ[PadicAlgCl l] W') (g : G)
    (h : ∀ d v, S (ρ g d) (ρ' g v) = σ g (S d v)) (d : V) :
    S (ρ g d) = Representation.linHom ρ' σ g (S d) := by
  ext v
  rw [Representation.linHom_apply, LinearMap.comp_apply, LinearMap.comp_apply, ← h]
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

variable {M} (D : WeilMonodromyData B)

variable (M) in
/-- The Weil fundamental representation of `ℱ ⊗ 𝒢` is the representation on
`Hom((ℱ^∨)_t, 𝒢_t)`, through the evaluation pairing of the stalks at the base point. -/
noncomputable def fundamentalRepTensorObjLinHomEquiv (F G : WeilSheaf K l C) (hF : F.IsLisse)
    (hG : G.IsLisse) :
    (fundamentalRep M D (F.tensorObj G hF) (hF.tensorObj hG)).Equiv
      (Representation.linHom (fundamentalRep M D (F.dual hF) hF.dual)
        (fundamentalRep M D G hG)) :=
  Representation.Equiv.mk
    (LinearEquiv.ofBijective _ (bijective_tensorStalkLinearMap F G hF hG))
    fun w ↦ LinearMap.ext fun d ↦ by
      change tensorStalkLinearMap B F G hF hG (fundamentalRep M D _ _ w d) =
        Representation.linHom _ _ w (tensorStalkLinearMap B F G hF hG d)
      refine intertwines_of_geometric_frobLift D _ _ (tensorStalkLinearMap B F G hF hG)
        (fun u hu d ↦ ?_) (fun d ↦ ?_) w d
      · refine apply_eq_linHom_of_equivariant _ _ _ _ _ (fun d v ↦ ?_) d
        rw [fundamentalRep_geometric M D _ _ ⟨u, hu⟩, fundamentalRep_geometric M D _ _ ⟨u, hu⟩,
          fundamentalRep_geometric M D G hG ⟨u, hu⟩]
        exact tensorStalkLinearMap_rep M F G hF hG _ d v
      · refine apply_eq_linHom_of_equivariant _ _ _ _ _ (fun d v ↦ ?_) d
        rw [fundamentalRep_frobLift, fundamentalRep_frobLift, fundamentalRep_frobLift]
        exact tensorStalkLinearMap_frobStalk M F G hF hG d v

variable (M) in
lemma fundamentalRepTensorObjLinHomEquiv_apply (F G : WeilSheaf K l C) (hF : F.IsLisse)
    (hG : G.IsLisse) (z) :
    fundamentalRepTensorObjLinHomEquiv M D F G hF hG z = tensorStalkLinearMap B F G hF hG z :=
  rfl

/-- The Weil fundamental representation of `ℱ ⊗ 𝒢` is the representation on
`Hom((ℱ^∨)_t, 𝒢_t)` induced by those of `ℱ^∨` and `𝒢`
(`AlgebraicGeometry.WeilGroup.fundamentalRepTensorObjLinHomEquiv`). -/
theorem nonempty_equiv_fundamentalRep_tensorObj_linHom (F G : WeilSheaf K l C) (hF : F.IsLisse)
    (hG : G.IsLisse) :
    Nonempty ((fundamentalRep M D (F.tensorObj G hF) (hF.tensorObj hG)).Equiv
      (Representation.linHom (fundamentalRep M D (F.dual hF) hF.dual)
        (fundamentalRep M D G hG))) :=
  ⟨fundamentalRepTensorObjLinHomEquiv M D F G hF hG⟩

variable (M) in
/-- The identification `(ℱ ⊗ 𝒢)_t ≅ ℱ_t ⊗ 𝒢_t` of Weil fundamental representations: the
composite of `(ℱ ⊗ 𝒢)_t ≅ Hom((ℱ^∨)_t, 𝒢_t)` and `ℱ_t ⊗ 𝒢_t ≅ Hom((ℱ^∨)_t, 𝒢_t)`,
`(ℱ^∨)_t ≅ (ℱ_t)^∨`. -/
noncomputable def fundamentalRepTensorObjEquiv (F G : WeilSheaf K l C) (hF : F.IsLisse)
    (hG : G.IsLisse) :
    (fundamentalRep M D (F.tensorObj G hF) (hF.tensorObj hG)).Equiv
      ((fundamentalRep M D F hF).tprod (fundamentalRep M D G hG)) :=
  haveI : FiniteDimensional (PadicAlgCl l) (LisseMonodromy.StalkSpace B.t (F.toLisse hF)) :=
    F.finiteDimensional_stalkObj B.t
  (fundamentalRepTensorObjLinHomEquiv M D F G hF hG).trans
    (Representation.Equiv.tprodEquivLinHomOfDual (fundamentalRepDualEquiv M D F hF)).symm

/-- **The Weil fundamental representation of a tensor product is the tensor product**: for lisse
Weil sheaves `ℱ` and `𝒢`, the Weil fundamental representation of `ℱ ⊗ 𝒢` is the tensor product
of those of `ℱ` and `𝒢` (`AlgebraicGeometry.WeilGroup.fundamentalRepTensorObjEquiv`). -/
theorem nonempty_equiv_fundamentalRep_tensorObj (F G : WeilSheaf K l C) (hF : F.IsLisse)
    (hG : G.IsLisse) :
    Nonempty ((fundamentalRep M D (F.tensorObj G hF) (hF.tensorObj hG)).Equiv
      ((fundamentalRep M D F hF).tprod (fundamentalRep M D G hG))) :=
  ⟨fundamentalRepTensorObjEquiv M D F G hF hG⟩

end WeilGroup

end AlgebraicGeometry
