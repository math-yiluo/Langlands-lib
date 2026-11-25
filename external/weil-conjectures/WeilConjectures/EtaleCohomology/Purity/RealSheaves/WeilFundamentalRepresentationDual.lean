/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentation
public import WeilConjectures.WeilSheaf.StalkConstantSheaf

/-!
# The Weil fundamental representation of the dual

For a lisse Weil sheaf `ℱ`, the evaluation pairing `(ℱ^∨)_t × ℱ_t → ℚ̄_ℓ` of the stalks at the
base point is perfect and invariant under the Weil fundamental representations, so the Weil
fundamental representation of the dual `ℱ^∨` is the contragredient of that of `ℱ`
(`AlgebraicGeometry.WeilGroup.nonempty_equiv_fundamentalRep_dual`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal

namespace AlgebraicGeometry.WeilGroup

open ProEtale Scheme.FiniteEtale

section MonoidalTransport

variable {𝒜 ℬ : Type*} [Category* 𝒜] [MonoidalCategory 𝒜] [Category* ℬ] [MonoidalCategory ℬ]
  {L : 𝒜 ⥤ 𝒜} [L.LaxMonoidal] {G₁ G₂ : 𝒜 ⥤ ℬ} [G₁.LaxMonoidal] [G₂.LaxMonoidal]
  (τ : G₁ ⟶ L ⋙ G₂) [NatTrans.IsMonoidal τ]

/-- A pairing `e : P ⊗ Q ⟶ R` compatible with morphisms `L P ⟶ P`, `L Q ⟶ Q`, `L R ⟶ R` is
transported by a monoidal natural transformation `G₁ ⟶ L ⋙ G₂` of lax monoidal functors. -/
lemma pairing_monoidalTransport {P Q R : 𝒜} (φP : L.obj P ⟶ P) (φQ : L.obj Q ⟶ Q)
    (φR : L.obj R ⟶ R) (e : P ⊗ Q ⟶ R) (h : (φP ⊗ₘ φQ) ≫ e = μ L P Q ≫ L.map e ≫ φR) :
    ((τ.app P ≫ G₂.map φP) ⊗ₘ (τ.app Q ≫ G₂.map φQ)) ≫ μ G₂ P Q ≫ G₂.map e =
      (μ G₁ P Q ≫ G₁.map e) ≫ τ.app R ≫ G₂.map φR := by
  rw [← tensorHom_comp_tensorHom_assoc, μ_natural_assoc, ← Functor.map_comp, h,
    Functor.map_comp, Functor.map_comp, ← Category.assoc (μ _ _ _),
    ← Functor.LaxMonoidal.comp_μ, ← Category.assoc, ← Category.assoc,
    ← NatTrans.IsMonoidal.tensor (τ := τ)]
  simp only [Category.assoc]
  rw [← Functor.comp_map, ← NatTrans.naturality_assoc]

end MonoidalTransport

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} [C.Over (Spec (.of K))]
  {l : ℕ} [Fact l.Prime] [Fact (ringChar K ≠ l)]

variable (K l C) in
/-- The isomorphism `G_{y ≫ Fr} ≅ ((Fr⁻¹)_* G)_y` of stalk functors at a geometric point `y` of
the geometric curve, from the composition of pullbacks and `Fr^* ≅ (Fr⁻¹)_*`. -/
noncomputable def stalkFrobTransport
    (y : Spec (.of (AlgebraicClosure K)) ⟶ (C ↘ Spec (.of K)).geometricFiber) :
    stalkFunctor l (y ≫ (C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom) ≅
      ((C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.inv)_*[_] ⋙ stalkFunctor l y :=
  Functor.isoWhiskerRight
    (upperStarComp _ y (C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerRight (upperStarIsoLowerStarInv _
      (C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso) _

/-- The isomorphism `G_{y ≫ Fr} ≅ ((Fr⁻¹)_* G)_y` of stalk functors is monoidal. -/
instance isMonoidal_stalkFrobTransport_hom
    (y : Spec (.of (AlgebraicClosure K)) ⟶ (C ↘ Spec (.of K)).geometricFiber) :
    NatTrans.IsMonoidal (stalkFrobTransport K C l y).hom := by
  dsimp only [stalkFrobTransport, Iso.trans_hom, Functor.isoWhiskerRight_hom]
  infer_instance

omit [Fact (ringChar K ≠ l)] in
/-- The components of `G_{y ≫ Fr} ≅ ((Fr⁻¹)_* G)_y`. -/
lemma stalkFrobTransport_hom_app
    (y : Spec (.of (AlgebraicClosure K)) ⟶ (C ↘ Spec (.of K)).geometricFiber)
    (G : Sheaf (Scheme.ProEt.topology (C ↘ Spec (.of K)).geometricFiber)
      (WeilCoefficients.{u} l)) :
    (stalkFrobTransport K C l y).hom.app G =
      (upperStarStalkIso l (C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom y G).hom ≫
        (stalkFunctor l y).map ((upperStarIsoLowerStarInv _
          (C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso).hom.app G) := by
  simp [stalkFrobTransport, upperStarStalkIso]

section UnitStalk

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] (M : LisseMonodromy l Y Ω)

omit [Finite K] [Fact (ringChar K ≠ l)] in
/-- The transport along a loop acts trivially on the stalk of the constant sheaf `ℚ̄_ℓ`: it
fixes the restriction of the unit global section, which spans this line. -/
lemma mono_hom_app_unit {y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y} (g : fiber y ≅ fiber y) :
    (M.mono g).hom.app (LisseSheaf.unit l) = 𝟙 _ :=
  WeilCoefficients.eq_id_of_finrank_eq_one _
    (finrank_globalSections_upperStar_adicConstantSheaf y) _
    (globalSectionsToUpperStar_oneGlobalSection_ne_zero y)
    (congrArg (fun φ ↦ φ.hom (oneGlobalSection Y)) (M.mono_globalSections g (LisseSheaf.unit l)))

end UnitStalk

variable [IsCurve (C ↘ Spec (.of K))] {W : WeilGroup (C ↘ Spec (.of K))}
  (M : LisseMonodromy l (C ↘ Spec (.of K)).geometricFiber K)
  {B : BasePointData W}

/-- The Frobenius `Φ` of the stalk of a lisse Weil sheaf `F` at the base point is the transport
along `β`, followed by `F_{t ≫ Fr} ≅ ((Fr⁻¹)_* F)_t` and the stalk of the Weil structure. -/
lemma frobStalkIso_hom_eq (F : WeilSheaf K l C) (hF : F.IsLisse) :
    (frobStalkIso M B F hF).hom = (M.mono B.frobPath).hom.app (F.toLisse hF) ≫
      (stalkFrobTransport K C l B.t).hom.app F.obj.carrier.X ≫
        (stalkFunctor l B.t).map F.obj.str.hom.hom := by
  rw [stalkFrobTransport_hom_app]
  simp only [frobStalkIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
  congr 2
  rw [← Functor.map_comp, ← adicUpperStarIsoLowerStarInv_hom_app_hom]
  rfl

omit [Fact (ringChar K ≠ l)] [IsCurve (C ↘ Spec (.of K))] in
/-- The restriction of global sections to the stalk at `t ≫ Fr`, followed by
`G_{t ≫ Fr} ≅ ((Fr⁻¹)_* G)_t` and the stalk of `φ : (Fr⁻¹)_* G ⟶ G`, is the global sections of
`Fr^* G ≅ (Fr⁻¹)_* G ⟶ G` followed by the restriction to the stalk at `t`. -/
lemma globalSectionsToUpperStar_comp_stalkFrobTransport
    (y : Spec (.of (AlgebraicClosure K)) ⟶ (C ↘ Spec (.of K)).geometricFiber)
    {G H : Sheaf (Scheme.ProEt.topology (C ↘ Spec (.of K)).geometricFiber)
      (WeilCoefficients.{u} l)}
    (φ : ((C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.inv)_*[_].obj G ⟶ H) :
    (globalSectionsToUpperStar _
        (y ≫ (C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom)).app G ≫
        (stalkFrobTransport K C l y).hom.app G ≫ (stalkFunctor l y).map φ =
      (globalSectionsToUpperStar _ (C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom).app G ≫
        (Sheaf.Γ _ _).map ((upperStarIsoLowerStarInv _
          (C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso).hom.app G ≫ φ) ≫
        (globalSectionsToUpperStar _ y).app H := by
  rw [stalkFrobTransport_hom_app, (globalSectionsToUpperStar _ y).naturality]
  have h := globalSectionsToUpperStar_comp (WeilCoefficients.{u} l) y
    (C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom G
  simp only [upperStarStalkIso, Functor.mapIso_hom, Iso.app_hom, Category.assoc,
    Functor.comp_map] at h ⊢
  rw [reassoc_of% h, Functor.map_comp, Functor.map_comp]

/-- The Frobenius of the stalk of the constant sheaf `ℚ̄_ℓ` at the base point is the identity:
it fixes the restriction of the unit global section, which spans this line. -/
lemma mono_comp_stalkFrobTransport_unit :
    (M.mono B.frobPath).hom.app (LisseSheaf.unit l) ≫
        (stalkFrobTransport K C l B.t).hom.app
          (WeilSheaf.adicConstant K l C).obj.carrier.X ≫
        (stalkFunctor l B.t).map (WeilSheaf.adicConstant K l C).obj.str.hom.hom = 𝟙 _ := by
  refine WeilCoefficients.eq_id_of_finrank_eq_one _
    (finrank_globalSections_upperStar_adicConstantSheaf B.t) _
    (globalSectionsToUpperStar_oneGlobalSection_ne_zero B.t) ?_
  have h₁ := M.mono_globalSections B.frobPath (LisseSheaf.unit l)
  have h₂ := globalSectionsToUpperStar_comp_stalkFrobTransport B.t
    (WeilSheaf.adicConstant K l C).obj.str.hom.hom
  have h₃ : (globalSectionsToUpperStar _ B.t).app
      (WeilSheaf.adicConstant K l C).obj.carrier.X ≫
      (M.mono B.frobPath).hom.app (LisseSheaf.unit l) ≫
        (stalkFrobTransport K C l B.t).hom.app
          (WeilSheaf.adicConstant K l C).obj.carrier.X ≫
        (stalkFunctor l B.t).map (WeilSheaf.adicConstant K l C).obj.str.hom.hom =
      (globalSectionsToUpperStar _ (C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom).app _ ≫
        (Sheaf.Γ _ _).map (WeilSheaf.frobeniusStr (WeilSheaf.adicConstant K l C)) ≫
        (globalSectionsToUpperStar _ B.t).app _ := by
    rw [← Category.assoc]
    erw [h₁]
    exact h₂
  have h₄ := congrArg (fun φ ↦ φ.hom (oneGlobalSection _)) h₃
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h₄
  refine h₄.trans (congrArg _ ?_)
  rw [WeilSheaf.frobeniusStr_adicConstant]
  exact Γ_map_adicUpperStarUnitIso_globalSectionsToUpperStar_oneGlobalSection _

/-- The evaluation pairing `(F^∨)_t × F_t → (ℚ̄_ℓ)_t` of the stalks at the base point is invariant
under the Frobenius `Φ` of the Weil fundamental representations: the transport along `β`
preserves it (`AlgebraicGeometry.ProEtale.LisseMonodromy.mono_evaluationPairing`), so do the
monoidal identification `G_{t ≫ Fr} ≅ ((Fr⁻¹)_* G)_t` and the Weil structures
(`AlgebraicGeometry.WeilSheaf.dual_evaluation_str`), and `Φ` is the identity on `(ℚ̄_ℓ)_t`. -/
lemma evaluationPairing_frobStalkIso (F : WeilSheaf K l C) (hF : F.IsLisse)
    (d : (stalkFunctor l B.t).obj ((AdicSheaf.ihom F.obj.carrier).obj (AdicSheaf.unit l _)).X)
    (v : (stalkFunctor l B.t).obj F.obj.carrier.X) :
    Mod.evaluationPairing (stalkFunctor l B.t) F.obj.carrier (AdicSheaf.unit l _)
        ((frobStalkIso M B (F.dual hF) hF.dual).hom.hom d) ((frobStalkIso M B F hF).hom.hom v) =
      Mod.evaluationPairing (stalkFunctor l B.t) F.obj.carrier (AdicSheaf.unit l _) d v := by
  have h := pairing_monoidalTransport (stalkFrobTransport K C l B.t).hom
    (F.dual hF).obj.str.hom.hom F.obj.str.hom.hom (WeilSheaf.adicConstant K l C).obj.str.hom.hom
    (Mod.evaluation F.obj.carrier (WeilSheaf.adicConstant K l C).obj.carrier)
    (WeilSheaf.dual_evaluation_str F hF)
  have h' := congrArg (fun f ↦ f.hom (((M.mono B.frobPath).hom.app ⟨_, hF.dual⟩).hom d ⊗ₜ
    ((M.mono B.frobPath).hom.app (F.toLisse hF)).hom v)) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul] at h'
  have e := M.mono_evaluationPairing B.frobPath (F.toLisse hF) (LisseSheaf.unit l) hF.dual d v
  rw [Mod.evaluationPairing_apply, Mod.evaluationPairing_apply] at e
  have u := congrArg (fun f ↦ f.hom (Mod.evaluationPairing (stalkFunctor l B.t) F.obj.carrier
    (AdicSheaf.unit l _) d v)) (mono_comp_stalkFrobTransport_unit M (B := B))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at u
  rw [Mod.evaluationPairing_apply] at u ⊢
  rw [Mod.evaluationPairing_apply, frobStalkIso_hom_eq, frobStalkIso_hom_eq]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  refine h'.trans ?_
  erw [e]
  exact u

omit [Finite K] [Fact (ringChar K ≠ l)] [IsCurve (C ↘ Spec (.of K))] in
/-- A linear map `S : V → V'^*` such that the pairing `(d, v) ↦ S d v` is invariant under `g`
intertwines `ρ g` with the contragredient `ρ'^∨ g`. -/
lemma apply_eq_dual_of_invariant {G V V' : Type*} [Group G] [AddCommGroup V]
    [Module (PadicAlgCl l) V] [AddCommGroup V'] [Module (PadicAlgCl l) V']
    (ρ : Representation (PadicAlgCl l) G V) (ρ' : Representation (PadicAlgCl l) G V')
    (S : V →ₗ[PadicAlgCl l] Module.Dual (PadicAlgCl l) V') (g : G)
    (h : ∀ d v, S (ρ g d) (ρ' g v) = S d v) (d : V) : S (ρ g d) = ρ'.dual g (S d) := by
  ext v
  rw [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply]
  conv_lhs => rw [← show ρ' g (ρ' g⁻¹ v) = v by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]]
  exact h _ _

variable (B) in
/-- The linear map `(F^∨)_t → (F_t)^*` induced by the evaluation pairing of the stalks at the base
point, `ℚ̄_ℓ`-valued through the unit section `ℚ̄_ℓ ≅ (ℚ̄_ℓ)_t`. -/
noncomputable def dualStalkLinearMap (F : WeilSheaf K l C) (hF : F.IsLisse) :
    LisseMonodromy.StalkSpace B.t ((F.dual hF).toLisse hF.dual) →ₗ[PadicAlgCl l]
      Module.Dual (PadicAlgCl l) (LisseMonodromy.StalkSpace B.t (F.toLisse hF)) :=
  WeilCoefficients.dualLinearMap
    (Mod.evaluationPairing (stalkFunctor l B.t) F.obj.carrier (AdicSheaf.unit l _))
    (asIso (unitSection l B.t)).symm.toLinearEquiv.toLinearMap

/-- The map `(F^∨)_t → (F_t)^*` induced by the evaluation pairing is bijective
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.bijective_evaluationPairing`). -/
lemma bijective_dualStalkLinearMap (F : WeilSheaf K l C) (hF : F.IsLisse) :
    Function.Bijective (dualStalkLinearMap B F hF) :=
  WeilCoefficients.bijective_dualLinearMap (IsAdicLisseSheaf.bijective_evaluationPairing hF B.t)
    (asIso (unitSection l B.t)).symm.toLinearEquiv

/-- The evaluation pairing of the stalks at the base point is invariant under the geometric
fundamental representations: transport along a loop preserves it and is trivial on `(ℚ̄_ℓ)_t`. -/
lemma dualStalkLinearMap_rep (F : WeilSheaf K l C) (hF : F.IsLisse) (g : Aut (fiber B.t))
    (d : LisseMonodromy.StalkSpace B.t ((F.dual hF).toLisse hF.dual))
    (v : LisseMonodromy.StalkSpace B.t (F.toLisse hF)) :
    dualStalkLinearMap B F hF (M.rep B.t _ g d) (M.rep B.t _ g v) =
      dualStalkLinearMap B F hF d v := by
  simp only [dualStalkLinearMap, WeilCoefficients.dualLinearMap_apply]
  change ((asIso (unitSection l B.t)).symm.toLinearEquiv
      (Mod.evaluationPairing (stalkFunctor l B.t) F.obj.carrier (AdicSheaf.unit l _)
        (((M.mono g.asIso).hom.app ⟨_, hF.dual⟩).hom d)
        (((M.mono g.asIso).hom.app (F.toLisse hF)).hom v))).down = _
  have e := M.mono_evaluationPairing g.asIso (F.toLisse hF) (LisseSheaf.unit l) hF.dual d v
  rw [mono_hom_app_unit] at e
  exact congrArg (fun x ↦ ((asIso (unitSection l B.t)).symm.toLinearEquiv x).down) e

/-- The evaluation pairing of the stalks at the base point is invariant under the Frobenius `Φ`. -/
lemma dualStalkLinearMap_frobStalk (F : WeilSheaf K l C) (hF : F.IsLisse)
    (d : LisseMonodromy.StalkSpace B.t ((F.dual hF).toLisse hF.dual))
    (v : LisseMonodromy.StalkSpace B.t (F.toLisse hF)) :
    dualStalkLinearMap B F hF (frobStalk M B _ hF.dual d) (frobStalk M B F hF v) =
      dualStalkLinearMap B F hF d v := by
  simp only [dualStalkLinearMap, WeilCoefficients.dualLinearMap_apply]
  change ((asIso (unitSection l B.t)).symm.toLinearEquiv
      (Mod.evaluationPairing (stalkFunctor l B.t) F.obj.carrier (AdicSheaf.unit l _)
        ((frobStalkIso M B (F.dual hF) hF.dual).hom.hom d)
        ((frobStalkIso M B F hF).hom.hom v))).down = _
  rw [evaluationPairing_frobStalkIso]
  rfl

variable {M} (D : WeilMonodromyData B)

variable (M) in
/-- The Weil fundamental representation of the dual `ℱ^∨` is the contragredient of that of `ℱ`,
through the evaluation pairing of the stalks at the base point. -/
noncomputable def fundamentalRepDualEquiv (F : WeilSheaf K l C) (hF : F.IsLisse) :
    (fundamentalRep M D (F.dual hF) hF.dual).Equiv (fundamentalRep M D F hF).dual :=
  Representation.Equiv.mk (LinearEquiv.ofBijective _ (bijective_dualStalkLinearMap F hF))
    fun w ↦ LinearMap.ext fun d ↦ by
      change dualStalkLinearMap B F hF (fundamentalRep M D _ _ w d) =
        (fundamentalRep M D F hF).dual w (dualStalkLinearMap B F hF d)
      refine intertwines_of_geometric_frobLift D _ _ (dualStalkLinearMap B F hF)
        (fun u hu d ↦ ?_) (fun d ↦ ?_) w d
      · refine apply_eq_dual_of_invariant _ _ _ _ (fun d v ↦ ?_) d
        rw [fundamentalRep_geometric M D _ _ ⟨u, hu⟩, fundamentalRep_geometric M D F hF ⟨u, hu⟩]
        exact dualStalkLinearMap_rep M F hF _ d v
      · refine apply_eq_dual_of_invariant _ _ _ _ (fun d v ↦ ?_) d
        rw [fundamentalRep_frobLift, fundamentalRep_frobLift]
        exact dualStalkLinearMap_frobStalk M F hF d v

variable (M) in
lemma fundamentalRepDualEquiv_apply (F : WeilSheaf K l C) (hF : F.IsLisse) (d) :
    fundamentalRepDualEquiv M D F hF d = dualStalkLinearMap B F hF d :=
  rfl

/-- **The Weil fundamental representation of the dual is the contragredient**: the evaluation
pairing of the stalks at the base point identifies the Weil fundamental representation of the
dual `ℱ^∨` of a lisse Weil sheaf with the dual of that of `ℱ`
(`AlgebraicGeometry.WeilGroup.fundamentalRepDualEquiv`). -/
theorem nonempty_equiv_fundamentalRep_dual (F : WeilSheaf K l C) (hF : F.IsLisse) :
    Nonempty ((fundamentalRep M D (F.dual hF) hF.dual).Equiv (fundamentalRep M D F hF).dual) :=
  ⟨fundamentalRepDualEquiv M D F hF⟩

end AlgebraicGeometry.WeilGroup
