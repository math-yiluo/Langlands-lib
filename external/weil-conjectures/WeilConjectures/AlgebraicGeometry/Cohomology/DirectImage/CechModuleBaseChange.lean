/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.FlatComplexBaseChange
public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.CechBaseChange
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechModule
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackSections
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.GlobalSections
public import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap

/-!
# Base change of the Čech complex over an affine base

Consider a cartesian square of schemes with affine bases
```
Y --g'--> X
|         |
f'        f
v         v
T --g---> S
```
and write `A = Γ(S, ⊤)`, `B = Γ(T, ⊤)`. For a quasi-coherent `𝒪_X`-module `ℱ` and an affine
open `W` of `X`, the map `B ⊗[A] Γ(ℱ, W) ⟶ Γ(g'^* ℱ, g'⁻¹ W)`, `b ⊗ m ↦ b • g'^* m`, is bijective
(`AlgebraicGeometry.Scheme.Modules.bijective_sectionsBaseChange`): it is the composite of the
identification `Γ(g'^* ℱ, g'⁻¹ W) = Γ(Y, g'⁻¹ W) ⊗[Γ(X, W)] Γ(ℱ, W)` and of the pushout
`Γ(Y, g'⁻¹ W) = Γ(X, W) ⊗[A] B` of rings.

Consequently, for a family `U` of opens of `X` whose finite intersections are affine, the Čech
complex of `g'^* ℱ` for `g'⁻¹ U` is the base change `B ⊗[A] Č(U, ℱ)` of the Čech complex of `ℱ`
(`AlgebraicGeometry.Scheme.Modules.cechModuleComplexBaseChangeIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y S T : Scheme.{u}} {f : X ⟶ S} {f' : Y ⟶ T} {g : T ⟶ S} {g' : Y ⟶ X}
  (H : IsPullback g' f' f g) (ℱ : X.Modules)
  [Algebra Γ(S, ⊤) Γ(T, ⊤)] (hg : algebraMap Γ(S, ⊤) Γ(T, ⊤) = g.appTop.hom)

include H hg in
/-- The functions on the base act compatibly on the sections of `ℱ` and of `g'^* ℱ`. -/
lemma pullbackSection_smul_appTop {W : X.Opens} (a : Γ(S, ⊤)) (m : Γ(ℱ, W)) :
    pullbackSection g' (X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (f.appTop a) • m) =
      Y.presheaf.map (homOfLE (le_top : g' ⁻¹ᵁ W ≤ ⊤)).op (f'.appTop (algebraMap _ _ a)) •
        pullbackSection g' m := by
  rw [pullbackSection_smul, hg]
  congr 1
  have h₁ : X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (f.appTop a) =
      f.appLE ⊤ W (by simp) a := rfl
  have h₂ : Y.presheaf.map (homOfLE (le_top : g' ⁻¹ᵁ W ≤ ⊤)).op (f'.appTop (g.appTop a)) =
      f'.appLE ⊤ (g' ⁻¹ᵁ W) (by simp) (g.appLE ⊤ ⊤ (by simp) a) := by
    rw [Scheme.Hom.appLE_top_top_eq_appTop]
    rfl
  rw [h₁, h₂]
  exact (appLE_comp_eq_app_appLE H.w (V := ⊤) (by simp) (W := W) (by simp) a).symm

/-- The pullback of sections `Γ(ℱ, W) ⟶ Γ(g'^* ℱ, g'⁻¹ W)`, as an additive map between the
modules of sections over the bases. -/
noncomputable def pullbackSectionAddHom (W : X.Opens) :
    sectionsModule f ℱ W →+ sectionsModule f' ((pullback g').obj ℱ) (g' ⁻¹ᵁ W) where
  toFun m := pullbackSection (M := ℱ) (U := W) g' m
  map_zero' := map_zero (((pullbackPushforwardAdjunction g').unit.app ℱ).app W).hom
  map_add' m m' := pullbackSection_add g' (M := ℱ) (U := W) m m'

omit [Algebra Γ(S, ⊤) Γ(T, ⊤)] in
lemma pullbackSectionAddHom_apply (W : X.Opens) (m : sectionsModule f ℱ W) :
    pullbackSectionAddHom (f := f) (f' := f') (g' := g') ℱ W m =
      pullbackSection (M := ℱ) (U := W) g' m :=
  rfl

include H hg in
lemma pullbackSectionAddHom_smul (W : X.Opens) (a : Γ(S, ⊤)) (m : sectionsModule f ℱ W) :
    pullbackSectionAddHom (f := f) (f' := f') (g' := g') ℱ W (a • m) =
      algebraMap Γ(S, ⊤) Γ(T, ⊤) a • pullbackSectionAddHom (f := f) (f' := f') (g' := g') ℱ W m :=
  pullbackSection_smul_appTop H ℱ hg (W := W) a m

/-- The additive map underlying `AlgebraicGeometry.Scheme.Modules.sectionsModuleBaseChange`. -/
noncomputable def sectionsModuleBaseChangeAddHom (H : IsPullback g' f' f g) (ℱ : X.Modules)
    (hg : algebraMap Γ(S, ⊤) Γ(T, ⊤) = g.appTop.hom) (W : X.Opens) :
    Γ(T, ⊤) ⊗[Γ(S, ⊤)] sectionsModule f ℱ W →+
      sectionsModule f' ((pullback g').obj ℱ) (g' ⁻¹ᵁ W) :=
  TensorProduct.liftAddHom (R := Γ(S, ⊤)) (M := Γ(T, ⊤)) (N := sectionsModule f ℱ W)
    (P := sectionsModule f' ((pullback g').obj ℱ) (g' ⁻¹ᵁ W))
    { toFun b := (DistribSMul.toAddMonoidHom _ b).comp
        (pullbackSectionAddHom (f := f) (f' := f') (g' := g') ℱ W)
      map_zero' := AddMonoidHom.ext fun m ↦ zero_smul Γ(T, ⊤)
        (pullbackSectionAddHom (f := f) (f' := f') (g' := g') ℱ W m)
      map_add' b b' := AddMonoidHom.ext fun m ↦ add_smul b b'
        (pullbackSectionAddHom (f := f) (f' := f') (g' := g') ℱ W m) }
    (fun a b m ↦ by
      change (a • b) • pullbackSectionAddHom (f := f) (f' := f') (g' := g') ℱ W m =
        b • pullbackSectionAddHom (f := f) (f' := f') (g' := g') ℱ W (a • m)
      rw [pullbackSectionAddHom_smul H ℱ hg, smul_smul, Algebra.smul_def, mul_comm])

lemma sectionsModuleBaseChangeAddHom_tmul (W : X.Opens) (b : Γ(T, ⊤))
    (m : sectionsModule f ℱ W) :
    sectionsModuleBaseChangeAddHom H ℱ hg W (b ⊗ₜ m) =
      b • pullbackSectionAddHom (f := f) (f' := f') (g' := g') ℱ W m :=
  TensorProduct.liftAddHom_tmul (R := Γ(S, ⊤)) (M := Γ(T, ⊤)) (N := sectionsModule f ℱ W)
    (P := sectionsModule f' ((pullback g').obj ℱ) (g' ⁻¹ᵁ W)) _ _ _ _

/-- **Base change of sections.** The map `B ⊗[A] Γ(ℱ, W) ⟶ Γ(g'^* ℱ, g'⁻¹ W)`,
`b ⊗ m ↦ b • g'^* m`, for `A = Γ(S, ⊤)` and `B = Γ(T, ⊤)`. -/
noncomputable def sectionsModuleBaseChange (H : IsPullback g' f' f g) (ℱ : X.Modules)
    (hg : algebraMap Γ(S, ⊤) Γ(T, ⊤) = g.appTop.hom) (W : X.Opens) :
    Γ(T, ⊤) ⊗[Γ(S, ⊤)] sectionsModule f ℱ W →ₗ[Γ(T, ⊤)]
      sectionsModule f' ((pullback g').obj ℱ) (g' ⁻¹ᵁ W) where
  toAddHom := (sectionsModuleBaseChangeAddHom H ℱ hg W).toAddHom
  map_smul' c x := by
    change sectionsModuleBaseChangeAddHom H ℱ hg W (c • x) =
      c • sectionsModuleBaseChangeAddHom H ℱ hg W x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
    | tmul b m =>
      rw [TensorProduct.smul_tmul', sectionsModuleBaseChangeAddHom_tmul,
        sectionsModuleBaseChangeAddHom_tmul, smul_eq_mul, mul_smul]

lemma sectionsModuleBaseChange_tmul (W : X.Opens) (b : Γ(T, ⊤)) (m : sectionsModule f ℱ W) :
    sectionsModuleBaseChange H ℱ hg W (b ⊗ₜ m) =
      b • pullbackSectionAddHom (f := f) (f' := f') (g' := g') ℱ W m :=
  sectionsModuleBaseChangeAddHom_tmul H ℱ hg W b m

/-- **Base change of sections over an affine open.** If `S` and `T` are affine, `ℱ` is
quasi-coherent and `W` is an affine open of `X`, the map `B ⊗[A] Γ(ℱ, W) ⟶ Γ(g'^* ℱ, g'⁻¹ W)` is
bijective: it is the composite
`B ⊗[A] Γ(ℱ, W) ≅ Γ(ℱ, W) ⊗[Γ(X, W)] (Γ(X, W) ⊗[A] B) ≅ Γ(ℱ, W) ⊗[Γ(X, W)] Γ(Y, g'⁻¹ W)
≅ Γ(g'^* ℱ, g'⁻¹ W)`, using that `g'⁻¹ W = W ×_S T` is affine with ring of functions
`Γ(X, W) ⊗[A] B`. -/
theorem bijective_sectionsModuleBaseChange [IsAffine S] [IsAffine T]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] {W : X.Opens} (hW : IsAffineOpen W) :
    Function.Bijective (sectionsModuleBaseChange H ℱ hg W) := by
  have hW' : IsAffineOpen (g' ⁻¹ᵁ W) :=
    isAffineOpen_preimage_of_isPullback H (isAffineOpen_top S) (by simp) (by simp) hW
  let : Algebra Γ(S, ⊤) Γ(X, W) := (f.appLE ⊤ W (by simp)).hom.toAlgebra
  let : Algebra Γ(X, W) Γ(Y, g' ⁻¹ᵁ W) := (g'.appLE W (g' ⁻¹ᵁ W) le_rfl).hom.toAlgebra
  let : Module Γ(X, W) (sectionsModule f ℱ W) := inferInstanceAs (Module Γ(X, W) Γ(ℱ, W))
  have : IsScalarTower Γ(S, ⊤) Γ(X, W) (sectionsModule f ℱ W) := ⟨fun a r m ↦ by
    change (f.appLE ⊤ W _ a * r) • (m : Γ(ℱ, W)) =
      X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (f.appTop a) • r • (m : Γ(ℱ, W))
    rw [mul_smul]
    rfl⟩
  -- the sections of the pullback
  obtain ⟨e₁, he₁⟩ := exists_linearEquiv_pullback_sections g' ℱ hW hW' le_rfl
  -- the ring of functions of `g'⁻¹ W = W ×_S T`
  have hUY : g' ⁻¹ᵁ W = g' ⁻¹ᵁ W ⊓ f' ⁻¹ᵁ ⊤ := by simp
  have hpush := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (by simp) (by simp) hUY).mp
    (isIso_pushoutSection_of_isAffineOpen H _ _ hUY (isAffineOpen_top S) (isAffineOpen_top T) hW)
  let ε := hpush.flip.tensorEquiv (A' := Γ(X, W)) (E := Γ(T, ⊤)) rfl (by
    rw [Scheme.Hom.appLE_top_top_eq_appTop, hg]
    rfl)
  have hε (r : Γ(X, W)) (b : Γ(T, ⊤)) : ε (r ⊗ₜ b) = g'.appLE W (g' ⁻¹ᵁ W) le_rfl r *
      f'.appLE ⊤ (g' ⁻¹ᵁ W) (by simp) b :=
    hpush.flip.tensorEquiv_tmul _ _ r b
  let εₗ : Γ(X, W) ⊗[Γ(S, ⊤)] Γ(T, ⊤) ≃ₗ[Γ(X, W)] Γ(Y, g' ⁻¹ᵁ W) :=
    { ε.toAddEquiv with
      map_smul' r x := by
        change ε (r • x) = r • ε x
        rw [Algebra.smul_def, map_mul, Algebra.TensorProduct.algebraMap_apply,
          Algebra.algebraMap_self, RingHom.id_apply, hε, map_one, mul_one, Algebra.smul_def]
        rfl }
  let Φ : Γ(T, ⊤) ⊗[Γ(S, ⊤)] sectionsModule f ℱ W ≃+
      sectionsModule f' ((pullback g').obj ℱ) (g' ⁻¹ᵁ W) :=
    (TensorProduct.comm Γ(S, ⊤) Γ(T, ⊤) (sectionsModule f ℱ W)).toAddEquiv.trans
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange Γ(S, ⊤) Γ(X, W) Γ(X, W)
        (sectionsModule f ℱ W) Γ(T, ⊤)).symm.toAddEquiv.trans
      ((εₗ.lTensor (sectionsModule f ℱ W)).toAddEquiv.trans
      ((TensorProduct.comm Γ(X, W) (sectionsModule f ℱ W) Γ(Y, g' ⁻¹ᵁ W)).toAddEquiv.trans
        e₁.toAddEquiv)))
  suffices h : ∀ x, sectionsModuleBaseChange H ℱ hg W x = Φ x by
    have : ⇑(sectionsModuleBaseChange H ℱ hg W) = ⇑Φ := funext h
    rw [this]
    exact Φ.bijective
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul b m =>
    rw [sectionsModuleBaseChange_tmul]
    change _ = e₁ (TensorProduct.comm _ _ _ (εₗ.lTensor _
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange Γ(S, ⊤) Γ(X, W) Γ(X, W)
        (sectionsModule f ℱ W) Γ(T, ⊤)).symm (m ⊗ₜ b))))
    rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearEquiv.lTensor_tmul,
      TensorProduct.comm_tmul]
    change _ = e₁ (ε (1 ⊗ₜ b) ⊗ₜ (m : Γ(ℱ, W)))
    rw [hε, map_one, one_mul, ← mul_one (f'.appLE ⊤ (g' ⁻¹ᵁ W) _ b), ← smul_eq_mul,
      ← TensorProduct.smul_tmul', e₁.map_smul, he₁,
      TopCat.Presheaf.map_homOfLE_self_apply]
    rfl

/-! ### The Čech complex -/

section Cech

open TopCat.Presheaf

variable {ι : Type u} (U : ι → X.Opens)

omit [Algebra Γ(S, ⊤) Γ(T, ⊤)] in
/-- Restriction commutes with the pullback of sections and the action of `Γ(T, ⊤)`. -/
lemma presheaf_map_smul_pullbackSection {V W : X.Opens} (h : V ≤ W) (b : Γ(T, ⊤))
    (m : sectionsModule f ℱ W) :
    sectionsModuleRestrict f' ((pullback g').obj ℱ) (g'.preimage_mono h)
      (b • pullbackSectionAddHom (f := f) (f' := f') (g' := g') ℱ W m) =
      b • pullbackSectionAddHom (f := f) (f' := f') (g' := g') ℱ V
        (sectionsModuleRestrict f ℱ h m) := by
  rw [LinearMap.map_smul]
  congr 1
  exact (pullbackSection_map g' h m).symm

/-- The identification of sections over equal opens. -/
noncomputable def sectionsModuleEqLinearEquiv {M : Scheme.{u}} {p : M ⟶ T} (𝒢 : M.Modules)
    {V W : M.Opens} (h : V = W) : sectionsModule p 𝒢 W ≃ₗ[Γ(T, ⊤)] sectionsModule p 𝒢 V where
  __ := sectionsModuleRestrict p 𝒢 h.le
  invFun := sectionsModuleRestrict p 𝒢 h.ge
  left_inv m := by
    change sectionsModuleRestrict p 𝒢 h.ge (sectionsModuleRestrict p 𝒢 h.le m) = m
    rw [sectionsModuleRestrict_comp, sectionsModuleRestrict_self]
  right_inv m := by
    change sectionsModuleRestrict p 𝒢 h.le (sectionsModuleRestrict p 𝒢 h.ge m) = m
    rw [sectionsModuleRestrict_comp, sectionsModuleRestrict_self]

/-- The base change of Čech cochains `B ⊗[A] Č^k(U, ℱ) ⟶ Č^k(g'⁻¹ U, g'^* ℱ)`,
`b ⊗ c ↦ (y ↦ b • g'^* (c y))`. -/
noncomputable def cechModuleBaseChange (k : ℕ) :
    Γ(T, ⊤) ⊗[Γ(S, ⊤)] (∀ y : Fin (k + 1) → ι, sectionsModule f ℱ (⨅ l, U (y l))) →ₗ[Γ(T, ⊤)]
      (∀ y : Fin (k + 1) → ι, sectionsModule f' ((pullback g').obj ℱ) (⨅ l, g' ⁻¹ᵁ U (y l))) :=
  LinearMap.pi fun y ↦ (sectionsModuleEqLinearEquiv ((pullback g').obj ℱ)
    (iInf_preimage_eq_preimage_iInf g' U y)).toLinearMap ∘ₗ
      sectionsModuleBaseChange H ℱ hg (⨅ l, U (y l)) ∘ₗ
        (LinearMap.proj (R := Γ(S, ⊤)) y).baseChange Γ(T, ⊤)

lemma cechModuleBaseChange_tmul (k : ℕ) (b : Γ(T, ⊤))
    (c : ∀ y : Fin (k + 1) → ι, sectionsModule f ℱ (⨅ l, U (y l))) (y : Fin (k + 1) → ι) :
    cechModuleBaseChange H ℱ hg U k (b ⊗ₜ c) y =
      sectionsModuleRestrict f' ((pullback g').obj ℱ)
        (iInf_preimage_eq_preimage_iInf g' U y).le
        (b • pullbackSectionAddHom (f := f) (f' := f') (g' := g') ℱ _ (c y)) := by
  simp only [cechModuleBaseChange, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.baseChange_tmul, LinearMap.coe_proj, Function.eval, sectionsModuleBaseChange_tmul]
  rfl

/-- **Base change of Čech cochains commutes with the differentials.** -/
theorem cechModuleBaseChange_d (k : ℕ)
    (x : Γ(T, ⊤) ⊗[Γ(S, ⊤)] (∀ y : Fin (k + 1) → ι, sectionsModule f ℱ (⨅ l, U (y l)))) :
    cechModuleBaseChange H ℱ hg U (k + 1) ((cechModuleD f ℱ U k).baseChange Γ(T, ⊤) x) =
      cechModuleD f' ((pullback g').obj ℱ) (fun i ↦ g' ⁻¹ᵁ U i) k
        (cechModuleBaseChange H ℱ hg U k x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b c =>
    funext y
    rw [LinearMap.baseChange_tmul, cechModuleBaseChange_tmul, cechModuleD_apply_apply,
      cechModuleD_apply_apply, map_sum, Finset.smul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_zsmul, smul_comm, map_zsmul, cechModuleBaseChange_tmul]
    congr 1
    rw [← presheaf_map_smul_pullbackSection, sectionsModuleRestrict_comp,
      sectionsModuleRestrict_comp]

/-- **Base change of Čech cochains is bijective** when `S`, `T` are affine, `ℱ` is
quasi-coherent and the finite intersections of the finitely many opens `U i` are affine. -/
theorem bijective_cechModuleBaseChange [IsAffine S] [IsAffine T]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] [Finite ι]
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineOpen (⨅ l, U (y l))) (k : ℕ) :
    Function.Bijective (cechModuleBaseChange H ℱ hg U k) := by
  classical
  have := Fintype.ofFinite ι
  let e := (TensorProduct.piRight Γ(S, ⊤) Γ(T, ⊤) Γ(T, ⊤)
    (fun y : Fin (k + 1) → ι ↦ sectionsModule f ℱ (⨅ l, U (y l)))).trans
    (LinearEquiv.piCongrRight fun y ↦ (LinearEquiv.ofBijective _
      (bijective_sectionsModuleBaseChange H ℱ hg (hU k y))).trans
      (sectionsModuleEqLinearEquiv ((pullback g').obj ℱ)
        (iInf_preimage_eq_preimage_iInf g' U y)))
  suffices h : ∀ x, cechModuleBaseChange H ℱ hg U k x = e x by
    have : ⇑(cechModuleBaseChange H ℱ hg U k) = ⇑e := funext h
    rw [this]
    exact e.bijective
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul b c =>
    funext y
    rw [cechModuleBaseChange_tmul]
    simp only [e, LinearEquiv.trans_apply, TensorProduct.piRight_apply,
      TensorProduct.piRightHom_tmul, LinearEquiv.piCongrRight_apply,
      LinearEquiv.ofBijective_apply, sectionsModuleBaseChange_tmul]
    rfl

variable [IsAffine S] [IsAffine T] [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]
  [Finite ι] (hU : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineOpen (⨅ l, U (y l)))

/-- The base change of the Čech complex, indexed by `ℕ`. -/
noncomputable def cechModuleComplexNatBaseChangeIso :
    ((ModuleCat.baseChange Γ(S, ⊤) Γ(T, ⊤)).mapHomologicalComplex _).obj
      (cechModuleComplexNat f ℱ U) ≅
      cechModuleComplexNat f' ((pullback g').obj ℱ) (fun i ↦ g' ⁻¹ᵁ U i) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun k ↦ (LinearEquiv.ofBijective _ (bijective_cechModuleBaseChange H ℱ hg U hU k)).toModuleIso)
    (by
      rintro k _ rfl
      ext x : 2
      rw [Functor.mapHomologicalComplex_obj_d, cechModuleComplexNat_d, cechModuleComplexNat_d]
      exact (cechModuleBaseChange_d H ℱ hg U k x).symm)

/-- **Base change of the Čech complex.** For a cartesian square with affine bases
`S = Spec A` and `T = Spec B`, a quasi-coherent `𝒪_X`-module `ℱ` and a finite family `U` of
opens of `X` whose finite intersections are affine, the Čech complex of `g'^* ℱ` for the family
`g'⁻¹ U` is the base change `B ⊗[A] Č(U, ℱ)` of the Čech complex of `ℱ`. -/
noncomputable def cechModuleComplexBaseChangeIso :
    ((ModuleCat.baseChange Γ(S, ⊤) Γ(T, ⊤)).mapHomologicalComplex _).obj
      (cechModuleComplex f ℱ U) ≅
      cechModuleComplex f' ((pullback g').obj ℱ) (fun i ↦ g' ⁻¹ᵁ U i) :=
  HomologicalComplex.mapExtendIso _ _ _ ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor _).mapIso
      (cechModuleComplexNatBaseChangeIso H ℱ hg U hU)

end Cech

end AlgebraicGeometry.Scheme.Modules
