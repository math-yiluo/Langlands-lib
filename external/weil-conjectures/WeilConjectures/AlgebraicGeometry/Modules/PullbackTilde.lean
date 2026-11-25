/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Pullback of quasi-coherent modules along morphisms of affine schemes

Let `R ⟶ S` be a ring map and `f : Spec S ⟶ Spec R` the induced morphism. The pullback of `M^~`
along `f` is `(S ⊗[R] M)^~`: both functors are left adjoint to `N ↦ Γ(N, ⊤)` viewed as an
`R`-module. On global sections, the resulting identification sends `1 ⊗ m` to the image of `m`
under the unit of the adjunction `f^* ⊣ f_*`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite TensorProduct

namespace AlgebraicGeometry

namespace Scheme.Modules

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

set_option backward.isDefEq.respectTransparency false in
/-- The global sections over `Spec R` of the pushforward along `Spec.map φ` are the global
sections over `Spec S`, viewed as an `R`-module. -/
noncomputable def pushforwardSpecMapCompΓIso :
    pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R) ≅
      moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom :=
  NatIso.ofComponents (fun P ↦ LinearEquiv.toModuleIso
    (X₁ := (pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R)).obj P)
    (X₂ := (moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom).obj P)
    { toFun x := x
      invFun x := x
      map_add' _ _ := rfl
      map_smul' r x := by
        let y : Γ(P, ⊤) := x
        change (Spec.map φ).appTop ((ΓSpecIso R).inv r) • y = (ΓSpecIso S).inv (φ r) • y
        rw [← CommRingCat.comp_apply, ← ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
      left_inv _ := rfl
      right_inv _ := rfl }) (fun _ ↦ rfl)

/-- The adjunction `(tilde ⋙ f^*) ⊣ (Γ ⋙ restrictScalars φ)`. -/
noncomputable def tildePullbackAdjunction :
    tilde.functor R ⋙ pullback (Spec.map φ) ⊣
      moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom :=
  (tilde.adjunction.comp (pullbackPushforwardAdjunction (Spec.map φ))).ofNatIsoRight
    (pushforwardSpecMapCompΓIso φ)

/-- **Pullback of `M^~` along `Spec S ⟶ Spec R` is `(S ⊗[R] M)^~`.** -/
noncomputable def tildePullbackIso :
    tilde.functor R ⋙ pullback (Spec.map φ) ≅ ModuleCat.extendScalars φ.hom ⋙ tilde.functor S :=
  (tildePullbackAdjunction φ).leftAdjointUniq
    ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp tilde.adjunction)

lemma tildePullbackIso_hom_app_pullbackUnit (M : ModuleCat.{u} R) (m : M) :
    ((tildePullbackIso φ).hom.app M).app ⊤
      ((pullbackUnit (Spec.map φ) (tilde M)).app ⊤ (tilde.toOpen M ⊤ m)) =
      tilde.toOpen ((ModuleCat.extendScalars φ.hom).obj M) ⊤ ((1 : S) ⊗ₜ m) := by
  have := congr($((tildePullbackAdjunction φ).unit_leftAdjointUniq_hom_app
    ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp tilde.adjunction) M) m)
  exact this

variable {φ} in
/-- On sections, a morphism of `𝒪_{Spec R}`-modules is `R`-linear. -/
lemma Hom.app_smul_Spec {P Q : (Spec R).Modules} (g : P ⟶ Q) (U : (Spec R).Opens) (r : R)
    (x : Γ(P, U)) : g.app U (r • x) = r • g.app U x := by
  rw [smul_Spec_def, smul_Spec_def, Hom.app_smul]

variable {φ} in
/-- On sections, a morphism of `𝒪_{Spec R}`-modules as an `R`-linear map. -/
noncomputable def Hom.appSpecₗ {P Q : (Spec R).Modules} (g : P ⟶ Q) (U : (Spec R).Opens) :
    Γ(P, U) →ₗ[R] Γ(Q, U) where
  toFun := g.app U
  map_add' := map_add _
  map_smul' := g.app_smul_Spec U

/-- The global sections of `f^* M^~` are `S ⊗[R] M`, for `f : Spec S ⟶ Spec R`. -/
noncomputable def tildePullbackΓEquiv (M : ModuleCat.{u} R) :
    (ModuleCat.extendScalars φ.hom).obj M ≃ₗ[S]
      Γ((pullback (Spec.map φ)).obj (tilde M), ⊤) :=
  (LinearEquiv.ofBijective (tilde.toOpen ((ModuleCat.extendScalars φ.hom).obj M) ⊤).hom
    (ConcreteCategory.bijective_of_isIso _)) ≪≫ₗ
    (LinearEquiv.ofBijective (Hom.appSpecₗ ((tildePullbackIso φ).hom.app M) ⊤)
      (ConcreteCategory.bijective_of_isIso (((tildePullbackIso φ).hom.app M).app ⊤))).symm

lemma tildePullbackΓEquiv_one_tmul (M : ModuleCat.{u} R) (m : M) :
    tildePullbackΓEquiv φ M ((1 : S) ⊗ₜ m) =
      (pullbackUnit (Spec.map φ) (tilde M)).app ⊤ (tilde.toOpen M ⊤ m) := by
  dsimp only [tildePullbackΓEquiv, LinearEquiv.trans_apply]
  exact (LinearEquiv.symm_apply_eq _).mpr (tildePullbackIso_hom_app_pullbackUnit φ M m).symm

lemma fromTildeΓ_app_toOpen (M : (Spec R).Modules) (m : Γ(M, ⊤)) :
    M.fromTildeΓ.app ⊤ (tilde.toOpen (moduleSpecΓFunctor.obj M) ⊤ m) = m := by
  have := congr($(toOpen_fromTildeΓ_app M ⊤) m)
  refine this.trans ?_
  change M.presheaf.map (homOfLE le_top).op m = m
  rw [show (homOfLE le_top : (⊤ : (Spec R).Opens) ⟶ ⊤) = 𝟙 _ from rfl, op_id,
    CategoryTheory.Functor.map_id]
  rfl

/-- **Base change for quasi-coherent modules along `Spec S ⟶ Spec R`**: the global sections of
the pullback of a quasi-coherent `𝒪_{Spec R}`-module `M` are `S ⊗[R] Γ(M, ⊤)`. -/
noncomputable def pullbackSpecΓEquiv (M : (Spec R).Modules) [M.IsQuasicoherent] :
    (ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj M) ≃ₗ[S]
      Γ((pullback (Spec.map φ)).obj M, ⊤) :=
  haveI : IsIso M.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent M
  haveI : IsIso ((pullback (Spec.map φ)).map M.fromTildeΓ) := inferInstance
  tildePullbackΓEquiv φ _ ≪≫ₗ
    LinearEquiv.ofBijective (Hom.appSpecₗ ((pullback (Spec.map φ)).map M.fromTildeΓ) ⊤)
      (ConcreteCategory.bijective_of_isIso (((pullback (Spec.map φ)).map M.fromTildeΓ).app ⊤))

lemma pullbackSpecΓEquiv_one_tmul (M : (Spec R).Modules) [M.IsQuasicoherent] (m : Γ(M, ⊤)) :
    pullbackSpecΓEquiv φ M ((1 : S) ⊗ₜ m) = (pullbackUnit (Spec.map φ) M).app ⊤ m := by
  change ((pullback (Spec.map φ)).map M.fromTildeΓ).app ⊤
    (tildePullbackΓEquiv φ (moduleSpecΓFunctor.obj M) ((1 : S) ⊗ₜ m)) = _
  refine (congr_arg (((pullback (Spec.map φ)).map M.fromTildeΓ).app ⊤)
    (tildePullbackΓEquiv_one_tmul φ (moduleSpecΓFunctor.obj M) m)).trans ?_
  have := congr($(((pullbackPushforwardAdjunction (Spec.map φ)).unit.naturality
    M.fromTildeΓ)).app ⊤ (tilde.toOpen (moduleSpecΓFunctor.obj M) ⊤ m))
  refine this.symm.trans ?_
  exact congr_arg ((pullbackUnit (Spec.map φ) M).app ⊤) (fromTildeΓ_app_toOpen M m)

section Algebra

/-- The ring map `R → Γ(Spec R, U)`. -/
noncomputable abbrev toΓSpec (R : Type u) [CommRing R] (U : (Spec (.of R)).Opens) :
    R →+* Γ(Spec (.of R), U) :=
  ((ΓSpecIso (.of R)).inv ≫ (Spec (.of R)).presheaf.map (homOfLE le_top).op).hom

/-- Sections of an `𝒪_{Spec R}`-module are `R`-modules, for `R` a commutative ring, through
`R → Γ(Spec R, U)`. (This agrees with the instance for `R : CommRingCat`, but is defined directly
through the `Γ(Spec R, U)`-module structure.) -/
noncomputable scoped instance moduleOf {R : Type u} [CommRing R] (M : (Spec (.of R)).Modules)
    (U : (Spec (.of R)).Opens) : Module R Γ(M, U) :=
  Module.compHom Γ(M, U) (toΓSpec R U)

lemma smul_of_def {R : Type u} [CommRing R] {M : (Spec (.of R)).Modules}
    {U : (Spec (.of R)).Opens} (r : R) (x : Γ(M, U)) : r • x = toΓSpec R U r • x :=
  rfl

/-- On sections, morphisms of `𝒪_{Spec R}`-modules are `R`-linear. -/
lemma Hom.app_smul_of {R : Type u} [CommRing R] {P Q : (Spec (.of R)).Modules} (g : P ⟶ Q)
    (U : (Spec (.of R)).Opens) (r : R) (x : Γ(P, U)) : g.app U (r • x) = r • g.app U x :=
  Hom.app_smul g _ x

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- On global sections over `Spec A`, the unit of the adjunction for `Spec B ⟶ Spec A` is
semilinear along `algebraMap A B`. -/
lemma pullbackΓ_smul (P : (Spec (.of A)).Modules) (a : A) (x : Γ(P, ⊤)) :
    pullbackΓ (Spec.map (CommRingCat.ofHom (algebraMap A B))) P (a • x) =
      algebraMap A B a • pullbackΓ (Spec.map (CommRingCat.ofHom (algebraMap A B))) P x := by
  set f := Spec.map (CommRingCat.ofHom (algebraMap A B))
  rw [smul_of_def, smul_of_def, pullbackΓ_apply, pullbackΓ_apply]
  refine (Hom.app_smul (pullbackUnit f P) (toΓSpec A ⊤ a) x).trans ?_
  have hr : f.app ⊤ (toΓSpec A ⊤ a) = toΓSpec B ⊤ (algebraMap A B a) := by
    simp only [toΓSpec, homOfLE_leOfHom, CommRingCat.hom_comp, RingHom.coe_comp,
      Function.comp_apply]
    rw [show (homOfLE le_top : (⊤ : (Spec (.of A)).Opens) ⟶ ⊤) = 𝟙 _ from rfl,
      show (homOfLE le_top : (⊤ : (Spec (.of B)).Opens) ⟶ ⊤) = 𝟙 _ from rfl, op_id, op_id,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    exact (congr($(ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A B))) a)).symm
  exact congrArg (fun r : Γ(Spec (.of B), f ⁻¹ᵁ ⊤) ↦ r • pullbackUnitApp f P ⊤ x) hr

/-- **Base change for quasi-coherent modules along `Spec B ⟶ Spec A`**, for an `A`-algebra `B`:
the global sections of the pullback of a quasi-coherent `𝒪_{Spec A}`-module `M` are
`B ⊗[A] Γ(M, ⊤)`, with `1 ⊗ m` corresponding to the image of `m` under the unit. -/
theorem exists_linearEquiv_pullback_Spec (M : (Spec (.of A)).Modules) [M.IsQuasicoherent] :
    ∃ e : B ⊗[A] Γ(M, ⊤) ≃ₗ[B]
      Γ((pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj M, ⊤),
      ∀ m : Γ(M, ⊤), e (1 ⊗ₜ m) =
        pullbackΓ (Spec.map (CommRingCat.ofHom (algebraMap A B))) M m := by
  let φ : CommRingCat.of A ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap A B)
  let e₁ := pullbackSpecΓEquiv φ M
  -- identify the two `A`-module structures on `Γ(M, ⊤)`
  let M₀ : ModuleCat (CommRingCat.of A) := @ModuleCat.of (CommRingCat.of A) _ Γ(M, ⊤) _
    (moduleOf M ⊤)
  let i : M₀ ≅ (moduleSpecΓFunctor (R := .of A)).obj M := LinearEquiv.toModuleIso
    (X₁ := M₀) (X₂ := (moduleSpecΓFunctor (R := .of A)).obj M)
    { toFun x := x
      invFun x := x
      map_add' _ _ := rfl
      map_smul' r x := (smul_Spec_def (R := .of A) (M := M) (U := ⊤) r x).symm
      left_inv _ := rfl
      right_inv _ := rfl }
  let e₀ := ModuleCat.tensorEquivExtendScalars A B M₀ ≪≫ₗ
    ((ModuleCat.extendScalars φ.hom).mapIso i).toLinearEquiv
  let e : B ⊗[A] Γ(M, ⊤) ≃ₗ[B] Γ((pullback (Spec.map φ)).obj M, ⊤) :=
    { toFun t := e₁ (e₀ t)
      invFun y := e₀.symm (e₁.symm y)
      map_add' x y := by rw [map_add, map_add]
      map_smul' b t := by
        rw [LinearEquiv.map_smul]
        exact (e₁.map_smul b (e₀ t)).trans
          (smul_Spec_def (R := .of B) (M := (pullback (Spec.map φ)).obj M) (U := ⊤) b _)
      left_inv t := by simp
      right_inv y := by simp }
  exact ⟨e, fun m ↦ (pullbackSpecΓEquiv_one_tmul φ M m).trans (pullbackΓ_apply _ M m).symm⟩

end Algebra

end Scheme.Modules

end AlgebraicGeometry
