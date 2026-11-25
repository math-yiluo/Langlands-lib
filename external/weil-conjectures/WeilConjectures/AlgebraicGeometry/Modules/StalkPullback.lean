/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk

/-!
# The stalk of the pullback of an `𝒪_S`-module

Let `g : T ⟶ S` be a morphism of schemes, `t` a point of `T` and `M` an `𝒪_S`-module. The stalk
of `g^* M` at `t` is the base change `𝒪_{T,t} ⊗_{𝒪_{S,g t}} M_{g t}`
(`AlgebraicGeometry.Scheme.Modules.bijective_pullbackStalkMap`).

The comparison map `𝒪_{T,t} ⊗ M_{g t} → (g^* M)_t` is induced by the unit `M ⟶ g_* g^* M`. It
is bijective since both sides corepresent the same functor on `𝒪_{T,t}`-modules `I`: maps
`(g^* M)_t → I` are morphisms `g^* M ⟶ t_* I` to the skyscraper module at `t`, hence morphisms
`M ⟶ g_* t_* I = (g t)_* I`, hence `𝒪_{S,g t}`-linear maps `M_{g t} → I`.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace Opposite TensorProduct

/-- A linear map `c` is bijective as soon as precomposition with `c` is a bijection
`(B →ₗ[R] I) → (A →ₗ[R] I)` for every module `I`. -/
theorem LinearMap.bijective_of_forall_bijective_comp {R A B : Type u} [CommRing R]
    [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B] (c : A →ₗ[R] B)
    (h : ∀ (I : Type u) [AddCommGroup I] [Module R I],
      Function.Bijective fun k : B →ₗ[R] I ↦ k ∘ₗ c) : Function.Bijective c := by
  obtain ⟨w, hw⟩ := (h A).2 LinearMap.id
  have hcw : c ∘ₗ w = LinearMap.id := (h B).1 (by
    simp only [LinearMap.comp_assoc, hw]
    rfl)
  exact ⟨Function.LeftInverse.injective (g := w) fun a ↦ congr($hw a),
    Function.RightInverse.surjective (g := w) fun b ↦ congr($hcw b)⟩

namespace AlgebraicGeometry.Scheme.Modules

variable {S T : Scheme.{u}} (g : T ⟶ S) (t : T)

/-- The map `(g_* N)_{g t} → N_t` on stalks of a pushforward. -/
noncomputable def pushforwardStalkMap (N : T.Modules) :
    ((pushforward g).obj N).presheaf.stalk (g t) →+ N.presheaf.stalk t :=
  ConcreteCategory.hom (colimit.desc ((OpenNhds.inclusion (g t)).op ⋙
      ((pushforward g).obj N).presheaf)
    { pt := N.presheaf.stalk t
      ι :=
        { app U := N.presheaf.germ (g ⁻¹ᵁ U.unop.1) t U.unop.2
          naturality U V i := by
            ext n
            exact N.presheaf.germ_res_apply (homOfLE (g.preimage_mono (leOfHom i.unop))) t
              V.unop.2 n } })

variable {g t} in
@[simp]
lemma pushforwardStalkMap_germ (N : T.Modules) {U : S.Opens} (hU : g t ∈ U)
    (n : Γ((pushforward g).obj N, U)) :
    pushforwardStalkMap g t N (((pushforward g).obj N).presheaf.germ U (g t) hU n) =
      N.presheaf.germ (g ⁻¹ᵁ U) t hU n := by
  rw [pushforwardStalkMap, TopCat.Presheaf.germ]
  erw [Limits.colimit.ι_desc_apply]
  rfl

/-- The structure of `𝒪_{S,g t}`-algebra on `𝒪_{T,t}` given by the stalk map of `g`. -/
noncomputable abbrev stalkAlgebra : Algebra (S.presheaf.stalk (g t)) (T.presheaf.stalk t) :=
  (g.stalkMap t).hom.toAlgebra

attribute [local instance] stalkAlgebra

/-- An `𝒪_{T,t}`-module is an `𝒪_{S,g t}`-module through the stalk map of `g`. -/
noncomputable abbrev stalkModule (I : Type*) [AddCommGroup I] [Module (T.presheaf.stalk t) I] :
    Module (S.presheaf.stalk (g t)) I :=
  Module.compHom I (g.stalkMap t).hom

attribute [local instance] stalkModule

instance (I : Type*) [AddCommGroup I] [Module (T.presheaf.stalk t) I] :
    IsScalarTower (S.presheaf.stalk (g t)) (T.presheaf.stalk t) I :=
  ⟨fun a b i ↦ mul_smul (g.stalkMap t a) b i⟩

/-- The additive map `M_{g t} → (g^* M)_t` induced by the unit `M ⟶ g_* g^* M`. -/
noncomputable def pullbackStalkAddHom (M : S.Modules) :
    M.presheaf.stalk (g t) →+ ((pullback g).obj M).presheaf.stalk t :=
  (pushforwardStalkMap g t _).comp
    (((pullbackPushforwardAdjunction g).unit.app M).stalkLinearMap (g t)).toAddMonoidHom

variable {g t} in
@[simp]
lemma pullbackStalkAddHom_germ (M : S.Modules) {U : S.Opens} (hU : g t ∈ U)
    (m : Γ(M, U)) :
    pullbackStalkAddHom g t M (M.presheaf.germ U (g t) hU m) =
      ((pullback g).obj M).presheaf.germ (g ⁻¹ᵁ U) t hU
        (((pullbackPushforwardAdjunction g).unit.app M).app U m) := by
  rw [pullbackStalkAddHom, AddMonoidHom.comp_apply]
  erw [Hom.stalkLinearMap_germ]
  exact pushforwardStalkMap_germ _ hU _

/-- The `𝒪_{S,g t}`-linear map `M_{g t} → (g^* M)_t` induced by the unit `M ⟶ g_* g^* M`. -/
noncomputable def pullbackStalkLinearMap (M : S.Modules) :
    M.presheaf.stalk (g t) →ₗ[S.presheaf.stalk (g t)] ((pullback g).obj M).presheaf.stalk t :=
  stalkLinearMapMk (pullbackStalkAddHom g t M) fun U hU r m ↦ by
    rw [pullbackStalkAddHom_germ, pullbackStalkAddHom_germ, Hom.app_smul]
    refine (germ_smul ((pullback g).obj M) t hU (g.app U r) _).trans ?_
    exact (congrArg (· • _) (Scheme.Hom.germ_stalkMap_apply g U t hU r)).symm

variable {g t} in
@[simp]
lemma pullbackStalkLinearMap_germ (M : S.Modules) {U : S.Opens} (hU : g t ∈ U)
    (m : Γ(M, U)) :
    pullbackStalkLinearMap g t M (M.presheaf.germ U (g t) hU m) =
      ((pullback g).obj M).presheaf.germ (g ⁻¹ᵁ U) t hU
        (((pullbackPushforwardAdjunction g).unit.app M).app U m) :=
  pullbackStalkAddHom_germ M hU m

/-- The comparison map `𝒪_{T,t} ⊗_{𝒪_{S,g t}} M_{g t} → (g^* M)_t`. -/
noncomputable def pullbackStalkMap (M : S.Modules) :
    T.presheaf.stalk t ⊗[S.presheaf.stalk (g t)] M.presheaf.stalk (g t) →ₗ[T.presheaf.stalk t]
      ((pullback g).obj M).presheaf.stalk t :=
  (pullbackStalkLinearMap g t M).liftBaseChange _

/-- Precomposing with `M_{g t} → (g^* M)_t` is the composite of the bijections given by the
stalk–skyscraper adjunctions at `t` and `g t` and the adjunction `g^* ⊣ g_*`. -/
lemma comp_pullbackStalkLinearMap_eq (M : S.Modules) (I : Type u) [AddCommGroup I]
    [Module (T.presheaf.stalk t) I]
    (k : ((pullback g).obj M).presheaf.stalk t →ₗ[T.presheaf.stalk t] I) :
    k.restrictScalars (S.presheaf.stalk (g t)) ∘ₗ pullbackStalkLinearMap g t M =
      (skyscraperHomEquiv (g t) I M).symm
        ((pullbackPushforwardAdjunction g).homEquiv _ _ (skyscraperHomEquiv t I _ k) ≫
          (pushforwardSkyscraperIso g t I rfl).hom) := by
  refine LinearMap.ext fun a ↦ ?_
  obtain ⟨U, hU, m, rfl⟩ := M.presheaf.exists_germ_eq a
  rw [LinearMap.comp_apply, pullbackStalkLinearMap_germ, LinearMap.restrictScalars_apply]
  simp only [skyscraperHomEquiv, Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk, LinearMap.comp_apply,
    Adjunction.homEquiv_unit]
  erw [Hom.stalkLinearMap_germ, skyscraperStalkEval_germ]
  rfl

/-- **The stalk of a pullback.** The comparison map `𝒪_{T,t} ⊗_{𝒪_{S,g t}} M_{g t} → (g^* M)_t` is
bijective. -/
theorem bijective_pullbackStalkMap (M : S.Modules) :
    Function.Bijective (pullbackStalkMap g t M) := by
  refine LinearMap.bijective_of_forall_bijective_comp _ fun I _ _ ↦ ?_
  have : (fun k ↦ k ∘ₗ pullbackStalkMap g t M) = LinearMap.liftBaseChangeEquiv _ ∘
      (fun k ↦ (skyscraperHomEquiv (g t) I M).symm
        ((pullbackPushforwardAdjunction g).homEquiv _ _ (skyscraperHomEquiv t I _ k) ≫
          (pushforwardSkyscraperIso g t I rfl).hom)) := by
    ext k : 1
    rw [Function.comp_apply, ← comp_pullbackStalkLinearMap_eq, pullbackStalkMap,
      LinearMap.liftBaseChange_comp]
  rw [this]
  refine (LinearEquiv.bijective _).comp ((Equiv.bijective _).comp ?_)
  have hpost : Function.Bijective
      fun f : M ⟶ (pushforward g).obj (skyscraper t I) ↦
        f ≫ (pushforwardSkyscraperIso g t I rfl).hom :=
    ⟨fun a b h ↦ by simpa using congrArg (· ≫ (pushforwardSkyscraperIso g t I rfl).inv) h,
      fun b ↦ ⟨b ≫ (pushforwardSkyscraperIso g t I rfl).inv, by simp⟩⟩
  exact hpost.comp ((Equiv.bijective _).comp (Equiv.bijective _))

/-- Naturality of the comparison map `𝒪_{T,t} ⊗ M_{g t} → (g^* M)_t`. -/
lemma pullbackStalkMap_naturality {M M' : S.Modules} (φ : M ⟶ M')
    (z : T.presheaf.stalk t ⊗[S.presheaf.stalk (g t)] M.presheaf.stalk (g t)) :
    pullbackStalkMap g t M' (LinearMap.lTensor _ (φ.stalkLinearMap (g t)) z) =
      ((pullback g).map φ).stalkLinearMap t (pullbackStalkMap g t M z) := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | tmul a b =>
    obtain ⟨U, hU, m, rfl⟩ := M.presheaf.exists_germ_eq b
    simp only [pullbackStalkMap, LinearMap.lTensor_tmul, LinearMap.liftBaseChange_tmul,
      Hom.stalkLinearMap_germ, pullbackStalkLinearMap_germ, LinearMap.map_smul]
    congr 2
    exact congrArg (fun f : M ⟶ (pushforward g).obj ((pullback g).obj M') ↦ f.app U m)
      ((pullbackPushforwardAdjunction g).unit.naturality φ)

end AlgebraicGeometry.Scheme.Modules
