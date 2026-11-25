/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackTensorIsIso

/-!
# Pullback of modules and tensor products

Source: Stacks Project, Modules, Lemma 17.16.4 (Tag 01CD), label
`lemma-tensor-product-pullback` (blueprint: lem-weil-pbc-module-pullback-tensor).

## Main statement

The tensor-formula pullback commutes naturally with tensor products and carries pure tensor
sections to pure tensor sections, as in the source statement.
-/

@[expose] public section

universe v

open CategoryTheory MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] presheafMonoidalCategory

private abbrev adj {X Y : Scheme.{v}} (f : X ⟶ Y) :=
  Classical.choose (exists_tensorPullbackAdjunction f)

private def sectionsBilinear {X Y : Scheme.{v}} (f : X ⟶ Y) (M N : Y.Modules)
    (U : Y.Opens) :
    Γ(M, U) →ₗ[Γ(Y, U)] Γ(N, U) →ₗ[Γ(Y, U)]
      Γ((pushforward f).obj ((tensorPullback f).obj M ⊗ (tensorPullback f).obj N), U) :=
  LinearMap.mk₂ Γ(Y, U)
    (fun s t ↦ tmulSection (M := (tensorPullback f).obj M) (N := (tensorPullback f).obj N)
      (U := f ⁻¹ᵁ U) (((adj f).unit.app M).app U s)
      (((adj f).unit.app N).app U t))
    (fun s s' t ↦ by rw [map_add, add_tmulSection])
    (fun r s t ↦ (congrArg (fun z ↦ tmulSection (M := (tensorPullback f).obj M)
      (N := (tensorPullback f).obj N) (U := f ⁻¹ᵁ U) z (((adj f).unit.app N).app U t))
      (Hom.app_smul _ r s)).trans (smul_tmulSection _ _ _))
    (fun s t t' ↦ by rw [map_add, tmulSection_add])
    (fun r s t ↦ (congrArg (tmulSection (M := (tensorPullback f).obj M)
      (N := (tensorPullback f).obj N)
      (U := f ⁻¹ᵁ U) (((adj f).unit.app M).app U s))
      (Hom.app_smul _ r t)).trans (tmulSection_smul _ _ _))

private def tensorPresheafHom {X Y : Scheme.{v}} (f : X ⟶ Y) (M N : Y.Modules) :
    (forgetToPresheafOfModules Y).obj M ⊗ (forgetToPresheafOfModules Y).obj N ⟶
      (forgetToPresheafOfModules Y).obj
        ((pushforward f).obj ((tensorPullback f).obj M ⊗ (tensorPullback f).obj N)) where
  app U := ModuleCat.ofHom (TensorProduct.lift (sectionsBilinear f M N U.unop))
  naturality {U U'} i := by
    ext1
    refine LinearMap.ext fun z ↦ ?_
    induction z using TensorProduct.inductionOn with
    | tmul s t =>
      have ht := PresheafOfModules.Monoidal.tensorObj_map_tmul (R := Y.presheaf) i s t
      refine (congrArg (TensorProduct.lift (sectionsBilinear f M N U'.unop)) ht).trans ?_
      refine (TensorProduct.lift.tmul _ _).trans ?_
      refine Eq.trans ?_ (congrArg
        (((pushforward f).obj
          ((tensorPullback f).obj M ⊗ (tensorPullback f).obj N)).val.map i).hom
        (TensorProduct.lift.tmul _ _).symm)
      dsimp only [sectionsBilinear, LinearMap.mk₂_apply]
      change tmulSection (M := (tensorPullback f).obj M) (N := (tensorPullback f).obj N)
        (((adj f).unit.app M).app U'.unop (M.presheaf.map i s))
        (((adj f).unit.app N).app U'.unop (N.presheaf.map i t)) =
        ((tensorPullback f).obj M ⊗ (tensorPullback f).obj N).presheaf.map
          ((Opens.map f.base).map i.unop).op
          (tmulSection (((adj f).unit.app M).app U.unop s)
            (((adj f).unit.app N).app U.unop t))
      have hM := Hom.app_presheaf_map ((adj f).unit.app M) i.unop
        (show Γ(M, U.unop) from s)
      have hN := Hom.app_presheaf_map ((adj f).unit.app N) i.unop
        (show Γ(N, U.unop) from t)
      exact (congrArg₂ (fun a b ↦ tmulSection
        (M := (tensorPullback f).obj M) (N := (tensorPullback f).obj N) a b) hM hN).trans
        (tmulSection_map (leOfHom ((Opens.map f.base).map i.unop)) _ _).symm
    | add a b ha hb => rw [map_add, map_add, ha, hb]

private def tensorPushforwardHom {X Y : Scheme.{v}} (f : X ⟶ Y) (M N : Y.Modules) :
    M ⊗ N ⟶ (pushforward f).obj ((tensorPullback f).obj M ⊗ (tensorPullback f).obj N) :=
  (SheafOfModules.tensorObjIsoSheafification M N).hom ≫
    ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).homEquiv _ _).symm
      (tensorPresheafHom f M N)

private def tensorComparison {X Y : Scheme.{v}} (f : X ⟶ Y) (M N : Y.Modules) :
    (tensorPullback f).obj (M ⊗ N) ⟶
      (tensorPullback f).obj M ⊗ (tensorPullback f).obj N :=
  ((adj f).homEquiv _ _).symm (tensorPushforwardHom f M N)

private theorem tensorPushforwardHom_tmul {X Y : Scheme.{v}} (f : X ⟶ Y)
    (M N : Y.Modules) (U : Y.Opens) (s : Γ(M, U)) (t : Γ(N, U)) :
    (tensorPushforwardHom f M N).app U (tmulSection s t) =
      tmulSection (M := (tensorPullback f).obj M) (N := (tensorPullback f).obj N)
      (U := f ⁻¹ᵁ U) (((adj f).unit.app M).app U s) (((adj f).unit.app N).app U t) := by
  let H := (pushforward f).obj ((tensorPullback f).obj M ⊗ (tensorPullback f).obj N)
  let P := M.val ⊗ N.val
  have he := (PresheafOfModules.sheafificationAdjunction
    (𝟙 Y.ringCatSheaf.obj)).homEquiv P H |>.apply_symm_apply (tensorPresheafHom f M N)
  rw [Adjunction.homEquiv_unit] at he
  have h := congrArg (fun q ↦ q.app (op U) (s ⊗ₜ[Γ(Y, U)] t)) he
  unfold tensorPushforwardHom
  rw [Hom.comp_app]
  unfold tmulSection
  have hc := (SheafOfModules.tensorObjIsoSheafification M N).inv_hom_id_assoc
    (((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).homEquiv
      P H).symm (tensorPresheafHom f M N))
  have hc' := congrArg (fun q ↦ q.val.app (op U)
    ((toSheafifyTensor M N).app (op U) (s ⊗ₜ[Γ(Y, U)] t))) hc
  exact hc'.trans (h.trans (TensorProduct.lift.tmul _ _))

private theorem tensorComparison_tmul {X Y : Scheme.{v}} (f : X ⟶ Y)
    (M N : Y.Modules) (U : Y.Opens) (s : Γ(M, U)) (t : Γ(N, U)) :
    (tensorComparison f M N).app (f ⁻¹ᵁ U)
      (((adj f).unit.app (M ⊗ N)).app U (tmulSection s t)) =
      tmulSection (M := (tensorPullback f).obj M) (N := (tensorPullback f).obj N)
      (U := f ⁻¹ᵁ U) (((adj f).unit.app M).app U s) (((adj f).unit.app N).app U t) := by
  have h := (adj f).homEquiv _ _ |>.apply_symm_apply (tensorPushforwardHom f M N)
  rw [Adjunction.homEquiv_unit] at h
  exact (congrArg (fun q ↦ q.app U (tmulSection s t)) h).trans
    (tensorPushforwardHom_tmul f M N U s t)

private theorem tensor_hom_ext {Y : Scheme.{v}} {M N H : Y.Modules}
    {a b : M ⊗ N ⟶ H}
    (h : ∀ (U : Y.Opens) (s : Γ(M, U)) (t : Γ(N, U)),
      a.app U (tmulSection s t) = b.app U (tmulSection s t)) : a = b := by
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification M N).inv).mp
  apply ((PresheafOfModules.sheafificationAdjunction
    (𝟙 Y.ringCatSheaf.obj)).homEquiv (M.val ⊗ N.val) H).injective
  apply PresheafOfModules.hom_ext
  intro U
  ext z
  induction z using TensorProduct.inductionOn with
  | tmul s t => exact h U.unop s t
  | add z w hz hw => simp only [map_add, hz, hw]

private theorem tensorComparison_naturality {X Y : Scheme.{v}} (f : X ⟶ Y)
    (M N M' N' : Y.Modules) (a : M ⟶ M') (b : N ⟶ N') :
    (tensorPullback f).map (a ⊗ₘ b) ≫ tensorComparison f M' N' =
      tensorComparison f M N ≫ ((tensorPullback f).map a ⊗ₘ (tensorPullback f).map b) := by
  apply ((adj f).homEquiv _ _).injective
  apply tensor_hom_ext
  intro U s t
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change (tensorComparison f M' N').app (f ⁻¹ᵁ U)
      (((tensorPullback f).map (a ⊗ₘ b)).app (f ⁻¹ᵁ U)
        (((adj f).unit.app (M ⊗ N)).app U (tmulSection s t))) =
    (((tensorPullback f).map a ⊗ₘ (tensorPullback f).map b)).app (f ⁻¹ᵁ U)
      ((tensorComparison f M N).app (f ⁻¹ᵁ U)
        (((adj f).unit.app (M ⊗ N)).app U (tmulSection s t)))
  have hn (P Q : Y.Modules) (c : P ⟶ Q) (z : Γ(P, U)) :
      ((tensorPullback f).map c).app (f ⁻¹ᵁ U) (((adj f).unit.app P).app U z) =
        ((adj f).unit.app Q).app U (c.app U z) :=
    congrArg (fun q ↦ q.app U z) ((adj f).unit_naturality c)
  rw [hn, tensorHom_app_tmulSection, tensorComparison_tmul, tensorComparison_tmul,
    tensorHom_app_tmulSection, hn, hn]

/-- Pullback of modules commutes with tensor products, naturally and on sections. The pullback
`f^*u` of a section `u` over `V` is the component over `f ⁻¹ᵁ V` of the unit of the chosen
adjunction `Classical.choose (exists_tensorPullbackAdjunction f)`.

Source: Stacks Project, Modules, Lemma 17.16.4 (Tag 01CD), label
`lemma-tensor-product-pullback` (blueprint: lem-weil-pbc-module-pullback-tensor).
Proof: construct the comparison by adjunction from the bilinear map on sections; check its
stalks using the stalk pullback and tensor lemmas and the base-change tensor identity; detect
isomorphisms on stalks. Naturality follows from the same adjunction and the sheaf tensor
universal property.
-/
theorem module_pullback_tensor {X Y : Scheme.{v}} (f : X ⟶ Y) :
    ∃ e : ∀ (M N : Y.Modules),
        (tensorPullback f).obj (M ⊗ N) ≅
          (tensorPullback f).obj M ⊗ (tensorPullback f).obj N,
      (∀ (M N M' N' : Y.Modules) (a : M ⟶ M') (b : N ⟶ N'),
        (tensorPullback f).map (a ⊗ₘ b) ≫ (e M' N').hom =
          (e M N).hom ≫ ((tensorPullback f).map a ⊗ₘ (tensorPullback f).map b)) ∧
      (∀ (M N : Y.Modules) (V : Y.Opens) (s : Γ(M, V)) (t : Γ(N, V)),
        (e M N).hom.app (f ⁻¹ᵁ V)
            (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app (M ⊗ N)).val.app
              (op V) (tmulSection s t) : Γ((tensorPullback f).obj (M ⊗ N), f ⁻¹ᵁ V)) =
          tmulSection
            (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app M).val.app
              (op V) s : Γ((tensorPullback f).obj M, f ⁻¹ᵁ V))
            (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app N).val.app
              (op V) t : Γ((tensorPullback f).obj N, f ⁻¹ᵁ V))) := by
  have he (M N : Y.Modules) : IsIso (tensorComparison f M N) :=
    isIso_tensorPullback_of_tmul f M N (tensorComparison f M N)
      (tensorComparison_tmul f M N)
  let := he
  let e : ∀ (M N : Y.Modules),
      (tensorPullback f).obj (M ⊗ N) ≅ (tensorPullback f).obj M ⊗ (tensorPullback f).obj N :=
    fun M N ↦ asIso (tensorComparison f M N)
  refine ⟨e, ?_, ?_⟩
  · exact tensorComparison_naturality f
  · intro M N V s t
    exact tensorComparison_tmul f M N V s t

end
end AlgebraicGeometry.Scheme.Modules
