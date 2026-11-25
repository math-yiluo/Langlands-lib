/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.LinearAlgebra.TensorProduct.Map
import WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineChartUnit
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Bijectivity of the affine tensor-sections map

Source: Stacks Project, Schemes, Tags 01I9, 01IA, 01HV; Sheaves, Tags 0097, 00A0.
(blueprint: lem-weil-pbc-module-pullback-affine-sections-bijective).
-/

@[expose] public section
universe u
open CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- Elaboration compares native tensor products with ModuleCat extension of scalars.
/-- Bijectivity of an A-linear map with the canonical affine pure-tensor formula.
Source: Stacks Project, Schemes, Tags 01I9, 01IA and 01HV; Sheaves, Tags 0097 and 00A0.
(blueprint: lem-weil-pbc-module-pullback-affine-sections-bijective).

Proof: restrict G along Spec A → Y, and identify its global sections with G(V).
The affine tilde-Gamma counit and the tilde pullback comparison give the B-linear
bijection B tensor_A Γ(G|Spec A) → Γ(ψ*G|Spec A). The chart square identifies the right
adjoints of restriction followed by ψ-pullback and f-pullback followed by restriction.
Uniqueness of left adjoints gives k between the two composites. On global sections,
compose k with the restriction-sections identification over B and swap tensor factors.
The chart-unit compatibility identifies the image of 1 tensor s with the restricted
unit of the standard pullback of f. Finally, identify the specified tensor pullback
with the standard pullback by uniqueness of left adjoints; its unit equation and
naturality with restriction identify the given map with this composite on pure
tensors. Tensor induction extends equality to every tensor, and the composite of
bijections proves both injectivity and surjectivity. -/
theorem tensorPullback_affine_sections_bijective
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.affineOpens) (U : X.affineOpens)
    (hUV : U.1 ≤ f ⁻¹ᵁ V.1) :
    letI : Algebra Γ(Y, V.1) Γ(X, U.1) := (f.appLE V.1 U.1 hUV).hom.toAlgebra
    letI : ∀ G : Y.Modules, Module Γ(Y, V.1) Γ((tensorPullback f).obj G, U.1) :=
      fun G ↦ Module.compHom Γ((tensorPullback f).obj G, U.1)
        (f.appLE V.1 U.1 hUV).hom
    ∀ (G : Y.Modules) (_ : G.IsQuasicoherent)
      (c : (Γ(G, V.1) ⊗[Γ(Y, V.1)] Γ(X, U.1)) →ₗ[Γ(Y, V.1)]
        Γ((tensorPullback f).obj G, U.1)),
      (∀ (s : Γ(G, V.1)) (b : Γ(X, U.1)),
        c (s ⊗ₜ[Γ(Y, V.1)] b) =
          b • ((tensorPullback f).obj G).presheaf.map (homOfLE hUV).op
            (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app G).val.app
              (op V.1) s)) → Function.Bijective c := by
  classical
  dsimp only
  intro G hG c hc
  let := hG
  let : Algebra Γ(Y, V.1) Γ(X, U.1) := (f.appLE V.1 U.1 hUV).hom.toAlgebra
  let : ∀ G : Y.Modules, Module Γ(Y, V.1) Γ((tensorPullback f).obj G, U.1) :=
    fun G ↦ Module.compHom Γ((tensorPullback f).obj G, U.1)
        (f.appLE V.1 U.1 hUV).hom
  let jV := V.2.fromSpec
  let jU := U.2.fromSpec
  let ρ := f.appLE V.1 U.1 hUV
  let ψ := Spec.map ρ
  have hsq : ψ ≫ jV = jU ≫ f := V.2.SpecMap_appLE_fromSpec f U.2 hUV
  let N := G.restrict jV
  let eV := sectionsRestrictFromSpecLinearEquiv G V.2
  let eU := sectionsRestrictFromSpecLinearEquiv ((pullback f).obj G) U.2
  let adj₁ := (restrictAdjunction jV).comp (pullbackPushforwardAdjunction ψ)
  let adj₂ := (pullbackPushforwardAdjunction f).comp (restrictAdjunction jU)
  let rightIso : pushforward ψ ⋙ pushforward jV ≅ pushforward jU ⋙ pushforward f :=
    pushforwardComp ψ jV ≪≫ pushforwardCongr hsq ≪≫ (pushforwardComp jU f).symm
  let k : (restrictFunctor jV ⋙ pullback ψ) ≅ (pullback f ⋙ restrictFunctor jU) :=
    adj₁.leftAdjointUniq (adj₂.ofNatIsoRight rightIso.symm)
  let e₁ := pullbackSpecΓEquiv ρ N
  let e₂ := LinearEquiv.ofBijective (Hom.appSpecₗ (k.hom.app G) ⊤)
    (ConcreteCategory.bijective_of_isIso ((k.hom.app G).app ⊤))
  have he : Function.Bijective (fun x ↦ eU (e₂ (e₁ x))) :=
    eU.bijective.comp (e₂.bijective.comp e₁.bijective)
  let e₀ := (TensorProduct.congr eV.symm (LinearEquiv.refl Γ(Y, V.1) Γ(X, U.1))) ≪≫ₗ
    TensorProduct.comm Γ(Y, V.1) _ Γ(X, U.1)
  let e₀' := ModuleCat.tensorEquivExtendScalars Γ(Y, V.1) Γ(X, U.1)
    (moduleSpecΓFunctor.obj N)
  let k₀ := (Classical.choose (exists_tensorPullbackAdjunction f)).leftAdjointUniq
    (pullbackPushforwardAdjunction f)
  have h₀ := ConcreteCategory.bijective_of_isIso ((k₀.hom.app G).app U.1)
  have eqc (t : Γ(G, V.1) ⊗[Γ(Y, V.1)] Γ(X, U.1)) :
      ((k₀.hom.app G).app U.1) (c t) = eU (e₂ (e₁ (e₀' (e₀ t)))) := by
    induction t using TensorProduct.inductionOn with
    | tmul s b =>
      rw [hc, Hom.app_smul]
      change b • ((k₀.hom.app G).app U.1) _ =
        eU (e₂ (e₁ (e₀' (b ⊗ₜ[Γ(Y, V.1)] eV.symm s))))
      rw [show b ⊗ₜ[Γ(Y, V.1)] eV.symm s =
          b • ((1 : Γ(X, U.1)) ⊗ₜ[Γ(Y, V.1)] eV.symm s) by
        rw [TensorProduct.smul_tmul']; simp only [smul_eq_mul, mul_one]]
      rw [e₀'.map_smul, e₁.map_smul, e₂.map_smul, eU.map_smul]
      congr 1
      have ht : e₁ (e₀' ((1 : Γ(X, U.1)) ⊗ₜ[Γ(Y, V.1)] eV.symm s)) =
          (pullbackUnit ψ N).app ⊤ (eV.symm s) := by
        exact pullbackSpecΓEquiv_one_tmul ρ N (eV.symm s)
      rw [ht]
      have hk := affineChart_pullback_unit f V U hUV G s
      change _ = eU (((k.hom.app G).app ⊤)
        ((pullbackUnit ψ N).app ⊤ (eV.symm s)))
      rw [hk]
      have hn := (k₀.hom.app G).val.naturality (homOfLE hUV).op
      have hv := Adjunction.unit_leftAdjointUniq_hom_app
        (Classical.choose (exists_tensorPullbackAdjunction f))
        (pullbackPushforwardAdjunction f) G
      exact (congrArg (fun q ↦ q
        (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app G).val.app
          (op V.1) s)) hn).trans
        (congrArg (fun z ↦ ((pullback f).obj G).presheaf.map (homOfLE hUV).op z)
          (congrArg (fun q ↦ q.val.app (op V.1) s) hv))
    | add t t' ht ht' =>
      rw [c.map_add, (((k₀.hom.app G).app U.1).hom).map_add,
        e₀.map_add, e₀'.map_add, e₁.map_add, e₂.map_add, eU.map_add, ht, ht']
  have H := he.comp (e₀'.bijective.comp e₀.bijective)
  constructor
  · intro t t' ht
    apply H.injective
    exact (eqc t).symm.trans
      ((congrArg (fun z ↦ ((k₀.hom.app G).app U.1) z) ht).trans (eqc t'))
  · intro y
    obtain ⟨t, ht⟩ := H.surjective (((k₀.hom.app G).app U.1) y)
    exact ⟨t, h₀.injective ((eqc t).trans ht)⟩
end AlgebraicGeometry.Scheme.Modules
