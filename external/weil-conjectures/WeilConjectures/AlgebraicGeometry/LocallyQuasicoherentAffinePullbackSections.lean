/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.LinearAlgebra.TensorProduct.Map
import WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineChartUnit
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-! # Affine pullback sections from local quasi-coherence

Source: Stacks Project, Tags 01I7, 01HV, 01I9, 0096 and 0097.
(blueprint: new-p4-locally-quasicoherent-affine-pullback-sections). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
open scoped TensorProduct
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Scheme.Modules

-- Affine chart tensors and module-category scalar extensions need elaboration fuel.
private theorem tensorPullback_affine_sections_bijective_of_chart
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.affineOpens) (U : X.affineOpens)
    (hUV : U.1 ≤ f ⁻¹ᵁ V.1) :
    letI : Algebra Γ(Y, V.1) Γ(X, U.1) := (f.appLE V.1 U.1 hUV).hom.toAlgebra
    letI : ∀ G : Y.Modules, Module Γ(Y, V.1) Γ((tensorPullback f).obj G, U.1) :=
      fun G ↦ Module.compHom Γ((tensorPullback f).obj G, U.1)
        (f.appLE V.1 U.1 hUV).hom
    ∀ (G : Y.Modules) (_ : (G.restrict V.2.fromSpec).IsQuasicoherent)
      (c : (Γ(G, V.1) ⊗[Γ(Y, V.1)] Γ(X, U.1)) →ₗ[Γ(Y, V.1)]
        Γ((tensorPullback f).obj G, U.1)),
      (∀ (s : Γ(G, V.1)) (b : Γ(X, U.1)),
        c (s ⊗ₜ[Γ(Y, V.1)] b) =
          b • ((tensorPullback f).obj G).presheaf.map (homOfLE hUV).op
            (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app G).val.app
              (op V.1) s)) → Function.Bijective c := by
  classical
  dsimp only
  intro G hN c hc
  let := hN
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

end Scheme.Modules

/-- Tensor pullback sections need quasi-coherence only on the affine target open.
Source: Stacks Project, Tag 01I9(1), lemma-widetilde-pullback; Tag 0096,
lemma-adjoint-pullback-pushforward-modules; Tag 0097, lemma-push-pull-composition-modules.
(blueprint: new-p4-locally-quasicoherent-affine-pullback-sections).
Proof: Put V=i inverse-image U, which is affine because i is affine. Restrict
G to Spec A through the canonical chart of U. Quasi-coherence of G on U and
restriction along the chart isomorphism make this restricted module N
quasi-coherent, with global sections identified with G(U). The affine chart
square identifies the right adjoints of chart restriction followed by the
standard Spec pullback and standard i-pullback followed by chart restriction.
Uniqueness of left adjoints gives the comparison k. The proved standard
pullbackSpecGamma equivalence gives B tensor_A Gamma(N) as sections on Spec B.
Compose with k and the chart section isomorphism. Compare tensorPullback i
with standard pullback by uniqueness of left adjoints as well. The existing
affineChart_pullback_unit theorem and the uniqueness unit equation show that
this composite sends b tensor s to b times the specified tensor pullback unit.
Construct that canonical map directly by TensorProduct.lift. Tensor induction
identifies it with the composite of bijections, proving bijectivity. Swapping
the tensor factors makes it B-linear; its pure-tensor formula proves the
B-linearity by tensor induction. Finally package it as a linear equivalence.
All section transports are equalities of opens and all maps are isomorphisms;
empty U, empty V and zero modules obey the same formulas. There is no global
quasi-coherence or quasi-separatedness hypothesis. -/
theorem exists_locallyQuasicoherent_affine_pullback_sections
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsAffineHom i]
    (U : Y.affineOpens) (G : Y.Modules) (hG : (G.restrict U.1.ι).IsQuasicoherent) :
    letI : Algebra Γ(Y, U.1) Γ(Z, i ⁻¹ᵁ U.1) := (i.app U.1).hom.toAlgebra
    ∃ e : (Γ(Z, i ⁻¹ᵁ U.1) ⊗[Γ(Y, U.1)] G.val.obj (op U.1)) ≃ₗ[Γ(Z, i ⁻¹ᵁ U.1)]
        ((Scheme.Modules.tensorPullback i).obj G).val.obj (op (i ⁻¹ᵁ U.1)),
      ∀ (b : Γ(Z, i ⁻¹ᵁ U.1)) (s : G.val.obj (op U.1)),
        e (b ⊗ₜ[Γ(Y, U.1)] s) = b •
          (show ((Scheme.Modules.tensorPullback i).obj G).val.obj (op (i ⁻¹ᵁ U.1)) from
            ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction i)).unit.app
            G).val.app (op U.1) s) := by
  classical
  dsimp only
  let : Algebra Γ(Y, U.1) Γ(Z, i ⁻¹ᵁ U.1) := (i.app U.1).hom.toAlgebra
  let V : Z.affineOpens := ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩
  let hUV : V.1 ≤ i ⁻¹ᵁ U.1 := le_rfl
  have happ : i.appLE U.1 V.1 hUV = i.app U.1 := by
    simp [Scheme.Hom.appLE, V]
  have : (G.restrict U.1.ι).IsQuasicoherent := hG
  have hN : (G.restrict U.2.fromSpec).IsQuasicoherent := by
    let H := G.restrict U.1.ι
    have : H.IsQuasicoherent := hG
    have : (H.restrict U.2.isoSpec.inv).IsQuasicoherent :=
      Scheme.Modules.isQuasicoherent_restrictFunctor U.2.isoSpec.inv H
    exact (SheafOfModules.isQuasicoherent (Spec Γ(Y, U.1)).ringCatSheaf).prop_of_iso
      ((Scheme.Modules.restrictFunctorComp U.2.isoSpec.inv U.1.ι).app G).symm
      (show (H.restrict U.2.isoSpec.inv).IsQuasicoherent from inferInstance)
  let : Module Γ(Y, U.1)
      (((Scheme.Modules.tensorPullback i).obj G).val.obj (op V.1)) :=
    Module.compHom _ (i.app U.1).hom
  let η := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction i)).unit.app G
  let unit : G.val.obj (op U.1) →ₗ[Γ(Y, U.1)]
      ((Scheme.Modules.tensorPullback i).obj G).val.obj (op V.1) :=
    { toFun := fun s ↦ η.val.app (op U.1) s
      map_add' := by intro s t; exact (η.val.app (op U.1)).hom.map_add s t
      map_smul' := by intro a s; exact (η.val.app (op U.1)).hom.map_smul a s }
  let c : (G.val.obj (op U.1) ⊗[Γ(Y, U.1)] Γ(Z, V.1)) →ₗ[Γ(Y, U.1)]
      ((Scheme.Modules.tensorPullback i).obj G).val.obj (op V.1) :=
    TensorProduct.lift (LinearMap.mk₂ Γ(Y, U.1)
    (fun s b ↦ b • unit s)
    (by intros; simp [smul_add])
    (by
      intro a s b
      rw [unit.map_smul]
      change b • ((i.app U.1).hom a • unit s) =
        (i.app U.1).hom a • (b • unit s)
      exact smul_comm _ _ _)
    (by intros; simp [add_smul])
    (by intro a s b; exact mul_smul _ _ _))
  have hc (s : G.val.obj (op U.1)) (b : Γ(Z, V.1)) :
      c (s ⊗ₜ[Γ(Y, U.1)] b) = b • unit s := TensorProduct.lift.tmul _ _
  have hbij : Function.Bijective c := by
    have H := Scheme.Modules.tensorPullback_affine_sections_bijective_of_chart i U V hUV
    dsimp only at H
    rw [happ] at H
    apply H G hN c
    intro s b
    change c (s ⊗ₜ[Γ(Y, U.1)] b) = b •
      ((Scheme.Modules.tensorPullback i).obj G).presheaf.map (𝟙 _) (unit s)
    rw [((Scheme.Modules.tensorPullback i).obj G).presheaf.map_id]
    exact hc s b
  let q : (Γ(Z, V.1) ⊗[Γ(Y, U.1)] G.val.obj (op U.1)) →ₗ[Γ(Z, V.1)]
      ((Scheme.Modules.tensorPullback i).obj G).val.obj (op V.1) :=
    { toFun := fun x ↦ c (TensorProduct.comm Γ(Y, U.1) _ _ x)
      map_add' := by intros; simp only [map_add]
      map_smul' := by
        intro b x
        induction x using TensorProduct.inductionOn with
        | tmul d s =>
          simp only [TensorProduct.smul_tmul', TensorProduct.comm_tmul, hc,
            smul_eq_mul, mul_smul, RingHom.id_apply]
        | add x y hx hy => simp_all only [map_add, smul_add] }
  refine ⟨LinearEquiv.ofBijective q
    (hbij.comp (TensorProduct.comm Γ(Y, U.1) _ _).bijective), ?_⟩
  intro b s
  exact hc s b

end AlgebraicGeometry
