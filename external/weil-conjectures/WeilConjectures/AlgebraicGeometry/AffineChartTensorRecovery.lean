/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
public import WeilConjectures.AlgebraicGeometry.ChartOrdinaryMapRecovery
public import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.Modules.FaithfullyFlatDescent
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Pullback of morphisms in normalized tensor coordinates

Source: Stacks Project, Tags 01I6, 0095 and 0096.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Scheme.Modules

private theorem pullbackΓ_smul_top {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)
    (b : Γ(X, ⊤)) (m : Γ(M, ⊤)) :
    pullbackΓ f M (b • m) = f.appTop b • pullbackΓ f M m := by
  simp only [pullbackΓ_apply]
  exact Hom.app_smul _ b m

private theorem affine_global_hom_ext {X : Scheme.{u}} {R : CommRingCat.{u}}
    (e : X ≅ Spec R) {M N : X.Modules} [M.IsQuasicoherent] {α β : M ⟶ N}
    (h : ∀ m : Γ(M, ⊤), α.app ⊤ m = β.app ⊤ m) : α = β := by
  let F := restrictFunctor e.inv
  let G := restrictFunctor e.hom
  let d : F ⋙ G ≅ 𝟭 X.Modules :=
    (restrictFunctorComp e.hom e.inv).symm ≪≫
      restrictFunctorCongr e.hom_inv_id ≪≫ restrictFunctorId
  let : F.Faithful := Functor.Faithful.of_comp_iso d
  apply F.map_injective
  apply hom_ext_of_isQuasicoherent_Spec
  intro m
  change α.app (e.inv ''ᵁ ⊤) m = β.app (e.inv ''ᵁ ⊤) m
  have htop : e.inv ''ᵁ ⊤ = ⊤ := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso]
  have hh (W : X.Opens) (hW : W = ⊤) (m : Γ(M, W)) :
      α.app W m = β.app W m := by
    subst W
    exact h m
  exact hh _ htop m

private theorem affine_pullback_hom_ext {X Y : Scheme.{u}} [IsAffine X]
    (f : Y ⟶ X) (M : X.Modules) [M.IsQuasicoherent] {N : Y.Modules}
    {α β : (Scheme.Modules.pullback f).obj M ⟶ N}
    (h : ∀ m : Γ(M, ⊤),
      α.app ⊤ (pullbackΓ f M m) = β.app ⊤ (pullbackΓ f M m)) : α = β := by
  apply ((pullbackPushforwardAdjunction f).homEquiv _ _).injective
  apply affine_global_hom_ext X.isoSpec
  intro m
  simpa only [Adjunction.homEquiv_unit, Hom.comp_app, pushforward_map_app,
    ConcreteCategory.comp_apply, pullbackΓ_apply, Scheme.Hom.preimage_top] using! h m

private theorem comparison_unit {X X₀ X₁ Y : Scheme.{u}}
    (f₀ : X₀ ⟶ X) (f₁ : X₁ ⟶ X) (v : Y ⟶ X₀) (l : Y ⟶ X₁)
    (hv : v ≫ f₀ = l ≫ f₁) (L : X.Modules) (m : Γ(L, ⊤)) :
    let d := pullbackComp v f₀ ≪≫ pullbackCongr hv ≪≫ (pullbackComp l f₁).symm
    (d.hom.app L).app ⊤ (pullbackΓ v _ (pullbackΓ f₀ L m)) =
      pullbackΓ l _ (pullbackΓ f₁ L m) := by
  change ((pullbackComp l f₁).inv.app L).app ⊤
    (((pullbackCompOfEq v f₀ (l ≫ f₁) hv L).hom).app ⊤
      (pullbackΓ v _ (pullbackΓ f₀ L m))) = _
  rw [pullbackCompOfEq_hom_app_pullbackΓ]
  simpa [pullbackCompOfEq, pullbackCongr, Iso.app] using!
    pullbackCompOfEq_inv_app_pullbackΓ l f₁ (l ≫ f₁) rfl L m

private theorem unitTensor_smul {A B : Type u} [CommRing A] [CommRing B]
    (r : A →+* B) (P : ModuleCat.{u} A) (a : A) (z : P) :
    (1 : B) ⊗ₜ[A,r] (a • z) = r a • ((1 : B) ⊗ₜ[A,r] z :
      (ModuleCat.extendScalars r).obj P) := by
  let : Module A B := Module.compHom B r
  rw [TensorProduct.tmul_smul]
  change (r a * 1) ⊗ₜ[A,r] z = r a • ((1 : B) ⊗ₜ[A,r] z :
    (ModuleCat.extendScalars r).obj P)
  rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]


/-- Tensor coordinates detect pullback of a morphism across a scheme square.
Source: Stacks Project, Tag 01I6, and Tags 0095 and 0096.
(blueprint: lem-pc-affine-chart-tensor-coordinate-recovery).

Proof: Let d identify v⁎f₀⁎L with l⁎fₓ⁎L using the square equation hv.
The comparison carries the composite direct pullback unit to the iterated stage
unit, by composition of the pullback adjunctions. For Q, compare the additive
maps from B ⊗ₐ Q to sections on V given by d followed after pullback along v
of e₀N(cQ.inv(1 ⊗ -)), and by pullback along l of eₓN. On 1 ⊗ n, cQ's
normalization and the unit comparison give equality. On b ⊗ n, semilinearity
and the ring-map equation move b outside and give the same equality. Tensor
induction proves equality on every stage tensor. The normalization for P
identifies the input sections under d.inv. Compare the two claimed sheaf maps
on pullbacks of eₓM(1 ⊗ m): naturality of the pullback unit, hψ, hτ, the
Q-coordinate identity and hs give equality. Semilinearity extends to b ⊗ m,
additivity to every stage tensor, and surjectivity of eₓM to every stage global
section. Since X₁ is affine and fₓ⁎M is quasi-coherent, affine reconstruction
and the pullback adjunction determine a morphism from these generator images.
Thus the two sheaf maps are equal. This proof uses no limit or colimit, no
existence of comparison models, and no finite-presentation hypothesis. It also
covers empty affine schemes, zero rings and zero modules. -/
private theorem tensor_coordinate_square
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (r : A →+* B) (r₁ : B →+* C) (r₀ : A →+* C)
    {X X₀ X₁ V : Scheme.{u}}
    (f₀ : X₀ ⟶ X) (fₓ : X₁ ⟶ X) (v : V ⟶ X₀) (l : V ⟶ X₁)
    (hv : v ≫ f₀ = l ≫ fₓ)
    (M N : X.Modules) (hMq : M.IsQuasicoherent)
    (P Q : ModuleCat.{u} A)
    (δM : P ≃ Γ(M, ⊤)) (δN : Q ≃ Γ(N, ⊤))
    (ρ₀ : C →+* Γ(X₀, ⊤))
    (ρₓ : B →+* Γ(X₁, ⊤))
    (e₀M : (ModuleCat.extendScalars r₀).obj P ≃+
      Γ((Scheme.Modules.pullback (f₀)).obj M, ⊤))
    (e₀N : (ModuleCat.extendScalars r₀).obj Q ≃+
      Γ((Scheme.Modules.pullback (f₀)).obj N, ⊤))
    (eₓM : (ModuleCat.extendScalars r).obj P ≃+
      Γ((Scheme.Modules.pullback (fₓ)).obj M, ⊤))
    (eₓN : (ModuleCat.extendScalars r).obj Q ≃+
      Γ((Scheme.Modules.pullback (fₓ)).obj N, ⊤))
    (h₀N : ∀ b z, e₀N (b • z) = ρ₀ b • e₀N z)
    (hₓM : ∀ b z, eₓM (b • z) = ρₓ b • eₓM z)
    (hₓN : ∀ b z, eₓN (b • z) = ρₓ b • eₓN z)
    (n₀M : ∀ m, e₀M ((1 : C) ⊗ₜ[A,r₀] m) =
      pullbackΓ (f₀) M (δM m))
    (n₀N : ∀ m, e₀N ((1 : C) ⊗ₜ[A,r₀] m) =
      pullbackΓ (f₀) N (δN m))
    (nₓM : ∀ m, eₓM ((1 : B) ⊗ₜ[A,r] m) =
      pullbackΓ (fₓ) M (δM m))
    (nₓN : ∀ m, eₓN ((1 : B) ⊗ₜ[A,r] m) =
      pullbackΓ (fₓ) N (δN m))
    (hAffine : IsAffine (X₁))
    (cQ : (ModuleCat.extendScalars r₀).obj Q ≅
      (ModuleCat.extendScalars r₁).obj ((ModuleCat.extendScalars r).obj Q))
    (hcQ : ∀ m, cQ.hom ((1 : C) ⊗ₜ[A,r₀] m) =
      (1 : C) ⊗ₜ[B,r₁] ((1 : B) ⊗ₜ[A,r] m))
    (τ : (ModuleCat.extendScalars r₀).obj P ⟶ (ModuleCat.extendScalars r₀).obj Q)
    (s : (ModuleCat.extendScalars r).obj P ⟶ (ModuleCat.extendScalars r).obj Q)
    (hτ : ∀ m, τ ((1 : C) ⊗ₜ[A,r₀] m) =
      cQ.inv ((1 : C) ⊗ₜ[B,r₁] s ((1 : B) ⊗ₜ[A,r] m)))
    (ψ : (Scheme.Modules.pullback (f₀)).obj M ⟶
      (Scheme.Modules.pullback (f₀)).obj N)
    (s' : (Scheme.Modules.pullback (fₓ)).obj M ⟶
      (Scheme.Modules.pullback (fₓ)).obj N)
    (hψ : ∀ z, ψ.app ⊤ (e₀M z) = e₀N (τ z))
    (hs : ∀ z, s'.app ⊤ (eₓM z) = eₓN (s z)) :
    let d := Scheme.Modules.pullbackComp v f₀ ≪≫ Scheme.Modules.pullbackCongr hv ≪≫
      (Scheme.Modules.pullbackComp l fₓ).symm
    (∀ b, v.appTop (ρ₀ (r₁ b)) = l.appTop (ρₓ b)) →
      d.inv.app M ≫ (Scheme.Modules.pullback v).map ψ ≫ d.hom.app N =
        (Scheme.Modules.pullback l).map s' := by
  classical
  let d := Scheme.Modules.pullbackComp v f₀ ≪≫ Scheme.Modules.pullbackCongr hv ≪≫
    (Scheme.Modules.pullbackComp l fₓ).symm
  change (∀ b, v.appTop (ρ₀ (r₁ b)) = l.appTop (ρₓ b)) →
    d.inv.app M ≫ (Scheme.Modules.pullback v).map ψ ≫ d.hom.app N =
      (Scheme.Modules.pullback l).map s'
  intro hRing
  have hout (z : (ModuleCat.extendScalars r).obj Q) :
      (d.hom.app N).app ⊤ (pullbackΓ v _
        (e₀N (cQ.inv ((1 : C) ⊗ₜ[B,r₁] z)))) = pullbackΓ l _ (eₓN z) := by
    induction z using TensorProduct.inductionOn with
    | tmul b n =>
      change B at b
      have hb : b ⊗ₜ[A,r] n = b • ((1 : B) ⊗ₜ[A,r] n :
          (ModuleCat.extendScalars r).obj Q) := by
        rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
      have hn : cQ.inv ((1 : C) ⊗ₜ[B,r₁] ((1 : B) ⊗ₜ[A,r] n)) =
          (1 : C) ⊗ₜ[A,r₀] n := by
        rw [← hcQ]
        exact cQ.toLinearEquiv.symm_apply_apply _
      rw [hb, unitTensor_smul r₁ ((ModuleCat.extendScalars r).obj Q),
        cQ.inv.hom.map_smul, h₀N,
        pullbackΓ_smul_top, Scheme.Modules.Hom.app_smul, hₓN, pullbackΓ_smul_top,
        hRing, hn, n₀N, nₓN]
      exact congrArg ((l.appTop (ρₓ b)) • ·)
        (comparison_unit (f₀) (fₓ) v l hv N (δN n))
    | add z z' hz hz' =>
      simp only [TensorProduct.tmul_add, map_add, hz, hz']
  let : M.IsQuasicoherent := hMq
  let : IsAffine X₁ := hAffine
  let : ((Scheme.Modules.pullback (fₓ)).obj M).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_pullback _ M
  change d.inv.app M ≫ (Scheme.Modules.pullback v).map ψ ≫ d.hom.app N =
    (Scheme.Modules.pullback l).map s'
  apply affine_pullback_hom_ext l _
  intro z
  obtain ⟨z, rfl⟩ := eₓM.surjective z
  induction z using TensorProduct.inductionOn with
  | tmul b m =>
    change B at b
    have hb : b ⊗ₜ[A,r] m = b • ((1 : B) ⊗ₜ[A,r] m :
        (ModuleCat.extendScalars r).obj P) := by
      rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
    rw [hb, hₓM, pullbackΓ_smul_top]
    rw [Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul]
    apply congrArg ((l.appTop (ρₓ b)) • ·)
    have hinput : (d.inv.app M).app ⊤
        (pullbackΓ l _ (eₓM ((1 : B) ⊗ₜ[A,r] m))) =
        pullbackΓ v _ (e₀M ((1 : C) ⊗ₜ[A,r₀] m)) := by
      rw [nₓM, n₀M, ← comparison_unit (f₀)
        (fₓ) v l hv M (δM m)]
      simpa only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
        Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply] using
        congr($(d.hom_inv_id_app M).app ⊤
          (pullbackΓ v _ (pullbackΓ (f₀) M (δM m))))
    simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
    calc
      _ = (d.hom.app N).app ⊤ (((Scheme.Modules.pullback v).map ψ).app ⊤
          (pullbackΓ v _ (e₀M ((1 : C) ⊗ₜ[A,r₀] m)))) :=
        congrArg (fun z ↦ (d.hom.app N).app ⊤
          (((Scheme.Modules.pullback v).map ψ).app ⊤ z)) hinput
      _ = (d.hom.app N).app ⊤ (pullbackΓ v _
          (ψ.app ⊤ (e₀M ((1 : C) ⊗ₜ[A,r₀] m)))) :=
        congrArg ((d.hom.app N).app ⊤) (pullbackΓ_naturality v ψ _)
      _ = (d.hom.app N).app ⊤ (pullbackΓ v _
          (e₀N (τ ((1 : C) ⊗ₜ[A,r₀] m)))) :=
        congrArg (fun z ↦ (d.hom.app N).app ⊤ (pullbackΓ v _ z)) (hψ _)
      _ = (d.hom.app N).app ⊤ (pullbackΓ v _
          (e₀N (cQ.inv ((1 : C) ⊗ₜ[B,r₁] s ((1 : B) ⊗ₜ[A,r] m))))) :=
        congrArg (fun z ↦ (d.hom.app N).app ⊤ (pullbackΓ v _ (e₀N z))) (hτ m)
      _ = pullbackΓ l _ (eₓN (s ((1 : B) ⊗ₜ[A,r] m))) := hout _
      _ = pullbackΓ l _ (s'.app ⊤ (eₓM ((1 : B) ⊗ₜ[A,r] m))) :=
        congrArg (pullbackΓ l _) (hs _).symm
      _ = _ := (pullbackΓ_naturality l s' _).symm
  | add z z' hz hz' => simp only [map_add, hz, hz']

/-- A chart specialization of the tensor-coordinate square criterion.
Source: Stacks Project, Tag 01I6, and Tags 0095 and 0096.
(blueprint: lem-pc-affine-chart-tensor-coordinate-recovery).

Proof: Form the canonical lift from the iterated chart to the direct chart.
Its second-projection equation is the square equation for the two maps to U(a).
Apply the tensor-coordinate square criterion proved above. Its comparison is
exactly the comparison in chartOrdinaryMapRecovery. The criterion proves the
section identity by tensor induction, pullback-unit composition and affine
quasi-coherent reconstruction, as detailed in the preceding proof. -/
theorem affine_chart_tensor_coordinate_recovery
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (r : A →+* B) (r₁ : B →+* C) (r₀ : A →+* C)
    {X Y Z : Scheme.{u}} (q : Y ⟶ X) (p : Z ⟶ Y) (q₀ : Z ⟶ X)
    (w : p ≫ q = q₀) (U : X.OpenCover.{u}) (a : U.I₀)
    (M N : (U.X a).Modules) (hMq : M.IsQuasicoherent)
    (P Q : ModuleCat.{u} A)
    (δM : P ≃ Γ(M, ⊤)) (δN : Q ≃ Γ(N, ⊤))
    (ρ₀ : C →+* Γ((U.pullback₁ q₀).X a, ⊤))
    (ρₓ : B →+* Γ((U.pullback₁ q).X a, ⊤))
    (e₀M : (ModuleCat.extendScalars r₀).obj P ≃+
      Γ((Scheme.Modules.pullback (U.pullbackHom q₀ a)).obj M, ⊤))
    (e₀N : (ModuleCat.extendScalars r₀).obj Q ≃+
      Γ((Scheme.Modules.pullback (U.pullbackHom q₀ a)).obj N, ⊤))
    (eₓM : (ModuleCat.extendScalars r).obj P ≃+
      Γ((Scheme.Modules.pullback (U.pullbackHom q a)).obj M, ⊤))
    (eₓN : (ModuleCat.extendScalars r).obj Q ≃+
      Γ((Scheme.Modules.pullback (U.pullbackHom q a)).obj N, ⊤))
    (h₀N : ∀ b z, e₀N (b • z) = ρ₀ b • e₀N z)
    (hₓM : ∀ b z, eₓM (b • z) = ρₓ b • eₓM z)
    (hₓN : ∀ b z, eₓN (b • z) = ρₓ b • eₓN z)
    (n₀M : ∀ m, e₀M ((1 : C) ⊗ₜ[A,r₀] m) =
      pullbackΓ (U.pullbackHom q₀ a) M (δM m))
    (n₀N : ∀ m, e₀N ((1 : C) ⊗ₜ[A,r₀] m) =
      pullbackΓ (U.pullbackHom q₀ a) N (δN m))
    (nₓM : ∀ m, eₓM ((1 : B) ⊗ₜ[A,r] m) =
      pullbackΓ (U.pullbackHom q a) M (δM m))
    (nₓN : ∀ m, eₓN ((1 : B) ⊗ₜ[A,r] m) =
      pullbackΓ (U.pullbackHom q a) N (δN m))
    (hAffine : IsAffine ((U.pullback₁ q).X a))
    (cQ : (ModuleCat.extendScalars r₀).obj Q ≅
      (ModuleCat.extendScalars r₁).obj ((ModuleCat.extendScalars r).obj Q))
    (hcQ : ∀ m, cQ.hom ((1 : C) ⊗ₜ[A,r₀] m) =
      (1 : C) ⊗ₜ[B,r₁] ((1 : B) ⊗ₜ[A,r] m))
    (τ : (ModuleCat.extendScalars r₀).obj P ⟶ (ModuleCat.extendScalars r₀).obj Q)
    (s : (ModuleCat.extendScalars r).obj P ⟶ (ModuleCat.extendScalars r).obj Q)
    (hτ : ∀ m, τ ((1 : C) ⊗ₜ[A,r₀] m) =
      cQ.inv ((1 : C) ⊗ₜ[B,r₁] s ((1 : B) ⊗ₜ[A,r] m)))
    (ψ : (Scheme.Modules.pullback (U.pullbackHom q₀ a)).obj M ⟶
      (Scheme.Modules.pullback (U.pullbackHom q₀ a)).obj N)
    (s' : (Scheme.Modules.pullback (U.pullbackHom q a)).obj M ⟶
      (Scheme.Modules.pullback (U.pullbackHom q a)).obj N)
    (hψ : ∀ z, ψ.app ⊤ (e₀M z) = e₀N (τ z))
    (hs : ∀ z, s'.app ⊤ (eₓM z) = eₓN (s z)) :
    let Uk : Y.OpenCover.{u} := U.pullback₁ q
    let V : Z.OpenCover.{u} := Uk.pullback₁ p
    let v : V.X a ⟶ (U.pullback₁ q₀).X a := pullback.lift (V.f a)
      (Uk.pullbackHom p a ≫ U.pullbackHom q a)
      (by
        dsimp only [V]
        rw [Category.assoc, U.pullbackHom_map,
          ← Category.assoc, Uk.pullbackHom_map, Category.assoc, w])
    (∀ b, v.appTop (ρ₀ (r₁ b)) = (Uk.pullbackHom p a).appTop (ρₓ b)) →
      chartOrdinaryMapRecovery q p q₀ w U a M N ψ s' := by
  classical
  intro Uk V v hRing
  let l := Uk.pullbackHom p a
  have hv : v ≫ U.pullbackHom q₀ a = l ≫ U.pullbackHom q a :=
    pullback.lift_snd _ _ _
  unfold chartOrdinaryMapRecovery
  exact tensor_coordinate_square r r₁ r₀ (U.pullbackHom q₀ a)
    (U.pullbackHom q a) v l hv M N hMq P Q δM δN ρ₀ ρₓ e₀M e₀N eₓM eₓN
    h₀N hₓM hₓN n₀M n₀N nₓM nₓN hAffine cQ hcQ τ s hτ ψ s' hψ hs hRing

end AlgebraicGeometry
