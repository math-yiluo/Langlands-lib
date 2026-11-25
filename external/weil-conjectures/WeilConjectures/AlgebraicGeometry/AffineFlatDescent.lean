/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import WeilConjectures.Mathlib.RingTheory.Flat.DescentAlgebra
import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.GlobalSections

/-!
# The affine case of effective descent

Source: Stacks Project, Descent, Lemma 35.37.1 (Tag 0245), affine case.
(blueprint: lem-galois-affine-flat-descent-effective).
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory

namespace CategoryTheory.Over.DescentDatum

/-- Descent of an affine morphism along a flat surjective map of affine schemes.

Source: Stacks Project, Descent, Lemma 35.37.1 (Tag 0245), the affine case in its proof.
Write the base, cover and total space as `Spec R`, `Spec A` and `Spec B`; the last
is affine because its morphism to the affine cover is affine. The descent isomorphism
is, contravariantly, an isomorphism `B ⊗[R] A ≃ A ⊗[R] B`. Evaluating at `b ⊗ 1`
gives an `A`-algebra coaction. The threefold cocycle gives coassociativity; restriction
of the cocycle to the diagonal gives an invertible idempotent endomorphism of `B`,
hence the identity, which is the counit. Flat algebra descent gives the invariant
`R`-algebra `C` and the isomorphism `A ⊗[R] C ≃ₐ[A] B`, sending `a ⊗ c` to `ac`.
Its spectrum yields the pullback square over `Spec R`. Compatibility with transport
is checked on the invariant generators `c ⊗ 1`: both composites send these to
`1 ⊗ 1 ⊗ c`, and these generate because the comparison isomorphism is surjective.
Transporting the resulting square through the initial affine identifications proves
effectivity for the original schemes. The flat algebra theorem used here is
`Algebra.DescentDatum.descendedEquiv`; it requires only flatness. Surjectivity is
retained to match the affine case in the fpqc reduction.

(blueprint: lem-galois-affine-flat-descent-effective) -/
theorem isEffective_of_isAffineHom_flat_affine {X S : Scheme.{u}}
    [IsAffine X] [IsAffine S] (f : X ⟶ S) (hf : Flat f) (hs : Surjective f)
    {V : Over X} [IsAffineHom V.hom] (D : Over.DescentDatum f V) : D.IsEffective := by
  classical
  have : Surjective f := hs
  have : IsAffine V.left := isAffine_of_isAffineHom V.hom
  -- Evaluate transport at the universal pair on `V ×_S X`.
  let P := Limits.pullback (V.hom ≫ f) f
  let pr₁ : P ⟶ V.left := Limits.pullback.fst _ _
  let pr₂ : P ⟶ X := Limits.pullback.snd _ _
  have hpr : (pr₁ ≫ V.hom) ≫ f = pr₂ ≫ f := by
    rw [Category.assoc]
    exact Limits.pullback.condition
  let γ : P ⟶ V.left :=
    (D.transport (pr₁ ≫ V.hom) pr₂ hpr (Over.homMk pr₁)).left
  have hγv : γ ≫ V.hom = pr₂ := Over.w _
  have hγnat {T : Scheme.{u}} (g : T ⟶ P) (t₁ t₂ : T ⟶ X)
      (h : t₁ ≫ f = t₂ ≫ f) (a : Over.mk t₁ ⟶ V)
      (h₁ : g ≫ pr₁ = a.left) (h₂ : g ≫ pr₂ = t₂) :
      (D.transport t₁ t₂ h a).left = g ≫ γ := by
    have e₁ : g ≫ (pr₁ ≫ V.hom) = t₁ := by
      rw [← Category.assoc, h₁, Over.w a]
      rfl
    cases e₁
    cases h₂
    have ha : (Over.homMk g : Over.mk (g ≫ pr₁ ≫ V.hom) ⟶
        Over.mk (pr₁ ≫ V.hom)) ≫ Over.homMk pr₁ = a := by
      ext
      exact h₁
    rw [← ha]
    exact congrArg (fun a ↦ a.left)
      (D.transport_homMk_comp g (pr₁ ≫ V.hom) pr₂ hpr (Over.homMk pr₁))
  let d : V.left ⟶ P := Limits.pullback.lift (𝟙 _) V.hom (by simp)
  have hd₁ : d ≫ pr₁ = 𝟙 _ := Limits.pullback.lift_fst _ _ _
  have hd₂ : d ≫ pr₂ = V.hom := Limits.pullback.lift_snd _ _ _
  have hdγ : d ≫ γ = 𝟙 _ := by
    have h := hγnat d V.hom V.hom rfl (Over.homMk (𝟙 _)) hd₁ hd₂
    rw [D.transport_self] at h
    exact h.symm
  let P₂ := Limits.pullback (pr₂ ≫ f) f
  let r₁ : P₂ ⟶ P := Limits.pullback.fst _ _
  let r₂ : P₂ ⟶ X := Limits.pullback.snd _ _
  let γ₁ : P₂ ⟶ P := Limits.pullback.lift (r₁ ≫ γ) r₂ (by
    rw [Category.assoc, ← Category.assoc γ, hγv]
    exact Limits.pullback.condition)
  let π₁ : P₂ ⟶ P := Limits.pullback.lift (r₁ ≫ pr₁) r₂ (by
    calc
      (r₁ ≫ pr₁) ≫ V.hom ≫ f = r₁ ≫ pr₂ ≫ f := by
        simp only [Category.assoc] at hpr ⊢
        rw [hpr]
      _ = r₂ ≫ f := Limits.pullback.condition)
  have hγ₁₁ : γ₁ ≫ pr₁ = r₁ ≫ γ := Limits.pullback.lift_fst _ _ _
  have hγ₁₂ : γ₁ ≫ pr₂ = r₂ := Limits.pullback.lift_snd _ _ _
  have hπ₁₁ : π₁ ≫ pr₁ = r₁ ≫ pr₁ := Limits.pullback.lift_fst _ _ _
  have hπ₁₂ : π₁ ≫ pr₂ = r₂ := Limits.pullback.lift_snd _ _ _
  have h₁₂ : (r₁ ≫ pr₁ ≫ V.hom) ≫ f = (r₁ ≫ pr₂) ≫ f := by
    simp only [Category.assoc] at hpr ⊢
    rw [hpr]
  have h₂₃ : (r₁ ≫ pr₂) ≫ f = r₂ ≫ f := by
    rw [Category.assoc]
    exact Limits.pullback.condition
  -- Naturality identifies the two successive transports with the cocycle.
  have hγ₁γ : γ₁ ≫ γ = π₁ ≫ γ := by
    let a : Over.mk (r₁ ≫ pr₁ ≫ V.hom) ⟶ V := Over.homMk (r₁ ≫ pr₁)
    have ht₁ := hγnat r₁ _ _ h₁₂ a rfl rfl
    have ht₂ := hγnat γ₁ _ _ h₂₃ (D.transport _ _ h₁₂ a)
      (hγ₁₁.trans ht₁.symm) hγ₁₂
    have ht₃ := hγnat π₁ _ _ (h₁₂.trans h₂₃) a hπ₁₁ hπ₁₂
    rw [← ht₂, ← ht₃, D.transport_transport]
  -- the rings and their algebra structures
  let R : CommRingCat.{u} := Γ(S, ⊤)
  let A' : CommRingCat.{u} := Γ(X, ⊤)
  let E : CommRingCat.{u} := Γ(V.left, ⊤)
  let _ : Algebra R A' := f.appTop.hom.toAlgebra
  let _ : Algebra A' E := V.hom.appTop.hom.toAlgebra
  let _ : Algebra R E := (V.hom ≫ f).appTop.hom.toAlgebra
  have : IsScalarTower R A' E := IsScalarTower.of_algebraMap_eq fun x ↦ rfl
  have : Flat f := hf
  have hflat : Module.Flat R A' := f.flat_appTop
  -- The affine fibre product has ring of sections `TensorProduct R A' E`.
  have hP := isPushout_appTop_of_flat f (V.hom ≫ f)
  let ξ : TensorProduct R A' E ≃+* Γ(P, ⊤) := hP.tensorEquiv rfl rfl
  have ξ_tmul : ∀ (a : A') (x : E),
      ξ (TensorProduct.tmul R a x) = pr₂.appTop a * pr₁.appTop x :=
    hP.tensorEquiv_tmul rfl rfl
  -- the coaction on `E`
  let δ₀ : E →+* TensorProduct R A' E := ξ.symm.toRingHom.comp γ.appTop.hom
  have δ₀_apply : ∀ x, ξ (δ₀ x) = γ.appTop x := fun x ↦ by
    change ξ (ξ.symm _) = _
    rw [RingEquiv.apply_symm_apply]
  have hγv : ∀ a, γ.appTop (V.hom.appTop a) = pr₂.appTop a := fun a ↦
    congr(((Scheme.Hom.appTop $hγv).hom) a)
  let δ : E →ₐ[A'] TensorProduct R A' E :=
    { δ₀ with
      commutes' := fun a ↦ by
        change δ₀ (algebraMap A' E a) = algebraMap A' (TensorProduct R A' E) a
        apply ξ.injective
        rw [δ₀_apply, Algebra.TensorProduct.algebraMap_apply, ξ_tmul, map_one, mul_one]
        exact hγv a }
  have δ_apply : ∀ x, ξ (δ x) = γ.appTop x := δ₀_apply
  -- the counit condition
  have hmul : ∀ t : TensorProduct R A' E,
      Algebra.TensorProduct.mulMap R A' E t = d.appTop (ξ t) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a x =>
      rw [ξ_tmul, map_mul, Algebra.TensorProduct.mulMap_tmul, Algebra.smul_def]
      have h1 : d.appTop (pr₂.appTop a) = V.hom.appTop a :=
        congr(((Scheme.Hom.appTop $hd₂).hom) a)
      have h2 : d.appTop (pr₁.appTop x) = x :=
        congr(((Scheme.Hom.appTop $hd₁).hom) x)
      rw [h1, h2]
      rfl
    | add s t hs ht => simp only [map_add, hs, ht]
  have hcounit : ∀ x, Algebra.TensorProduct.mulMap R A' E (δ x) = x := fun x ↦ by
    rw [hmul, δ_apply]
    exact congr(((Scheme.Hom.appTop $hdγ).hom) x)
  -- Coassociativity follows from the transport cocycle on `P₂ = P ×_S X`.
  let _ : Algebra R Γ(P, ⊤) := (pr₂ ≫ f).appTop.hom.toAlgebra
  have hP₂ := isPushout_appTop_of_flat f (pr₂ ≫ f)
  let ξ₂ : TensorProduct R A' Γ(P, ⊤) ≃+* Γ(P₂, ⊤) := hP₂.tensorEquiv rfl rfl
  have ξ₂_tmul : ∀ (a : A') (y : Γ(P, ⊤)), ξ₂ (TensorProduct.tmul R a y) =
      (Limits.pullback.snd (pr₂ ≫ f) f).appTop a *
        (Limits.pullback.fst (pr₂ ≫ f) f).appTop y :=
    hP₂.tensorEquiv_tmul rfl rfl
  let ξₐ : TensorProduct R A' E ≃ₐ[R] Γ(P, ⊤) :=
    { ξ with
      commutes' := fun r ↦ by
        change ξ (algebraMap R (TensorProduct R A' E) r) = algebraMap R Γ(P, ⊤) r
        rw [Algebra.TensorProduct.algebraMap_apply, ξ_tmul, map_one, mul_one]
        rfl }
  have ξₐ_apply : ∀ t, ξₐ t = ξ t := fun _ ↦ rfl
  let Θ : TensorProduct R A' (TensorProduct R A' E) →+* Γ(P₂, ⊤) :=
    ξ₂.toRingHom.comp (Algebra.TensorProduct.map (AlgHom.id R A') ξₐ.toAlgHom).toRingHom
  have Θ_inj : Function.Injective Θ := by
    have : ⇑Θ = ξ₂ ∘ (Algebra.TensorProduct.congr (AlgEquiv.refl (R := R) (A₁ := A')) ξₐ) := by
      ext t
      simp [Θ, Algebra.TensorProduct.congr_apply]
    rw [this]
    exact ξ₂.injective.comp
      (Algebra.TensorProduct.congr (AlgEquiv.refl (R := R) (A₁ := A')) ξₐ).injective
  have Θ_tmul : ∀ (a : A') (t : TensorProduct R A' E), Θ (TensorProduct.tmul R a t) =
      (Limits.pullback.snd (pr₂ ≫ f) f).appTop a *
        (Limits.pullback.fst (pr₂ ≫ f) f).appTop (ξ t) := by
    intro a t
    simp [Θ, ξ₂_tmul, ξₐ_apply]
  have hΘδ : ∀ t, Θ (Algebra.TensorProduct.map (AlgHom.id R A') (δ.restrictScalars R) t) =
      γ₁.appTop (ξ t) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a x =>
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.restrictScalars_apply, Θ_tmul,
        ξ_tmul, map_mul, δ_apply]
      congr 1
      · exact (congr(((Scheme.Hom.appTop $hγ₁₂).hom) a)).symm
      · exact (congr(((Scheme.Hom.appTop $hγ₁₁).hom) x)).symm
    | add s t hs ht => simp only [map_add, hs, ht]
  have hΘinc : ∀ t, Θ (Algebra.TensorProduct.map (AlgHom.id R A')
      (Algebra.TensorProduct.includeRight (R := R) (A := A') (B := E)) t) =
      π₁.appTop (ξ t) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a x =>
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.includeRight_apply,
        Θ_tmul, ξ_tmul, ξ_tmul, map_one, one_mul, map_mul]
      congr 1
      · exact (congr(((Scheme.Hom.appTop $hπ₁₂).hom) a)).symm
      · exact (congr(((Scheme.Hom.appTop $hπ₁₁).hom) x)).symm
    | add s t hs ht => simp only [map_add, hs, ht]
  have hcoassoc : ∀ x, Algebra.TensorProduct.map (AlgHom.id R A') (δ.restrictScalars R) (δ x) =
      Algebra.TensorProduct.map (AlgHom.id R A') Algebra.TensorProduct.includeRight (δ x) := by
    intro x
    apply Θ_inj
    rw [hΘδ, hΘinc, δ_apply]
    exact congr(((Scheme.Hom.appTop $hγ₁γ).hom) x)
  -- the descent datum and the descended algebra
  let EDatum : Algebra.DescentDatum R A' E := ⟨δ, hcounit, hcoassoc⟩
  let D₀ : Subalgebra R E := EDatum.descended
  let ε : TensorProduct R A' D₀ ≃ₐ[A'] E := EDatum.descendedEquiv
  have ε_tmul : ∀ (a : A') (x : D₀), ε (TensorProduct.tmul R a x) = a • (x : E) := fun a x ↦ by
    change EDatum.descendedEquiv (TensorProduct.tmul R a x) = _
    rw [EDatum.descendedEquiv_apply, EDatum.descendedMap_tmul]
  -- The descended spectrum and its pullback square over `S`.
  have hpush : IsPushout (CommRingCat.ofHom (algebraMap R A'))
      (CommRingCat.ofHom (algebraMap R D₀)) (CommRingCat.ofHom (algebraMap A' E))
      (CommRingCat.ofHom (algebraMap D₀ E)) := by
    refine (CommRingCat.isPushout_tensorProduct R A' D₀).of_iso (Iso.refl _) (Iso.refl _)
      (Iso.refl _) ε.toRingEquiv.toCommRingCatIso (by simp) (by simp) ?_ ?_
    · ext a
      simp [ε_tmul, Algebra.smul_def]
    · ext x
      simp [ε_tmul]
  have hsq := isPullback_SpecMap_of_isPushout _ _ _ _ hpush
  have hiso : IsPullback X.isoSpec.inv (Spec.map (CommRingCat.ofHom (algebraMap R A')))
      f S.isoSpec.inv :=
    IsPullback.of_horiz_isIso ⟨(Scheme.isoSpec_inv_naturality f).symm⟩
  have hQ := hsq.paste_horiz hiso
  have hjw : V.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap A' E)) ≫ X.isoSpec.inv =
      V.hom := by
    rw [← Category.assoc]
    change V.left.toSpecΓ ≫ Spec.map V.hom.appTop ≫ X.isoSpec.inv = V.hom
    rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc, ← Scheme.isoSpec_hom,
      Iso.hom_inv_id, Category.comp_id]
  let nS : Spec (.of D₀) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap R D₀)) ≫ S.isoSpec.inv
  let q : V.left ⟶ Spec (.of D₀) :=
    V.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap D₀ E))
  have hq : IsPullback V.hom q f nS := by
    have hj : IsPullback V.left.toSpecΓ V.hom
        (Spec.map (CommRingCat.ofHom (algebraMap A' E)) ≫ X.isoSpec.inv) (𝟙 X) :=
      IsPullback.of_horiz_isIso ⟨by simpa using hjw⟩
    simpa [q, nS] using (hj.paste_horiz hQ.flip).flip
  -- Invariant sections make the descended morphism transport invariant.
  refine ⟨Over.mk nS, q, hq.flip, ?_⟩
  intro T f₁ f₂ h a
  let g : T ⟶ P := Limits.pullback.lift a.left f₂ (by
    rw [← Category.assoc, Over.w a]
    exact h)
  have hg₁ : g ≫ pr₁ = a.left := Limits.pullback.lift_fst _ _ _
  have hg₂ : g ≫ pr₂ = f₂ := Limits.pullback.lift_snd _ _ _
  have hga : g ≫ γ = (D.transport f₁ f₂ h a).left :=
    (hγnat g f₁ f₂ h a hg₁ hg₂).symm
  have hinv : γ ≫ q = pr₁ ≫ q := by
    dsimp only [q]
    rw [← Category.assoc, Scheme.toSpecΓ_naturality, ← Category.assoc pr₁,
      Scheme.toSpecΓ_naturality, Category.assoc, Category.assoc,
      ← Spec.map_comp, ← Spec.map_comp]
    congr 2
    ext x
    have hx := EDatum.δ_of_mem_descended x.2
    have he := δ_apply x
    rw [hx, ξ_tmul, map_one, one_mul] at he
    exact he.symm
  rw [← hga, Category.assoc, hinv, ← Category.assoc, hg₁]

end CategoryTheory.Over.DescentDatum
