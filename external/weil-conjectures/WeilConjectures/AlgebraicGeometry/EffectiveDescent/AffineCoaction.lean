/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.GlobalSections
public import WeilConjectures.Mathlib.RingTheory.Flat.DescentAlgebra

/-!
# Affine flat descent in coaction form

Let `p : X ⟶ Y` be a flat morphism of affine schemes and `v : V ⟶ X` a morphism from an affine
scheme. A *coaction* on `V` relative to `p` is a morphism `γ : V ×_Y X ⟶ V` over the second
projection, satisfying the counit identity (`γ (x, v x) = x`) and the coassociativity identity
(`γ (γ (x, s), t) = γ (x, t)`). Taking global sections, `γ` becomes a descent datum on the ring
`Γ(V)` relative to `Γ(Y) → Γ(X)` in the sense of `Algebra.DescentDatum`, and flat descent of
algebras (`Algebra.DescentDatum.descendedEquiv`) shows that `V` is the base change of an affine
`Y`-scheme `N` along `p`, through a morphism `q : V ⟶ N` invariant under `γ`
(`AlgebraicGeometry.exists_isPullback_of_coaction`).

The argument follows `AlgebraicGeometry.Scheme.Hom.EtaleDescent.exists_affine_descent`.
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

namespace AlgebraicGeometry

variable {X Y V : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine V] (p : X ⟶ Y) [Flat p]
  (v : V ⟶ X)

/-- The diagonal-type morphism `V ⟶ V ×_Y X`, `x ↦ (x, v x)`. -/
noncomputable abbrev coactionUnit : V ⟶ pullback (v ≫ p) p :=
  pullback.lift (𝟙 V) v (by simp)

/-- The morphism `(V ×_Y X) ×_Y X ⟶ V ×_Y X` forgetting the middle factor. -/
noncomputable abbrev coactionForget :
    pullback (pullback.snd (v ≫ p) p ≫ p) p ⟶ pullback (v ≫ p) p :=
  pullback.map _ _ _ _ (pullback.fst _ _) (𝟙 X) (𝟙 Y) (by simp [pullback.condition]) (by simp)

/-- The morphism `(V ×_Y X) ×_Y X ⟶ V ×_Y X` applying the coaction `γ` to the first two
factors. -/
noncomputable abbrev coactionMap (γ : pullback (v ≫ p) p ⟶ V)
    (hγv : γ ≫ v = pullback.snd _ _) :
    pullback (pullback.snd (v ≫ p) p ≫ p) p ⟶ pullback (v ≫ p) p :=
  pullback.map _ _ _ _ γ (𝟙 X) (𝟙 Y) (by rw [reassoc_of% hγv]; simp) (by simp)

/-- **Affine flat descent in coaction form.** Let `p : X ⟶ Y` be a flat morphism of affine
schemes and `v : V ⟶ X` with `V` affine. A coaction `γ : V ×_Y X ⟶ V` over the second projection
satisfying the counit and coassociativity identities exhibits `V` as the base change along `p`
of a `Y`-scheme `N`, through a morphism `q : V ⟶ N` with `γ ≫ q = pr₁ ≫ q`. -/
theorem exists_isPullback_of_coaction (γ : pullback (v ≫ p) p ⟶ V)
    (hγv : γ ≫ v = pullback.snd _ _) (hd : coactionUnit p v ≫ γ = 𝟙 V)
    (hγ₁ : coactionMap p v γ hγv ≫ γ = coactionForget p v ≫ γ) :
    ∃ (N : Scheme.{u}) (_ : IsAffine N) (nY : N ⟶ Y) (q : V ⟶ N), IsPullback q v nY p ∧
      γ ≫ q = pullback.fst _ _ ≫ q := by
  -- the rings and their algebra structures
  let R : CommRingCat.{u} := Γ(Y, ⊤)
  let A' : CommRingCat.{u} := Γ(X, ⊤)
  let E : CommRingCat.{u} := Γ(V, ⊤)
  let _ : Algebra R A' := p.appTop.hom.toAlgebra
  let _ : Algebra A' E := v.appTop.hom.toAlgebra
  let _ : Algebra R E := (v ≫ p).appTop.hom.toAlgebra
  have : IsScalarTower R A' E := IsScalarTower.of_algebraMap_eq fun x ↦ rfl
  have hflat : Module.Flat R A' := p.flat_appTop
  -- flat base change of global sections for `P = V ×_Y X`
  have hP := isPushout_appTop_of_flat p (v ≫ p)
  let ξ : A' ⊗[R] E ≃+* Γ(pullback (v ≫ p) p, ⊤) := hP.tensorEquiv rfl rfl
  have ξ_tmul : ∀ (a : A') (x : E),
      ξ (a ⊗ₜ x) = (pullback.snd (v ≫ p) p).appTop a * (pullback.fst (v ≫ p) p).appTop x :=
    hP.tensorEquiv_tmul rfl rfl
  -- the coaction on `E`
  let δ₀ : E →+* A' ⊗[R] E := ξ.symm.toRingHom.comp γ.appTop.hom
  have δ₀_apply : ∀ x, ξ (δ₀ x) = γ.appTop x := fun x ↦ by
    change ξ (ξ.symm _) = _
    rw [RingEquiv.apply_symm_apply]
  have hγv' : ∀ a, γ.appTop (v.appTop a) = (pullback.snd (v ≫ p) p).appTop a := fun a ↦
    congr(((Scheme.Hom.appTop $hγv).hom) a)
  let δ : E →ₐ[A'] A' ⊗[R] E :=
    { δ₀ with
      commutes' := fun a ↦ by
        change δ₀ (algebraMap A' E a) = algebraMap A' (A' ⊗[R] E) a
        apply ξ.injective
        rw [δ₀_apply, Algebra.TensorProduct.algebraMap_apply, ξ_tmul, map_one, mul_one]
        exact hγv' a }
  have δ_apply : ∀ x, ξ (δ x) = γ.appTop x := δ₀_apply
  -- the counit condition
  have hd₁ : coactionUnit p v ≫ pullback.fst (v ≫ p) p = 𝟙 _ := pullback.lift_fst _ _ _
  have hd₂ : coactionUnit p v ≫ pullback.snd (v ≫ p) p = v := pullback.lift_snd _ _ _
  have hmul : ∀ t : A' ⊗[R] E,
      Algebra.TensorProduct.mulMap R A' E t = (coactionUnit p v).appTop (ξ t) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a x =>
      rw [ξ_tmul, map_mul, Algebra.TensorProduct.mulMap_tmul, Algebra.smul_def]
      have h1 : (coactionUnit p v).appTop ((pullback.snd (v ≫ p) p).appTop a) = v.appTop a :=
        congr(((Scheme.Hom.appTop $hd₂).hom) a)
      have h2 : (coactionUnit p v).appTop ((pullback.fst (v ≫ p) p).appTop x) = x :=
        congr(((Scheme.Hom.appTop $hd₁).hom) x)
      rw [h1, h2]
      rfl
    | add s t hs ht => simp only [map_add, hs, ht]
  have hcounit : ∀ x, Algebra.TensorProduct.mulMap R A' E (δ x) = x := fun x ↦ by
    rw [hmul, δ_apply]
    exact congr(((Scheme.Hom.appTop $hd).hom) x)
  -- the coassociativity condition, via `P₂ = P ×_Y X`
  let _ : Algebra R Γ(pullback (v ≫ p) p, ⊤) :=
    (pullback.snd (v ≫ p) p ≫ p).appTop.hom.toAlgebra
  have hP₂ := isPushout_appTop_of_flat p (pullback.snd (v ≫ p) p ≫ p)
  let ξ₂ : A' ⊗[R] Γ(pullback (v ≫ p) p, ⊤) ≃+*
      Γ(pullback (pullback.snd (v ≫ p) p ≫ p) p, ⊤) := hP₂.tensorEquiv rfl rfl
  have ξ₂_tmul : ∀ (a : A') (y : Γ(pullback (v ≫ p) p, ⊤)), ξ₂ (a ⊗ₜ y) =
      (pullback.snd (pullback.snd (v ≫ p) p ≫ p) p).appTop a *
        (pullback.fst (pullback.snd (v ≫ p) p ≫ p) p).appTop y :=
    hP₂.tensorEquiv_tmul rfl rfl
  let ξₐ : A' ⊗[R] E ≃ₐ[R] Γ(pullback (v ≫ p) p, ⊤) :=
    { ξ with
      commutes' := fun r ↦ by
        change ξ (algebraMap R (A' ⊗[R] E) r) = algebraMap R Γ(pullback (v ≫ p) p, ⊤) r
        rw [Algebra.TensorProduct.algebraMap_apply, ξ_tmul, map_one, mul_one]
        rfl }
  have ξₐ_apply : ∀ t, ξₐ t = ξ t := fun _ ↦ rfl
  let Θ : A' ⊗[R] (A' ⊗[R] E) →+* Γ(pullback (pullback.snd (v ≫ p) p ≫ p) p, ⊤) :=
    ξ₂.toRingHom.comp (Algebra.TensorProduct.map (AlgHom.id R A') ξₐ.toAlgHom).toRingHom
  have Θ_inj : Function.Injective Θ := by
    have : ⇑Θ = ξ₂ ∘ (Algebra.TensorProduct.congr (AlgEquiv.refl (R := R) (A₁ := A')) ξₐ) := by
      ext t
      simp [Θ, Algebra.TensorProduct.congr_apply]
    rw [this]
    exact ξ₂.injective.comp
      (Algebra.TensorProduct.congr (AlgEquiv.refl (R := R) (A₁ := A')) ξₐ).injective
  have Θ_tmul : ∀ (a : A') (t : A' ⊗[R] E), Θ (a ⊗ₜ t) =
      (pullback.snd (pullback.snd (v ≫ p) p ≫ p) p).appTop a *
        (pullback.fst (pullback.snd (v ≫ p) p ≫ p) p).appTop (ξ t) := by
    intro a t
    simp [Θ, ξ₂_tmul, ξₐ_apply]
  have hγ₁₂ : coactionMap p v γ hγv ≫ pullback.snd (v ≫ p) p =
      pullback.snd (pullback.snd (v ≫ p) p ≫ p) p := by simp
  have hγ₁₁ : coactionMap p v γ hγv ≫ pullback.fst (v ≫ p) p = pullback.fst _ _ ≫ γ := by simp
  have hπ₁₂ : coactionForget p v ≫ pullback.snd (v ≫ p) p =
      pullback.snd (pullback.snd (v ≫ p) p ≫ p) p := by simp
  have hπ₁₁ : coactionForget p v ≫ pullback.fst (v ≫ p) p =
      pullback.fst _ _ ≫ pullback.fst (v ≫ p) p := by simp
  have hΘδ : ∀ t, Θ (Algebra.TensorProduct.map (AlgHom.id R A') (δ.restrictScalars R) t) =
      (coactionMap p v γ hγv).appTop (ξ t) := by
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
      (coactionForget p v).appTop (ξ t) := by
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
    exact congr(((Scheme.Hom.appTop $hγ₁).hom) x)
  -- the descent datum and the descended algebra
  let D : Algebra.DescentDatum R A' E := ⟨δ, hcounit, hcoassoc⟩
  let D₀ : Subalgebra R E := D.descended
  let ε : A' ⊗[R] D₀ ≃ₐ[A'] E := D.descendedEquiv
  have ε_tmul : ∀ (a : A') (x : D₀), ε (a ⊗ₜ x) = a • (x : E) := fun a x ↦ by
    change D.descendedEquiv (a ⊗ₜ x) = _
    rw [D.descendedEquiv_apply, D.descendedMap_tmul]
  -- the affine scheme `N = Spec D₀` and the pullback square `Spec E = N ×_Y X`
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
      p Y.isoSpec.inv :=
    IsPullback.of_horiz_isIso ⟨(Scheme.isoSpec_inv_naturality p).symm⟩
  have hQ := hsq.paste_horiz hiso
  have hjw : V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap A' E)) ≫ X.isoSpec.inv =
      v := by
    rw [← Category.assoc]
    change V.toSpecΓ ≫ Spec.map v.appTop ≫ X.isoSpec.inv = v
    rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc, ← Scheme.isoSpec_hom,
      Iso.hom_inv_id, Category.comp_id]
  have hV : IsPullback V.toSpecΓ v
      (Spec.map (CommRingCat.ofHom (algebraMap A' E)) ≫ X.isoSpec.inv) (𝟙 X) :=
    IsPullback.of_horiz_isIso ⟨by rw [hjw, Category.comp_id]⟩
  refine ⟨Spec (.of D₀), inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap R D₀)) ≫ Y.isoSpec.inv,
    V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap D₀ E)), ?_, ?_⟩
  · simpa using hV.paste_horiz hQ.flip
  rw [← Category.assoc, Scheme.toSpecΓ_naturality, ← Category.assoc (pullback.fst _ _),
    Scheme.toSpecΓ_naturality, Category.assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  ext x
  have hx := D.δ_of_mem_descended x.2
  have := δ_apply x
  rw [hx, ξ_tmul, map_one, one_mul] at this
  exact this.symm

end AlgebraicGeometry
