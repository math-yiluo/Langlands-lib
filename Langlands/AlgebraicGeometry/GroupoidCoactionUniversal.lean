import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationComodule
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.RingTheory.RingHom.Flat

/-! # Universal points of an affine ring equivalence relation -/

universe u v

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace Langlands.AlgebraicGeometry

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
variable {t : B →+* C}

namespace RingEtaleEquivalenceRelation

/-- The closed relation is determined by its source and target. -/
lemma hom_ext (hE : RingEtaleEquivalenceRelation t) {T : Type u} [CommRing T]
    {f g : C →+* T} (ht : f.comp t = g.comp t)
    (hs : f.comp (algebraMap B C) = g.comp (algebraMap B C)) : f = g := by
  let K : Subalgebra B C :=
    { f.eqLocus g with
      algebraMap_mem' := fun b => congrArg (fun h : B →+* T => h b) hs }
  have hK : Algebra.adjoin B (Set.range t) ≤ K := by
    apply Algebra.adjoin_le
    rintro c ⟨b, rfl⟩
    exact congrArg (fun h : B →+* T => h b) ht
  rw [hE.adjoin_range_eq_top] at hK
  exact RingHom.ext fun c => hK (show c ∈ (⊤ : Subalgebra B C) from trivial)

/-- The identity point of the relation. -/
noncomputable def identity (hE : RingEtaleEquivalenceRelation t) : C →ₐ[B] B where
  toRingHom := (hE.refl B (RingHom.id B)).choose
  commutes' b := congrArg (fun h : B →+* B => h b)
    (hE.refl B (RingHom.id B)).choose_spec.2

@[simp]
lemma identity_comp_t (hE : RingEtaleEquivalenceRelation t) :
    (hE.identity : C →+* B).comp t = RingHom.id B :=
  (hE.refl B (RingHom.id B)).choose_spec.1

/-- The ring representing two composable points, in the order of `coactionCompose`. -/
noncomputable def composableRing (t : B →+* C) : CommRingCat.{u} :=
  pushout (CommRingCat.ofHom (algebraMap B C)) (CommRingCat.ofHom t)

noncomputable def composableFirst (t : B →+* C) : C →+* composableRing t :=
  (pushout.inl (CommRingCat.ofHom (algebraMap B C)) (CommRingCat.ofHom t)).hom

noncomputable def composableSecondHom (t : B →+* C) : C →+* composableRing t :=
  (pushout.inr (CommRingCat.ofHom (algebraMap B C)) (CommRingCat.ofHom t)).hom

noncomputable instance composableAlgebra (t : B →+* C) : Algebra B (composableRing t) :=
  ((composableSecondHom t).comp (algebraMap B C)).toAlgebra

noncomputable def composableSecond (t : B →+* C) : C →ₐ[B] composableRing t where
  toRingHom := composableSecondHom t
  commutes' _ := rfl

lemma composable_compat (t : B →+* C) :
    (composableFirst t).comp (algebraMap B C) =
      (composableSecond t : C →+* composableRing t).comp t :=
  congrArg CommRingCat.Hom.hom (pushout.condition
    (f := CommRingCat.ofHom (algebraMap B C)) (g := CommRingCat.ofHom t))

/-- The composite of the two universal composable points. -/
noncomputable def composableComposite (hE : RingEtaleEquivalenceRelation t) :
    C →ₐ[B] composableRing t where
  toRingHom := (hE.trans (composableRing t) (composableFirst t)
    (composableSecond t) (composable_compat t)).choose
  commutes' b := congrArg (fun h : B →+* composableRing t => h b)
    (hE.trans (composableRing t) (composableFirst t)
      (composableSecond t) (composable_compat t)).choose_spec.2

lemma composableComposite_comp_t (hE : RingEtaleEquivalenceRelation t) :
    (hE.composableComposite : C →+* composableRing t).comp t =
      (composableFirst t).comp t :=
  (hE.trans (composableRing t) (composableFirst t)
    (composableSecond t) (composable_compat t)).choose_spec.1

lemma composable_flat (hE : RingEtaleEquivalenceRelation t) :
    Module.Flat B (composableRing t) := by
  have hs : (algebraMap B C).Flat :=
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp
      hE.etale_algebraMap).1
  have hinr : (composableSecondHom t).Flat :=
    CommRingCat.flat.pushout_inr (CommRingCat.ofHom (algebraMap B C))
      (CommRingCat.ofHom t) hs
  exact hs.comp hinr

/-- Every pair of composable points is a specialization of the universal pair. -/
noncomputable def composableLift {T : Type u} [CommRing T] [Algebra B T]
    (φ₁ : C →+* T) (φ₂ : C →ₐ[B] T)
    (h : φ₁.comp (algebraMap B C) = (φ₂ : C →+* T).comp t) :
    composableRing t →ₐ[B] T where
  toRingHom := (pushout.desc (CommRingCat.ofHom φ₁) (CommRingCat.ofHom φ₂.toRingHom)
    (congrArg CommRingCat.ofHom h)).hom
  commutes' b := by
    have heq := pushout.inr_desc
      (f := CommRingCat.ofHom (algebraMap B C)) (g := CommRingCat.ofHom t)
      (CommRingCat.ofHom φ₁) (CommRingCat.ofHom φ₂.toRingHom)
      (congrArg CommRingCat.ofHom h)
    exact (congrArg (fun f : CommRingCat.of C ⟶ CommRingCat.of T =>
      f (algebraMap B C b)) heq).trans (φ₂.commutes b)

@[simp]
lemma composableLift_first {T : Type u} [CommRing T] [Algebra B T]
    (φ₁ : C →+* T) (φ₂ : C →ₐ[B] T)
    (h : φ₁.comp (algebraMap B C) = (φ₂ : C →+* T).comp t) :
    (composableLift φ₁ φ₂ h : composableRing t →+* T).comp (composableFirst t) = φ₁ := by
  exact congrArg (fun f : CommRingCat.of C ⟶ CommRingCat.of T => f.hom)
    (pushout.inl_desc (f := CommRingCat.ofHom (algebraMap B C))
      (g := CommRingCat.ofHom t) (CommRingCat.ofHom φ₁)
      (CommRingCat.ofHom φ₂.toRingHom) (congrArg CommRingCat.ofHom h))

@[simp]
lemma composableLift_second {T : Type u} [CommRing T] [Algebra B T]
    (φ₁ : C →+* T) (φ₂ : C →ₐ[B] T)
    (h : φ₁.comp (algebraMap B C) = (φ₂ : C →+* T).comp t) :
    (composableLift φ₁ φ₂ h).comp (composableSecond t) = φ₂ := by
  apply AlgHom.coe_ringHom_injective
  exact congrArg (fun f : CommRingCat.of C ⟶ CommRingCat.of T => f.hom)
    (pushout.inr_desc (f := CommRingCat.ofHom (algebraMap B C))
      (g := CommRingCat.ofHom t) (CommRingCat.ofHom φ₁)
      (CommRingCat.ofHom φ₂.toRingHom) (congrArg CommRingCat.ofHom h))

lemma identity_factor (hE : RingEtaleEquivalenceRelation t)
    {T : Type u} [CommRing T] [Algebra B T] (φ : C →ₐ[B] T)
    (hφ : (φ : C →+* T).comp t = algebraMap B T) :
    (Algebra.ofId B T).comp hE.identity = φ := by
  apply AlgHom.coe_ringHom_injective
  apply hE.hom_ext
  · change (algebraMap B T).comp ((hE.identity : C →+* B).comp t) = _
    rw [hE.identity_comp_t, RingHom.comp_id, hφ]
  · ext b
    simp

lemma composableComposite_factor (hE : RingEtaleEquivalenceRelation t)
    {T : Type u} [CommRing T] [Algebra B T]
    (φ₁ : C →+* T) (φ₂ φ₃ : C →ₐ[B] T)
    (h : φ₁.comp (algebraMap B C) = (φ₂ : C →+* T).comp t)
    (h₃ : (φ₃ : C →+* T).comp t = φ₁.comp t) :
    (composableLift φ₁ φ₂ h).comp hE.composableComposite = φ₃ := by
  apply AlgHom.coe_ringHom_injective
  apply hE.hom_ext
  · change (composableLift φ₁ φ₂ h : composableRing t →+* T).comp
      ((hE.composableComposite : C →+* composableRing t).comp t) = _
    rw [hE.composableComposite_comp_t, ← RingHom.comp_assoc, composableLift_first, h₃]
  · ext b
    simp

end RingEtaleEquivalenceRelation

section Naturality

variable {M : Type v} [AddCommGroup M] [Module B M]
variable {D T : Type u} [CommRing D] [Algebra B D] [CommRing T] [Algebra B T]

lemma rTensor_algHom_smul (ψ : D →ₐ[B] T) (d : D) (x : D ⊗[B] M) :
    LinearMap.rTensor M ψ.toLinearMap (d • x) =
      ψ d • LinearMap.rTensor M ψ.toLinearMap x := by
  induction x with
  | tmul d' m => simp [smul_tmul', smul_eq_mul]
  | add x y hx hy => simp [smul_add, hx, hy]

lemma rTensor_algHom_comp (ψ : D →ₐ[B] T) (φ : C →ₐ[B] D) (x : C ⊗[B] M) :
    LinearMap.rTensor M ψ.toLinearMap (LinearMap.rTensor M φ.toLinearMap x) =
      LinearMap.rTensor M (ψ.comp φ).toLinearMap x := by
  induction x <;> simp_all

lemma coactionCompose_naturality (θ : M →+ C ⊗[B] M)
    (hθ : ∀ (b : B) (m : M), θ (b • m) = t b • θ m)
    (ψ : D →ₐ[B] T) (φ₁ : C →+* D) (φ₂ : C →ₐ[B] D)
    (φ₁' : C →+* T) (φ₂' : C →ₐ[B] T)
    (h : φ₁.comp (algebraMap B C) = (φ₂ : C →+* D).comp t)
    (h' : φ₁'.comp (algebraMap B C) = (φ₂' : C →+* T).comp t)
    (h₁ : ψ.toRingHom.comp φ₁ = φ₁') (h₂ : ψ.comp φ₂ = φ₂') (x : C ⊗[B] M) :
    LinearMap.rTensor M ψ.toLinearMap (coactionCompose t M θ hθ φ₁ φ₂ h x) =
      coactionCompose t M θ hθ φ₁' φ₂' h' x := by
  subst φ₁'
  subst φ₂'
  induction x with
  | tmul c m =>
    change LinearMap.rTensor M ψ.toLinearMap
      (φ₁ c • LinearMap.rTensor M φ₂.toLinearMap (θ m)) =
      ψ (φ₁ c) • LinearMap.rTensor M (ψ.comp φ₂).toLinearMap (θ m)
    rw [rTensor_algHom_smul, rTensor_algHom_comp]
  | add x y hx hy => simp [hx, hy]

end Naturality

namespace GroupoidCoaction

open RingEtaleEquivalenceRelation

/-- It suffices to verify the coaction identities at the universal points. -/
noncomputable def ofUniversal (hE : RingEtaleEquivalenceRelation t)
    {M : Type v} [AddCommGroup M] [Module B M]
    (θ : M →+ C ⊗[B] M) (hθ : ∀ (b : B) (m : M), θ (b • m) = t b • θ m)
    (hunit : ∀ m : M, LinearMap.rTensor M hE.identity.toLinearMap (θ m) = (1 : B) ⊗ₜ m)
    (hcomp : ∀ m : M,
      LinearMap.rTensor M hE.composableComposite.toLinearMap (θ m) =
        coactionCompose t M θ hθ (composableFirst t) (composableSecond t)
          (composable_compat t) (θ m)) : GroupoidCoaction t M where
  coaction := θ
  map_smul := hθ
  counit T _ _ φ hφ m := by
    rw [← hE.identity_factor φ hφ, ← rTensor_algHom_comp, hunit]
    simp
  coassoc T _ _ φ₁ φ₂ φ₃ h h₃ m := by
    rw [← hE.composableComposite_factor φ₁ φ₂ φ₃ h h₃,
      ← rTensor_algHom_comp, hcomp]
    exact coactionCompose_naturality θ hθ (composableLift φ₁ φ₂ h)
      (composableFirst t) (composableSecond t) φ₁ φ₂ (composable_compat t) h
      (composableLift_first φ₁ φ₂ h) (composableLift_second φ₁ φ₂ h) (θ m)

end GroupoidCoaction

end Langlands.AlgebraicGeometry
