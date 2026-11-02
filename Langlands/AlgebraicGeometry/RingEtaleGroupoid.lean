import Langlands.AlgebraicGeometry.GroupoidCoactionCore
import Langlands.AlgebraicGeometry.GroupoidCoactionSubmodule

/-! # Affine étale groupoids in ring form without the closed immersion condition

`RingEtaleGroupoid t` is the ring form of an étale equivalence relation on `Spec B` with
relation scheme `Spec C` in which `j = (t, s)` is only required to be a monomorphism: ring
maps out of `C` are determined by their composites with the source and target maps. The
coaction constructions of the Library modules `GroupoidCoactionUniversal`,
`GroupoidCoactionExact`, `GroupoidCoactionCore` and `GroupoidCoactionSubmodule` use the
closed immersion condition only through this uniqueness, so they are repeated here under the
weaker hypothesis.
-/

universe u v

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace Langlands.AlgebraicGeometry

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]

/-- The ring form of an étale equivalence relation on `Spec B` with relation scheme `Spec C`,
source map `Spec (algebraMap B C)` and target map `Spec t`, for which `j = (t, s)` is a
monomorphism: ring maps out of `C` are determined by their composites with `t` and with the
source map. A ring map `φ : C →+* T` is the point `r` with `t r = φ ∘ t` and
`s r = φ ∘ algebraMap B C`. -/
structure RingEtaleGroupoid (t : B →+* C) : Prop where
  /-- `j = (t, s)` is a monomorphism. -/
  hom_ext : ∀ {T : Type u} [CommRing T] {f g : C →+* T}, f.comp t = g.comp t →
    f.comp (algebraMap B C) = g.comp (algebraMap B C) → f = g
  /-- Reflexivity: every pair `(a, a)` is a point of `Spec C`. -/
  refl : ∀ (T : Type u) [CommRing T] (a : B →+* T),
    ∃ φ : C →+* T, φ.comp t = a ∧ φ.comp (algebraMap B C) = a
  /-- Symmetry: with `(t r, s r)` the pair `(s r, t r)` is a point of `Spec C`. -/
  symm : ∀ (T : Type u) [CommRing T] (φ : C →+* T),
    ∃ ψ : C →+* T, ψ.comp t = φ.comp (algebraMap B C) ∧ ψ.comp (algebraMap B C) = φ.comp t
  /-- Transitivity: `(x, y)` and `(y, z)` give `(x, z)`. -/
  trans : ∀ (T : Type u) [CommRing T] (φ ψ : C →+* T),
    φ.comp (algebraMap B C) = ψ.comp t →
      ∃ χ : C →+* T, χ.comp t = φ.comp t ∧ χ.comp (algebraMap B C) = ψ.comp (algebraMap B C)
  /-- The source map is étale. -/
  etale_algebraMap : (algebraMap B C).Etale
  /-- The target map is étale. -/
  etale_t : t.Etale

variable {t : B →+* C}

/-- A ring étale equivalence relation is in particular a ring étale groupoid. -/
theorem RingEtaleEquivalenceRelation.toRingEtaleGroupoid
    (hE : RingEtaleEquivalenceRelation t) : RingEtaleGroupoid t where
  hom_ext ht hs := hE.hom_ext ht hs
  refl := hE.refl
  symm := hE.symm
  trans := hE.trans
  etale_algebraMap := hE.etale_algebraMap
  etale_t := hE.etale_t

namespace RingEtaleGroupoid

open RingEtaleEquivalenceRelation

/-- The source map is flat. -/
theorem flat (hE : RingEtaleGroupoid t) : Module.Flat B C :=
  RingHom.flat_algebraMap_iff.mp
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp hE.etale_algebraMap).1

/-- The identity point of the groupoid. -/
noncomputable def identity (hE : RingEtaleGroupoid t) : C →ₐ[B] B where
  toRingHom := (hE.refl B (RingHom.id B)).choose
  commutes' b := congrArg (fun h : B →+* B => h b)
    (hE.refl B (RingHom.id B)).choose_spec.2

@[simp]
theorem identity_comp_t (hE : RingEtaleGroupoid t) :
    (hE.identity : C →+* B).comp t = RingHom.id B :=
  (hE.refl B (RingHom.id B)).choose_spec.1

/-- The composite of the two universal composable points. -/
noncomputable def composableComposite (hE : RingEtaleGroupoid t) :
    C →ₐ[B] composableRing t where
  toRingHom := (hE.trans (composableRing t) (composableFirst t)
    (composableSecond t) (composable_compat t)).choose
  commutes' b := congrArg (fun h : B →+* composableRing t => h b)
    (hE.trans (composableRing t) (composableFirst t)
      (composableSecond t) (composable_compat t)).choose_spec.2

theorem composableComposite_comp_t (hE : RingEtaleGroupoid t) :
    (hE.composableComposite : C →+* composableRing t).comp t =
      (composableFirst t).comp t :=
  (hE.trans (composableRing t) (composableFirst t)
    (composableSecond t) (composable_compat t)).choose_spec.1

theorem composable_flat (hE : RingEtaleGroupoid t) :
    Module.Flat B (composableRing t) := by
  have hs : (algebraMap B C).Flat :=
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp hE.etale_algebraMap).1
  have hinr : (composableSecondHom t).Flat :=
    CommRingCat.flat.pushout_inr (CommRingCat.ofHom (algebraMap B C))
      (CommRingCat.ofHom t) hs
  exact hs.comp hinr

theorem identity_factor (hE : RingEtaleGroupoid t)
    {T : Type u} [CommRing T] [Algebra B T] (φ : C →ₐ[B] T)
    (hφ : (φ : C →+* T).comp t = algebraMap B T) :
    (Algebra.ofId B T).comp hE.identity = φ := by
  apply AlgHom.coe_ringHom_injective
  apply hE.hom_ext
  · change (algebraMap B T).comp ((hE.identity : C →+* B).comp t) = _
    rw [hE.identity_comp_t, RingHom.comp_id, hφ]
  · ext b
    simp

theorem composableComposite_factor (hE : RingEtaleGroupoid t)
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

variable {M N : Type v} [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]

/-- It suffices to verify the coaction identities at the universal points. -/
noncomputable def coactionOfUniversal (hE : RingEtaleGroupoid t)
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

@[simp]
theorem coactionOfUniversal_coaction (hE : RingEtaleGroupoid t)
    (θ : M →+ C ⊗[B] M) (hθ : ∀ (b : B) (m : M), θ (b • m) = t b • θ m) (hunit) (hcomp) :
    (hE.coactionOfUniversal θ hθ hunit hcomp).coaction = θ :=
  rfl

/-- Transport a coaction through an injective equivariant linear map. -/
noncomputable def coactionOfInjective (hE : RingEtaleGroupoid t)
    (θN : GroupoidCoaction t N) (f : M →ₗ[B] N) (hinj : Function.Injective f)
    (θ : M →+ C ⊗[B] M) (hθ : ∀ (b : B) (m : M), θ (b • m) = t b • θ m)
    (hf : ∀ m : M, θN.coaction (f m) = LinearMap.lTensor C f (θ m)) :
    GroupoidCoaction t M := by
  letI := hE.composable_flat
  refine hE.coactionOfUniversal θ hθ (fun m => ?_) (fun m => ?_)
  · apply Module.Flat.lTensor_preserves_injective_linearMap f hinj
    rw [lTensor_rTensor_commute, ← hf m,
      θN.counit B hE.identity hE.identity_comp_t]
    simp
  · apply Module.Flat.lTensor_preserves_injective_linearMap f hinj
    rw [lTensor_rTensor_commute, ← hf m,
      θN.coassoc _ _ _ _ _ hE.composableComposite_comp_t, hf m]
    exact (coactionCompose_map θ θN.coaction hθ θN.map_smul f hf _ _ _ (θ m)).symm

@[simp]
theorem coactionOfInjective_coaction (hE : RingEtaleGroupoid t)
    (θN : GroupoidCoaction t N) (f : M →ₗ[B] N) (hinj : Function.Injective f)
    (θ : M →+ C ⊗[B] M) (hθ : ∀ (b : B) (m : M), θ (b • m) = t b • θ m)
    (hf : ∀ m : M, θN.coaction (f m) = LinearMap.lTensor C f (θ m)) :
    (hE.coactionOfInjective θN f hinj θ hθ hf).coaction = θ :=
  rfl

open GroupoidCoaction

theorem core_le (hE : RingEtaleGroupoid t)
    (θ : GroupoidCoaction t M) (H : Submodule B M) : core θ H ≤ H := by
  intro m hm
  have hzero := (mem_core_iff θ H m).mp hm
  have h := congrArg (LinearMap.rTensor (M ⧸ H) hE.identity.toLinearMap) hzero
  rw [← lTensor_rTensor_commute, θ.counit B hE.identity hE.identity_comp_t] at h
  have hq := congrArg (TensorProduct.lid B (M ⧸ H)) h
  simpa using hq

/-- The composite of the two points of the pair ring. -/
noncomputable def pairComposite (hE : RingEtaleGroupoid t) : C →ₐ[B] PairRing t where
  toRingHom := (hE.trans (PairRing t) (pairFirst t) (pairSecond t) (pair_compat t)).choose
  commutes' b := congrArg (fun f : B →+* PairRing t => f b)
    (hE.trans (PairRing t) (pairFirst t) (pairSecond t) (pair_compat t)).choose_spec.2

theorem pairComposite_comp_t (hE : RingEtaleGroupoid t) :
    (hE.pairComposite : C →+* PairRing t).comp t = (pairFirst t).comp t :=
  (hE.trans (PairRing t) (pairFirst t) (pairSecond t) (pair_compat t)).choose_spec.1

theorem core_stable (hE : RingEtaleGroupoid t)
    (θ : GroupoidCoaction t M) (H : Submodule B M) (m : core θ H) :
    LinearMap.lTensor C (coreMap θ H) (θ.coaction m) = 0 := by
  apply pairTensorMap_injective t (M ⧸ H)
  rw [map_zero, pairTensorMap_lTensor_coreMap,
    ← θ.coassoc (PairRing t) (pairFirst t) (pairSecond t) hE.pairComposite
      (pair_compat t) hE.pairComposite_comp_t, lTensor_rTensor_commute,
    (mem_core_iff θ H m).mp m.property, map_zero]

/-- Restrict a coaction to its core, using flat tensor-kernel exactness. -/
noncomputable def coreSemilinearMap (hE : RingEtaleGroupoid t)
    (θ : GroupoidCoaction t M) (H : Submodule B M) :
    core θ H →ₛₗ[t] C ⊗[B] core θ H :=
  letI := hE.flat
  (LinearMap.tensorKerEquiv C C (coreMap θ H)).symm.toLinearMap.comp
    ((θ.semilinearMap.domRestrict (core θ H)).codRestrict
      (LinearMap.ker (AlgebraTensorModule.lTensor C C (coreMap θ H)))
      (fun m => hE.core_stable θ H m))

theorem coreSemilinearMap_subtype (hE : RingEtaleGroupoid t)
    (θ : GroupoidCoaction t M) (H : Submodule B M) (m : core θ H) :
    LinearMap.lTensor C (core θ H).subtype (hE.coreSemilinearMap θ H m) =
      θ.coaction m :=
  letI := hE.flat
  LinearMap.lTensor_ker_subtype_tensorKerEquiv_symm C C (coreMap θ H) _

/-- The core inherits a coaction from the ambient module. -/
noncomputable def coreCoaction (hE : RingEtaleGroupoid t)
    (θ : GroupoidCoaction t M) (H : Submodule B M) : GroupoidCoaction t (core θ H) :=
  hE.coactionOfInjective θ (core θ H).subtype (core θ H).subtype_injective
    (hE.coreSemilinearMap θ H).toAddMonoidHom
    (fun b m => (hE.coreSemilinearMap θ H).map_smulₛₗ b m)
    (fun m => (hE.coreSemilinearMap_subtype θ H m).symm)

theorem core_subtype_isHom (hE : RingEtaleGroupoid t)
    (θ : GroupoidCoaction t M) (H : Submodule B M) :
    (hE.coreCoaction θ H).IsHom θ (core θ H).subtype :=
  fun m => (hE.coreSemilinearMap_subtype θ H m).symm

theorem finite_core [IsNoetherianRing B] (hE : RingEtaleGroupoid t)
    (θ : GroupoidCoaction t M) (H : Submodule B M) [Module.Finite B H] :
    Module.Finite B (core θ H) :=
  Module.Finite.of_injective (Submodule.inclusion (hE.core_le θ H))
    (Submodule.inclusion_injective _)

/-- Every element lies in a finite stable submodule (ring form, for affine groupoids, of the
exhaustion in Stacks Lemma 39.15.4, Tag 07TU). -/
theorem exists_finite_stableSubmodule [IsNoetherianRing B] (hE : RingEtaleGroupoid t)
    (θ : GroupoidCoaction t M) (m : M) :
    ∃ H : Submodule B M, Module.Finite B H ∧ m ∈ H ∧ θ.IsStableSubmodule H := by
  obtain ⟨H, hH, hm⟩ := TensorProduct.exists_finite_submodule_right_of_setFinite
    ({θ.coaction m} : Set (C ⊗[B] M)) (Set.finite_singleton _)
  let := hH
  refine ⟨core θ H, hE.finite_core θ H,
    mem_core_of_tensor_range θ H m (hm (Set.mem_singleton _)), fun n => ?_⟩
  exact ⟨hE.coreSemilinearMap θ H n, hE.coreSemilinearMap_subtype θ H n⟩

/-- Restriction of a coaction to a stable submodule. -/
noncomputable def submoduleCoaction (hE : RingEtaleGroupoid t)
    (θ : GroupoidCoaction t M) (N : Submodule B M) (hN : θ.IsStableSubmodule N) :
    GroupoidCoaction t N :=
  letI := hE.flat
  hE.coactionOfInjective θ N.subtype N.subtype_injective
    (submoduleSemilinearMap θ N hN).toAddMonoidHom
    (fun b m => (submoduleSemilinearMap θ N hN).map_smulₛₗ b m)
    (fun m => (submoduleSemilinearMap_subtype θ N hN m).symm)

theorem submoduleCoaction_subtype (hE : RingEtaleGroupoid t)
    (θ : GroupoidCoaction t M) (N : Submodule B M) (hN : θ.IsStableSubmodule N) (m : N) :
    LinearMap.lTensor C N.subtype ((hE.submoduleCoaction θ N hN).coaction m) =
      θ.coaction m :=
  letI := hE.flat
  submoduleSemilinearMap_subtype θ N hN m

end RingEtaleGroupoid

end Langlands.AlgebraicGeometry
