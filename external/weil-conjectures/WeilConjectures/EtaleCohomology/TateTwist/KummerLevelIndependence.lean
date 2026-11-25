/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.TateTwist.KummerClass

/-!
# The finite-level twist does not depend on the Kummer level

Blueprint `sk-def-purity-conv`: the finite-level twist `A(1) = μ_{ℓ^N} ⊗ A` of a finite
coefficient ring `A` is defined with any `N ≥ 1` such that `ℓ^N A = 0`, and does not depend on
the choice of `N`. In this repository `A(1)` is built with `N` minimal, `ℓ^N` being the
characteristic `n` of `A` (`AlgebraicGeometry.Etale.tateTwistSheaf`, `≅ μₙ ⊗ A` by
`AlgebraicGeometry.Etale.tateTwistSheafOneIso`). For every multiple `m = n d` of `n` which is
invertible on `X`, the power map `μ_m ⟶ μ_n`, `u ↦ u^d`
(`AlgebraicGeometry.Scheme.rootsOfUnityPow`), becomes an isomorphism after extending the
coefficients to `A` (`AlgebraicGeometry.Etale.isIso_extendScalars_map_rootsOfUnityPow`), so that
`μ_m ⊗ A ≅ A(1)` (`AlgebraicGeometry.Etale.extendScalarsRootsOfUnityIsoTateTwistSheaf`).

## Proof

All maps are induced by the power maps of `𝔾ₘ`. The square

```
μ_{nd} ──u ↦ u^d──▶ μ_n
  │                   │
  ▼                   ▼
 𝔾ₘ ─────u ↦ u^d───▶ 𝔾ₘ
```

is cartesian, and `u ↦ u^d` is an epimorphism of étale sheaves when `d` is invertible (the
Kummer sequence), so `p : μ_{nd} ⟶ μ_n` is an epimorphism, with kernel `μ_d ⟶ μ_{nd}`. The
composite `μ_{nd} ⟶ μ_d ⟶ μ_{nd}` of `u ↦ uⁿ` (again an epimorphism) and the inclusion is
multiplication by `n`, which vanishes after extending the coefficients to `A`; hence so does the
inclusion, and by right exactness of the extension of scalars `A ⊗ p` is a monomorphism, as well
as an epimorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

variable {X : Scheme.{u}}

lemma nsmul_id_comp_nsmul_id {C : Type*} [Category C] [Preadditive C] (G : C) (a b : ℕ) :
    (a • 𝟙 G) ≫ (b • 𝟙 G) = (b * a) • 𝟙 G := by
  rw [Preadditive.nsmul_comp, Category.id_comp, mul_nsmul]

variable (X) in
/-- The inclusion `μₐ ⟶ 𝔾ₘ`. -/
noncomputable def rootsOfUnityι (a : ℕ) : X.rootsOfUnitySheaf a ⟶ X.gmSheaf :=
  kernel.ι (a • 𝟙 X.gmSheaf)

instance (a : ℕ) : Mono (X.rootsOfUnityι a) :=
  inferInstanceAs (Mono (kernel.ι _))

@[reassoc (attr := simp)]
lemma rootsOfUnityι_nsmul (a : ℕ) : X.rootsOfUnityι a ≫ (a • 𝟙 X.gmSheaf) = 0 :=
  kernel.condition _

/-- A morphism to `𝔾ₘ` killed by `a` factors through `μₐ`. -/
noncomputable def rootsOfUnityLift {T : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (a : ℕ) (t : T ⟶ X.gmSheaf) (ht : t ≫ (a • 𝟙 X.gmSheaf) = 0) : T ⟶ X.rootsOfUnitySheaf a :=
  kernel.lift _ t ht

@[reassoc (attr := simp)]
lemma rootsOfUnityLift_ι {T : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (a : ℕ) (t : T ⟶ X.gmSheaf) (ht : t ≫ (a • 𝟙 X.gmSheaf) = 0) :
    rootsOfUnityLift a t ht ≫ X.rootsOfUnityι a = t :=
  kernel.lift_ι _ _ _

/-- The power map `μ_c ⟶ μ_a`, `u ↦ u^b`, for `c = a b`. -/
noncomputable def rootsOfUnityPow (a b c : ℕ) (h : c = a * b) :
    X.rootsOfUnitySheaf c ⟶ X.rootsOfUnitySheaf a :=
  rootsOfUnityLift a (X.rootsOfUnityι c ≫ (b • 𝟙 X.gmSheaf)) (by
    rw [Category.assoc, nsmul_id_comp_nsmul_id, ← h, rootsOfUnityι_nsmul])

@[reassoc (attr := simp)]
lemma rootsOfUnityPow_ι (a b c : ℕ) (h : c = a * b) :
    rootsOfUnityPow (X := X) a b c h ≫ X.rootsOfUnityι a =
      X.rootsOfUnityι c ≫ (b • 𝟙 X.gmSheaf) :=
  rootsOfUnityLift_ι _ _ _

/-- The square `μ_{ab} ⟶ μ_a`, `𝔾ₘ ⟶ 𝔾ₘ` of `b`-th power maps is cartesian. -/
lemma isPullback_rootsOfUnityPow (a b c : ℕ) (h : c = a * b) :
    IsPullback (rootsOfUnityPow (X := X) a b c h) (X.rootsOfUnityι c)
      (X.rootsOfUnityι a) (b • 𝟙 X.gmSheaf) := by
  refine ⟨⟨rootsOfUnityPow_ι a b c h⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s ↦ rootsOfUnityLift c s.snd ?_) (fun s ↦ ?_) (fun s ↦ rootsOfUnityLift_ι _ _ _)
    (fun s m h₁ h₂ ↦ ?_)⟩⟩
  · rw [h, ← nsmul_id_comp_nsmul_id, ← Category.assoc, ← s.condition,
      Category.assoc, rootsOfUnityι_nsmul, comp_zero]
  · rw [← cancel_mono (X.rootsOfUnityι a), Category.assoc, rootsOfUnityPow_ι,
      rootsOfUnityLift_ι_assoc, s.condition]
  · rw [← cancel_mono (X.rootsOfUnityι c), rootsOfUnityLift_ι]
    exact h₂

/-- The power map `μ_{ab} ⟶ μ_a`, `u ↦ u^b`, is an epimorphism of étale sheaves when `b` is
invertible on `X`: it is the base change of the epimorphism `u ↦ u^b` of `𝔾ₘ`. -/
lemma epi_rootsOfUnityPow (a b c : ℕ) (h : c = a * b) (hb : IsUnit (b : Γ(X, ⊤))) :
    Epi (rootsOfUnityPow (X := X) a b c h) := by
  have := X.isLocallySurjective_nsmul_gmSheaf b hb
  have : Epi (b • 𝟙 X.gmSheaf) := Sheaf.epi_of_isLocallySurjective _
  exact Abelian.epi_fst_of_isLimit _ _ (isPullback_rootsOfUnityPow a b c h).isLimit

/-- The inclusion `μ_b ⟶ μ_c` for `c = a b`. -/
noncomputable def rootsOfUnityIncl (a b c : ℕ) (h : c = a * b) :
    X.rootsOfUnitySheaf b ⟶ X.rootsOfUnitySheaf c :=
  rootsOfUnityLift c (X.rootsOfUnityι b) (by
    rw [h, ← nsmul_id_comp_nsmul_id, rootsOfUnityι_nsmul_assoc, zero_comp])

@[reassoc (attr := simp)]
lemma rootsOfUnityIncl_ι (a b c : ℕ) (h : c = a * b) :
    rootsOfUnityIncl (X := X) a b c h ≫ X.rootsOfUnityι c = X.rootsOfUnityι b :=
  rootsOfUnityLift_ι _ _ _

/-- `μ_b ⟶ μ_{ab} ⟶ μ_a` is exact: `μ_b` is the kernel of the power map `u ↦ u^b`. -/
lemma exact_rootsOfUnityIncl_rootsOfUnityPow (a b c : ℕ) (h : c = a * b) :
    (ShortComplex.mk (rootsOfUnityIncl (X := X) a b c h) (rootsOfUnityPow a b c h)
      (by rw [← cancel_mono (X.rootsOfUnityι a), Category.assoc, rootsOfUnityPow_ι,
        rootsOfUnityIncl_ι_assoc, rootsOfUnityι_nsmul, zero_comp])).Exact := by
  refine ShortComplex.exact_of_f_is_kernel _ (KernelFork.IsLimit.ofι _ _
    (fun t ht ↦ rootsOfUnityLift b (t ≫ X.rootsOfUnityι c) ?_) (fun t ht ↦ ?_)
    (fun t ht m hm ↦ ?_))
  · have := ht =≫ X.rootsOfUnityι a
    rwa [Category.assoc, rootsOfUnityPow_ι, zero_comp, ← Category.assoc] at this
  · rw [← cancel_mono (X.rootsOfUnityι c), Category.assoc, rootsOfUnityIncl_ι,
      rootsOfUnityLift_ι]
  · rw [← cancel_mono (X.rootsOfUnityι b), rootsOfUnityLift_ι, ← hm, Category.assoc,
      rootsOfUnityIncl_ι]

/-- The composite of `μ_{ab} ⟶ μ_b`, `u ↦ uᵃ`, and the inclusion `μ_b ⟶ μ_{ab}` is
multiplication by `a`. -/
lemma rootsOfUnityPow_comp_rootsOfUnityIncl (a b c : ℕ) (h : c = a * b) (h' : c = b * a) :
    rootsOfUnityPow (X := X) b a c h' ≫ rootsOfUnityIncl a b c h =
      a • 𝟙 (X.rootsOfUnitySheaf c) := by
  rw [← cancel_mono (X.rootsOfUnityι c), Category.assoc, rootsOfUnityIncl_ι, rootsOfUnityPow_ι,
    Preadditive.nsmul_comp, Category.id_comp, Preadditive.comp_nsmul, Category.comp_id]

end Scheme

namespace Etale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] {X : Scheme.{u}}

lemma sheaf_nsmul_id_eq_zero_of_natCast_eq_zero {n : ℕ} (hn : (n : Λ) = 0)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) : n • 𝟙 M = 0 := by
  ext U x
  change ((n • 𝟙 M).hom.app U).hom x = 0
  have e : (n • 𝟙 M).hom = n • 𝟙 M.obj :=
    (sheafToPresheaf _ _).map_nsmul (f := 𝟙 M) (n := n)
  rw [e, NatTrans.app_nsmul, NatTrans.id_app, ModuleCat.hom_nsmul, LinearMap.smul_apply,
    ModuleCat.hom_id, LinearMap.id_coe, id_eq, ← Nat.cast_smul_eq_nsmul Λ, hn, zero_smul]

/-- For a ring `Λ` in which `n` vanishes and `d` invertible on `X`, the power map
`μ_{nd} ⟶ μ_n`, `u ↦ u^d`, becomes an isomorphism after extending the coefficients to `Λ`. -/
theorem isIso_extendScalars_map_rootsOfUnityPow (n d : ℕ) (hn : (n : Λ) = 0)
    (hnd : IsUnit ((n * d : ℕ) : Γ(X, ⊤))) :
    IsIso ((extendScalars Λ X).map (rootsOfUnityPow n d (n * d) rfl)) := by
  have hd : IsUnit (d : Γ(X, ⊤)) := isUnit_of_mul_isUnit_right (by simpa using hnd)
  have hn' : IsUnit (n : Γ(X, ⊤)) := isUnit_of_mul_isUnit_left (by simpa using hnd)
  let F := extendScalars Λ X
  have := epi_rootsOfUnityPow (X := X) n d (n * d) rfl hd
  have hq := epi_rootsOfUnityPow (X := X) d n (n * d) (mul_comm _ _) hn'
  -- `F` kills the inclusion `μ_d ⟶ μ_{nd}`
  have h0 : F.map (rootsOfUnityIncl (X := X) n d (n * d) rfl) = 0 := by
    rw [← cancel_epi (F.map (rootsOfUnityPow d n (n * d) (mul_comm _ _))), ← F.map_comp,
      rootsOfUnityPow_comp_rootsOfUnityIncl, Functor.map_nsmul, CategoryTheory.Functor.map_id,
      comp_zero]
    exact sheaf_nsmul_id_eq_zero_of_natCast_eq_zero Λ hn _
  have hex := ShortComplex.Exact.map_of_epi_of_preservesCokernel
    (exact_rootsOfUnityIncl_rootsOfUnityPow (X := X) n d (n * d) rfl) F inferInstance inferInstance
  have : Mono (F.map (rootsOfUnityPow n d (n * d) rfl)) := hex.mono_g h0
  exact isIso_of_mono_of_epi _

/-- Blueprint `sk-def-purity-conv`: Purity conventions and the rank-one datum

*The finite-level twist does not depend on the Kummer level.* Let `Λ` be a ring of
characteristic `n ≠ 0` (for `Λ = A_{E,n}`, `n = ℓ^N` with `N` minimal) and `X` a scheme on which
`n` is invertible. For every `m` with `m Λ = 0` (that is, `n ∣ m`; for instance `m = ℓ^{N'}`
with `ℓ^{N'} A = 0`) which is invertible on `X`, the power map `μ_m ⟶ μ_n`, `u ↦ u^{m/n}`,
induces an isomorphism `μ_m ⊗ Λ ≅ μ_n ⊗ Λ = Λ(1)`
(`AlgebraicGeometry.Etale.tateTwistSheafOneIso`): the twist `μ_{ℓ^{N'}} ⊗ Λ` is the same for
every admissible `N'`. The tensor product is over `ℤ`, which for sheaves killed by `m` is the
tensor product over `ℤ/m`. -/
noncomputable def extendScalarsRootsOfUnityIsoTateTwistSheaf [NeZero (ringChar Λ)]
    [HasInvertibleExponent Λ X] (m : ℕ) (hm : (m : Λ) = 0) (hu : IsUnit (m : Γ(X, ⊤))) :
    (extendScalars Λ X).obj (X.rootsOfUnitySheaf m) ≅ tateTwistSheaf Λ X 1 :=
  have hd : ringChar Λ ∣ m := (ringChar.spec Λ m).1 hm
  have hm' : m = ringChar Λ * (m / ringChar Λ) := (Nat.mul_div_cancel' hd).symm
  have := isIso_extendScalars_map_rootsOfUnityPow Λ (X := X) (ringChar Λ) (m / ringChar Λ)
    (ringChar.Nat.cast_ringChar) (by rw [← hm']; exact hu)
  (extendScalars Λ X).mapIso (eqToIso (by rw [← hm'])) ≪≫
    asIso ((extendScalars Λ X).map
      (rootsOfUnityPow (ringChar Λ) (m / ringChar Λ) (ringChar Λ * (m / ringChar Λ)) rfl)) ≪≫
    (tateTwistSheafOneIso X Λ).symm

end Etale

end AlgebraicGeometry
