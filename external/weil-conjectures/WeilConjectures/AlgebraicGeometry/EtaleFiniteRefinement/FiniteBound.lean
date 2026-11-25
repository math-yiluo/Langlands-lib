/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.Mathlib.FieldTheory.Fixed
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement.GeometricLifts

/-!
# Finite morphisms have boundedly many geometric lifts

A finite morphism `π : Y ⟶ T` to a quasi-compact scheme has a uniform bound on the number of
lifts of field-valued points of `T`: over an affine open `Spec R ⊆ T` with preimage `Spec A`,
the lifts of a `K`-point are `R`-algebra maps `A ⟶ K`, and by Dedekind's independence of
characters there are at most as many of them as generators of the `R`-module `A`.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.exists_hasAtMostGeometricLifts_of_isFinite`.
- `AlgebraicGeometry.Scheme.Hom.HasAtMostGeometricLifts.comp_of_mono`.
-/

@[expose] public section

universe u

open CategoryTheory IsLocalRing


namespace AlgebraicGeometry

variable {U Y T : Scheme.{u}}

lemma Scheme.Hom.HasAtMostGeometricLifts.comp_of_mono {π : Y ⟶ T} {d : ℕ}
    (h : π.HasAtMostGeometricLifts d) (j : U ⟶ Y) [Mono j] :
    (j ≫ π).HasAtMostGeometricLifts d := by
  intro K _ _ σ x hx hinj
  refine h K σ (fun i ↦ x i ≫ j) (fun i ↦ by rw [Category.assoc, hx]) fun i₁ i₂ e ↦ hinj ?_
  exact (cancel_mono j).1 e

/-- Over an affine open of the base, a finite morphism has boundedly many lifts of
field-valued points. -/
lemma Scheme.Hom.exists_forall_not_injective_lifts_of_isFinite (π : Y ⟶ T) [IsFinite π]
    (W : T.affineOpens) :
    ∃ n : ℕ, ∀ (K : Type u) [Field K] (σ : Spec (.of K) ⟶ T),
      σ (closedPoint K) ∈ (W : T.Opens) → ∀ x : Fin (n + 1) → (Spec (.of K) ⟶ Y),
        (∀ i, x i ≫ π = σ) → ¬ Function.Injective x := by
  have : IsAffine (W : T.Opens).toScheme := W.2
  obtain ⟨hA, hfin⟩ :=
    (HasAffineProperty.iff_of_isAffine (P := @IsFinite) (f := π ∣_ (W : T.Opens))).mp inferInstance
  let R := Γ((W : T.Opens).toScheme, ⊤)
  let A := Γ((π ⁻¹ᵁ (W : T.Opens)).toScheme, ⊤)
  let : Algebra R A := (π ∣_ (W : T.Opens)).appTop.hom.toAlgebra
  have : Module.Finite R A := hfin
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := A)
  refine ⟨n, fun K _ σ hσ x hx hinj ↦ ?_⟩
  have hσW : Set.range σ ⊆ Set.range (W : T.Opens).ι := by
    rintro _ ⟨w, rfl⟩
    rw [Subsingleton.elim w (closedPoint K), Scheme.Opens.range_ι]
    exact hσ
  let σ' := IsOpenImmersion.lift (W : T.Opens).ι σ hσW
  have hxW (i : Fin (n + 1)) : Set.range (x i) ⊆ Set.range (π ⁻¹ᵁ (W : T.Opens)).ι := by
    rintro _ ⟨w, rfl⟩
    rw [Subsingleton.elim w (closedPoint K), Scheme.Opens.range_ι]
    change π (x i (closedPoint K)) ∈ (W : T.Opens)
    rw [← Scheme.Hom.comp_apply, hx i]
    exact hσ
  let x' (i : Fin (n + 1)) := IsOpenImmersion.lift _ (x i) (hxW i)
  have hx' (i : Fin (n + 1)) : x' i ≫ π ∣_ (W : T.Opens) = σ' := by
    rw [← cancel_mono (W : T.Opens).ι, Category.assoc, morphismRestrict_ι,
      IsOpenImmersion.lift_fac_assoc, IsOpenImmersion.lift_fac, hx i]
  let e := (Scheme.ΓSpecIso (.of K)).hom
  let : Algebra R K := (σ'.appTop ≫ e).hom.toAlgebra
  let ψ (i : Fin (n + 1)) : A →ₐ[R] K :=
    { ((x' i).appTop ≫ e).hom with
      commutes' r := by
        change ((π ∣_ (W : T.Opens)).appTop ≫ (x' i).appTop ≫ e).hom r = (σ'.appTop ≫ e).hom r
        rw [← Category.assoc, ← Scheme.Hom.comp_appTop, hx'] }
  refine AlgHom.not_injective_of_span_eq_top s hs ψ fun i₁ i₂ hψ ↦ hinj ?_
  have : x' i₁ = x' i₂ := by
    refine ext_of_isAffine ((cancel_mono e).1 (CommRingCat.hom_ext ?_))
    exact congr_arg (fun φ : A →ₐ[R] K ↦ (φ : A →+* K)) hψ
  rw [← IsOpenImmersion.lift_fac _ (x i₁) (hxW i₁), ← IsOpenImmersion.lift_fac _ (x i₂) (hxW i₂)]
  exact congr($this ≫ _)

/-- **A finite morphism has boundedly many geometric lifts.** If `π : Y ⟶ T` is finite and `T`
is quasi-compact, there is a `d` such that no separably closed point of `T` has `d + 1`
distinct lifts along `π`. -/
theorem Scheme.Hom.exists_hasAtMostGeometricLifts_of_isFinite (π : Y ⟶ T) [IsFinite π]
    [CompactSpace T] : ∃ d, π.HasAtMostGeometricLifts d := by
  classical
  choose n hn using π.exists_forall_not_injective_lifts_of_isFinite
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun W : T.affineOpens ↦ (W : Set T))
    (fun W ↦ W.1.2) fun t _ ↦ by
      obtain ⟨_, ⟨W, hW, rfl⟩, htW, -⟩ :=
        T.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ t) isOpen_univ
      exact Set.mem_iUnion.mpr ⟨⟨W, hW⟩, htW⟩
  refine ⟨∑ W ∈ s, n W, fun K _ _ σ x hx hinj ↦ ?_⟩
  obtain ⟨W, hWs, hW⟩ : ∃ W ∈ s, σ (closedPoint K) ∈ (W : Set T) := by
    simpa using hs (Set.mem_univ (σ (closedPoint K)))
  have hle : n W + 1 ≤ ∑ W ∈ s, n W + 1 := by
    have := Finset.single_le_sum (f := n) (fun _ _ ↦ Nat.zero_le _) hWs
    omega
  exact hn W K σ hW (x ∘ Fin.castLE hle) (fun i ↦ hx _) (hinj.comp (Fin.castLE_injective hle))

end AlgebraicGeometry
