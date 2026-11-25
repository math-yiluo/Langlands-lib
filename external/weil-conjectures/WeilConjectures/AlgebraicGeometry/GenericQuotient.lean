/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Mathlib.RingTheory.Nilpotent.Lemmas
public import WeilConjectures.RingTheory.Invariant.Etale

/-!
# Generic quotients of affine schemes by an automorphism of finite order

For a `k`-algebra `C`, `AlgebraicGeometry.specAlgOver C` is `Spec C` as a scheme over `Spec k`,
with `AlgebraicGeometry.specAlgOverMap` and `AlgebraicGeometry.specAlgOverIso` the morphisms and
isomorphisms induced by `k`-algebra maps.

The main result is the **generic quotient** of an affine scheme `Spec B` of finite type over a
field by an automorphism `Spec σ` of finite order (SGA 1, Exposé V, Prop. 1.1 and Cor. 2.4):
there are a nonempty `σ`-stable basic open `U = Spec B_b`, its reduction `Z = U_red`, and a finite
étale morphism `π : Z ⟶ V` to an affine scheme of finite type `V`, invariant under the
automorphism of `Z` induced by `σ` (`AlgebraicGeometry.exists_isFinite_etale_specAlgOver`). Here
`V = Spec R_c`, for a finitely generated subalgebra `R` of invariants of `A = B_red` over which
`A` is finite and generically étale
(`Algebra.IsInvariant.exists_subalgebra_basicOpen_subset_etaleLocus`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- `Spec C` as a scheme over `Spec k`, for a `k`-algebra `C`. -/
noncomputable def specAlgOver (C : Type u) [CommRing C] [Algebra k C] : Over (Spec (.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k C)))

variable {C D E : Type u} [CommRing C] [CommRing D] [CommRing E] [Algebra k C] [Algebra k D]
  [Algebra k E]

instance [Algebra.FiniteType k C] : LocallyOfFiniteType (specAlgOver (k := k) C).hom := by
  dsimp only [specAlgOver, Over.mk_hom]
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), CommRingCat.hom_ofHom]
  exact RingHom.finiteType_algebraMap.2 inferInstance

instance : QuasiCompact (specAlgOver (k := k) C).hom := by
  dsimp only [specAlgOver, Over.mk_hom]
  have : IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap k C))) := isAffineHom_of_isAffine _
  infer_instance

instance : IsSeparated (specAlgOver (k := k) C).hom := by
  dsimp only [specAlgOver, Over.mk_hom]; infer_instance

instance : IsAffine (specAlgOver (k := k) C).left := by
  dsimp only [specAlgOver, Over.mk_left]; infer_instance

/-- `Spec` of a `k`-algebra map, as a morphism of schemes over `Spec k`. -/
noncomputable def specAlgOverMap (f : C →ₐ[k] D) : specAlgOver (k := k) D ⟶ specAlgOver C :=
  Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
    dsimp only [specAlgOver, Over.mk_hom]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun r ↦ f.commutes r)

lemma specAlgOverMap_left (f : C →ₐ[k] D) :
    (specAlgOverMap f).left = Spec.map (CommRingCat.ofHom f.toRingHom) :=
  rfl

@[simp]
lemma specAlgOverMap_id : specAlgOverMap (AlgHom.id k C) = 𝟙 _ := by
  ext1
  exact Spec.map_id _

@[reassoc]
lemma specAlgOverMap_comp (f : C →ₐ[k] D) (g : D →ₐ[k] E) :
    specAlgOverMap (g.comp f) = specAlgOverMap g ≫ specAlgOverMap f := by
  ext1
  exact Spec.map_comp (CommRingCat.ofHom f.toRingHom) (CommRingCat.ofHom g.toRingHom)

/-- `Spec` of a `k`-algebra isomorphism. -/
@[simps]
noncomputable def specAlgOverIso (e : C ≃ₐ[k] D) : specAlgOver (k := k) D ≅ specAlgOver C where
  hom := specAlgOverMap e.toAlgHom
  inv := specAlgOverMap e.symm.toAlgHom
  hom_inv_id := by
    rw [← specAlgOverMap_comp]
    convert specAlgOverMap_id
    ext x; simp
  inv_hom_id := by
    rw [← specAlgOverMap_comp]
    convert specAlgOverMap_id
    ext x; simp

end AlgebraicGeometry

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- **Generic quotient, affine case** (SGA 1, Exposé V, Prop. 1.1 and Cor. 2.4). Let `σ` be an
automorphism of finite order of a nonzero finitely generated `k`-algebra `B`. There are a nonempty
open subscheme `j : U ⟶ Spec B`, stable under `Spec σ`, a surjective closed immersion `i : Z ⟶ U`
(the reduction of `U`), stable under the induced automorphism `e_Z`, and a finite étale morphism
`π : Z ⟶ V` to an affine scheme of finite type over `k` with `e_Z ≫ π = π`. -/
theorem exists_isFinite_etale_specAlgOver (B : Type u) [CommRing B] [Algebra k B]
    [Algebra.FiniteType k B] [Nontrivial B] (σ : B ≃ₐ[k] B) {m : ℕ} (hσ : σ ^ (m + 1) = 1) :
    ∃ (U : Over (Spec (.of k))) (_ : LocallyOfFiniteType U.hom) (_ : QuasiCompact U.hom)
      (_ : IsSeparated U.hom) (eU : U ≅ U) (j : U ⟶ specAlgOver B) (_ : IsOpenImmersion j.left)
      (_ : eU.hom ≫ j = j ≫ (specAlgOverIso σ).hom) (Z : Over (Spec (.of k)))
      (_ : LocallyOfFiniteType Z.hom) (_ : QuasiCompact Z.hom) (_ : IsSeparated Z.hom)
      (eZ : Z ≅ Z) (i : Z ⟶ U) (_ : IsClosedImmersion i.left) (_ : eZ.hom ≫ i = i ≫ eU.hom)
      (V : Over (Spec (.of k))) (_ : IsAffine V.left) (_ : LocallyOfFiniteType V.hom)
      (π : Z ⟶ V) (_ : IsFinite π.left) (_ : Etale π.left),
      Nonempty U.left ∧ Function.Surjective i.left.base ∧ eZ.hom ≫ π = π := by
  classical
  -- the reduced quotient `A = B ⧸ nil(B)` with the automorphism induced by `σ`
  let A := B ⧸ nilradical B
  let σA : A ≃ₐ[k] A := Ideal.quotientEquivAlg _ _ σ (nilradical_eq_map_ringEquiv σ.toRingEquiv)
  have hσAmk : ∀ n : ℕ, ∀ x : B, (σA ^ n) (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ ((σ ^ n) x) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro x
      rw [pow_succ, pow_succ, AlgEquiv.mul_apply, AlgEquiv.mul_apply,
        show σA (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (σ x) from rfl, ih]
  have hσA : IsOfFinOrder σA := by
    refine isOfFinOrder_iff_pow_eq_one.2 ⟨m + 1, m.succ_pos, ?_⟩
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hσAmk, hσ]
    rfl
  have : _root_.IsReduced A :=
    (Ideal.isRadical_iff_quotient_reduced _).1 (Ideal.radical_isRadical ⊥)
  have : Nontrivial A := Ideal.Quotient.nontrivial_iff.2 (fun h ↦ by
    have : (1 : B) ∈ nilradical B := h ▸ Submodule.mem_top
    exact not_isNilpotent_one (mem_nilradical.1 this))
  obtain ⟨R, hRσ, hRft, hRfin, c, hc, hcE⟩ :=
    Algebra.IsInvariant.exists_subalgebra_basicOpen_subset_etaleLocus σA hσA
  -- an invariant lift `b` of `c^(m+1)`
  have hσAc : ∀ n : ℕ, (σA ^ n) (c : A) = c := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, AlgEquiv.mul_apply, hRσ _ c.2, ih]
  obtain ⟨b₀, hb₀⟩ := Ideal.Quotient.mk_surjective (c : A)
  set b : B := ∏ i ∈ Finset.range (m + 1), (σ ^ i) b₀ with hb_def
  have hb : σ b = b := by
    have h : ∀ i, σ ((σ ^ i) b₀) = (σ ^ (i + 1)) b₀ := fun i ↦ by
      rw [pow_succ', AlgEquiv.mul_apply]
    rw [hb_def, map_prod]
    simp only [h]
    rw [Finset.prod_range_succ, Finset.prod_range_succ' (fun i ↦ (σ ^ i) b₀), hσ, pow_zero]
  set c' : R := c ^ (m + 1) with hc'_def
  have hbc : Ideal.Quotient.mk (nilradical B) b = (c' : A) := by
    rw [hb_def, map_prod]
    simp only [← hσAmk, hb₀, hσAc, Finset.prod_const, Finset.card_range]
    rw [hc'_def, SubmonoidClass.coe_pow]
  have hc' : ¬ IsNilpotent (c' : A) := fun h ↦ hc (by
    rw [hc'_def, SubmonoidClass.coe_pow] at h
    exact h.of_pow)
  have hbn : ¬ IsNilpotent b := fun h ↦ hc' (hbc ▸ h.map (Ideal.Quotient.mk _))
  have hσAc' : σA (c' : A) = c' := hRσ _ c'.2
  -- the localizations
  have := hRft
  let Bb := Localization.Away b
  let Ac := Localization.Away (c' : A)
  let Rc := Localization.Away c'
  let σb : Bb ≃ₐ[k] Bb := Localization.awayAlgEquiv σ b hb
  let σAc : Ac ≃ₐ[k] Ac := Localization.awayAlgEquiv σA (c' : A) hσAc'
  have : IsLocalization.Away (Ideal.Quotient.mkₐ k (nilradical B) b) Ac := by
    change IsLocalization.Away (Ideal.Quotient.mk (nilradical B) b) Ac
    rw [hbc]; infer_instance
  have : IsLocalization.Away (R.val c') Ac := inferInstanceAs (IsLocalization.Away (c' : A) Ac)
  let ψ : Bb →ₐ[k] Ac := IsLocalization.Away.mapₐ Bb Ac (Ideal.Quotient.mkₐ k (nilradical B)) b
  let π : Rc →ₐ[k] Ac := IsLocalization.Away.mapₐ Rc Ac R.val c'
  have hψ : Function.Surjective ψ :=
    IsLocalization.Away.mapₐ_surjective_of_surjective b Ideal.Quotient.mk_surjective
  have hψker : RingHom.ker ψ ≤ nilradical Bb := by
    refine IsLocalization.Away.ker_mapₐ_le_nilradical _ ?_ b
    intro x hx
    rwa [RingHom.mem_ker, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
  -- `ψ ∘ σ_b = σ_A ∘ ψ` and `σ_A ∘ π = π`
  have hψσ : ψ.comp σb.toAlgHom = σAc.toAlgHom.comp ψ := by
    refine AlgHom.toRingHom_injective (IsLocalization.ringHom_ext (Submonoid.powers b) ?_)
    ext x
    simp only [ψ, σb, σAc, AlgHom.coe_comp, AlgHom.toRingHom_eq_coe,
      RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, AlgEquiv.coe_toAlgHom,
      IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map, IsLocalization.map_eq]
    rw [Localization.awayAlgEquiv_algebraMap, Localization.awayAlgEquiv_algebraMap,
      IsLocalization.map_eq]
    rfl
  have hπσ : σAc.toAlgHom.comp π = π := by
    refine AlgHom.toRingHom_injective (IsLocalization.ringHom_ext (Submonoid.powers c') ?_)
    ext x
    simp only [π, σAc, AlgHom.coe_comp, AlgHom.toRingHom_eq_coe,
      RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, AlgEquiv.coe_toAlgHom,
      IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map, IsLocalization.map_eq]
    rw [Localization.awayAlgEquiv_algebraMap]
    exact congrArg _ (hRσ _ x.2)
  -- `π` is finite and étale
  have : IsLocalization.Away ((algebraMap R A) c') Ac :=
    inferInstanceAs (IsLocalization.Away (c' : A) Ac)
  have hπfin : π.toRingHom.Finite :=
    RingHom.localization_away_map_finite R A Rc Ac (algebraMap R A) c'
      (RingHom.finite_algebraMap.2 hRfin)
  have hπet : π.toRingHom.Etale := by
    let := π.toRingHom.toAlgebra
    have : IsScalarTower R Rc Ac := IsScalarTower.of_algebraMap_eq fun r ↦ by
      change _ = IsLocalization.Away.map Rc Ac (algebraMap R A) c' (algebraMap R Rc r)
      rw [IsLocalization.Away.map, IsLocalization.map_eq, IsScalarTower.algebraMap_apply R A Ac]
    have : IsLocalization ((Submonoid.powers c').map (algebraMap R A)) Ac := by
      rw [Submonoid.map_powers]
      exact inferInstanceAs (IsLocalization.Away (c' : A) Ac)
    have : Algebra.FormallyEtale R Ac := by
      have hsub : ↑(PrimeSpectrum.basicOpen (c' : A)) ⊆ Algebra.etaleLocus R A := by
        rw [hc'_def, SubmonoidClass.coe_pow, PrimeSpectrum.basicOpen_pow _ _ m.succ_pos]
        exact hcE
      convert (Algebra.basicOpen_subset_etaleLocus_iff (R := R) (A := A)).1 hsub using 2
      exact Algebra.algebra_ext _ _ fun r ↦ (IsScalarTower.algebraMap_apply R A Ac r).symm
    have : Algebra.FormallyEtale Rc Ac :=
      Algebra.FormallyEtale.localization_base (Submonoid.powers c')
    have : Module.Finite Rc Ac := hπfin
    have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
    have : IsNoetherianRing Rc :=
      IsLocalization.isNoetherianRing (Submonoid.powers c') Rc inferInstance
    have : Algebra.FinitePresentation Rc Ac :=
      Algebra.FinitePresentation.of_finiteType.1 inferInstance
    exact ⟨inferInstance, inferInstance⟩
  have hBb : Nontrivial Bb := by
    refine ⟨⟨0, 1, fun h ↦ hbn ?_⟩⟩
    have : algebraMap B Bb 1 = 0 := by rw [map_one]; exact h.symm
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers b) Bb 1).1 this
    exact ⟨n, by simpa using hn⟩
  refine ⟨specAlgOver Bb, inferInstance, inferInstance, inferInstance, specAlgOverIso σb,
    specAlgOverMap (IsScalarTower.toAlgHom k B Bb), ?_, ?_, specAlgOver Ac, inferInstance,
    inferInstance, inferInstance, specAlgOverIso σAc, specAlgOverMap ψ, ?_, ?_, specAlgOver Rc,
    inferInstance, inferInstance, specAlgOverMap π, ?_, ?_, ?_, ?_, ?_⟩
  · exact inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B Bb))))
  · rw [specAlgOverIso_hom, specAlgOverIso_hom, ← specAlgOverMap_comp, ← specAlgOverMap_comp]
    congr 1
    ext x
    exact Localization.awayAlgEquiv_algebraMap σ b hb x
  · exact IsClosedImmersion.spec_of_surjective _ hψ
  · rw [specAlgOverIso_hom, specAlgOverIso_hom, ← specAlgOverMap_comp, ← specAlgOverMap_comp]
    exact congrArg specAlgOverMap hψσ.symm
  · rw [specAlgOverMap_left, IsFinite.SpecMap_iff]
    exact hπfin
  · rw [specAlgOverMap_left, HasRingHomProperty.Spec_iff (P := @Etale)]
    exact hπet
  · exact inferInstanceAs (Nonempty (PrimeSpectrum Bb))
  · rw [specAlgOverMap_left, Spec.map_base]
    change Function.Surjective (PrimeSpectrum.comap ψ.toRingHom)
    rw [← Set.range_eq_univ, range_comap_of_surjective _ _ hψ,
      PrimeSpectrum.zeroLocus_eq_univ_iff]
    exact hψker
  · rw [specAlgOverIso_hom, ← specAlgOverMap_comp, hπσ]

end AlgebraicGeometry
