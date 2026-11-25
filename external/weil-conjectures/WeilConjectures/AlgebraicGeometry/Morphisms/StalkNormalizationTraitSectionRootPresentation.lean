/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

public import Mathlib.RingTheory.RingHom.Flat

public import Mathlib.RingTheory.AdjoinRoot

import WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionLocalizedRootChart

/-!
# Root-algebra presentation along a transverse trait section

## References

* Stacks Project, Tags 0EYH and 0EYI, proof preceding parts (1) and (2)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem root_local {R : Type u} [CommRing R] [IsLocalRing R]
    (f : R) (e : ℕ) (he : 0 < e) (hf : f ∈ IsLocalRing.maximalIdeal R)
    (P : Ideal (AdjoinRoot ((Polynomial.X : Polynomial R) ^ e - Polynomial.C f)))
    (hP : P.IsMaximal) :
    IsLocalRing (AdjoinRoot ((Polynomial.X : Polynomial R) ^ e - Polynomial.C f)) := by
  let p := (Polynomial.X : Polynomial R) ^ e - Polynomial.C f
  let D := AdjoinRoot p
  let ρ := AdjoinRoot.of p
  let t := AdjoinRoot.root p
  let : Module.Finite R D := (Polynomial.monic_X_pow_sub_C f he.ne').finite_adjoinRoot
  have hrel : t ^ e = ρ f := by
    have h := AdjoinRoot.eval₂_root p
    simpa only [p, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, sub_eq_zero] using h
  have hmem (M : Ideal D) (hM : M.IsMaximal) (q : Polynomial R) :
      AdjoinRoot.mk p q ∈ M ↔ q.coeff 0 ∈ IsLocalRing.maximalIdeal R := by
    let := hM
    have hc : M.comap ρ = IsLocalRing.maximalIdeal R := by
      have hm := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) M
      exact IsLocalRing.eq_maximalIdeal hm
    have ht : t ∈ M := by
      apply hM.isPrime.mem_of_pow_mem e
      rw [hrel]
      change f ∈ M.comap ρ
      rwa [hc]
    obtain ⟨q', hq⟩ := Polynomial.X_dvd_sub_C (p := q)
    have hdecomp : AdjoinRoot.mk p q = ρ (q.coeff 0) + t * AdjoinRoot.mk p q' := by
      have h := congrArg (AdjoinRoot.mk p) hq
      simp only [map_sub, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h
      exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
    rw [hdecomp, Ideal.add_mem_iff_left _ (M.mul_mem_right _ ht)]
    change q.coeff 0 ∈ M.comap ρ ↔ _
    rw [hc]
  apply IsLocalRing.of_unique_max_ideal
  refine ⟨P, hP, ?_⟩
  intro M hM
  ext z
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective (g := p) z
  exact (hmem M hM q).trans (hmem P hP q).symm

/-- The geometric normal form, retaining the actual local root algebra and a uniformizer
of the auxiliary section trait. No maximal-ideal formula for the root algebra and no
integer-valued valuation are asserted here. -/
theorem GaloisCover.stalk_normalization_trait_section_root_presentation {S C : Scheme.{u}}
    [IsNoetherian S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c] [GeometricallyConnected c]
    (σ : S ⟶ C) (hσ : σ ≫ c = 𝟙 S)
    (G : Type (u + 1)) [Group G] [Finite G]
    (hG : IsUnit (Nat.card G : Γ(S, ⊤)))
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c)
    (sη : Spec S.functionField ⟶ Cη)
    (hsj : sη ≫ j = S.fromSpecStalk (genericPoint S) ≫ σ)
    (Z : GaloisCover G Cη)
    (U : S.Opens)
    (jU : Cη ⟶ (c ⁻¹ᵁ U).toScheme) (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (ψ : Z.P ⟶ PA.obj.left) (hjU : jU ≫ (c ⁻¹ᵁ U).ι = j)
    (hψ : IsPullback ψ Z.π PA.obj.hom jU)
    (s : S) (hs : s ∉ U)
    (hmin : ∀ t : S, t ⤳ s → t ∉ U → t = s)
    (hdvr : IsDiscreteValuationRing (S.presheaf.stalk s)) :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    let a := S.fromSpecStalk s
    let n := pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization (pullback.fst c a)
    let τ : Spec (S.presheaf.stalk s) ⟶ pullback c a :=
      pullback.lift (a ≫ σ) (𝟙 _) (by simp [Category.assoc, hσ])
    IsFinite n → ∀ x : (pullback (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
      (pullback.fst c a) : Scheme.{u}),
      n x = τ (IsLocalRing.closedPoint (S.presheaf.stalk s)) →
      let B := (pullback (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
        (pullback.fst c a)).presheaf.stalk x
      let J := (IsLocalRing.maximalIdeal ((pullback c a).presheaf.stalk (n x))).map
        (n.stalkMap x).hom
      ∃ (R : CommRingCat.{u}) (_ : IsLocalRing R) (f : R) (e : ℕ),
        0 < e ∧ f ∈ IsLocalRing.maximalIdeal R ∧
        let p := (Polynomial.X : Polynomial R) ^ e - Polynomial.C f
        let D := AdjoinRoot p
        ∃ (_ : IsLocalRing D) (β : B →+* D),
          IsLocalHom β ∧ β.Flat ∧ IsLocalHom (AdjoinRoot.of p) ∧
          J.map β = (IsLocalRing.maximalIdeal R).map (AdjoinRoot.of p) ∧
          ∃ (A : CommRingCat.{u}) (_ : IsDomain A) (_ : IsDiscreteValuationRing A)
            (K : Type u) (_ : Field K) (_ : Algebra A K) (_ : IsFractionRing A K)
            (ϖ : A) (π : Kˣ) (b : Spec (CommRingCat.of K) ⟶ Spec S.functionField),
            Irreducible ϖ ∧ (π : K) = algebraMap A K ϖ ∧
            ∃ g : Spec (CommRingCat.of
                (AdjoinRoot ((Polynomial.X : Polynomial K) ^ e - Polynomial.C (π : K)))) ⟶
                pullback Z.π (b ≫ sη),
              IsOpenImmersion g ∧
              g ≫ pullback.snd Z.π (b ≫ sη) =
                Spec.map (CommRingCat.ofHom (algebraMap K
                  (AdjoinRoot ((Polynomial.X : Polynomial K) ^ e -
                    Polynomial.C (π : K))))) := by
  let : IsFinite PA.obj.hom := PA.property
  let : QuasiCompact (c ⁻¹ᵁ U).ι :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
      (inferInstance : QuasiCompact U.ι)
  dsimp only
  intro hn x hx
  have hchart := GaloisCover.stalk_normalization_trait_section_localized_root_chart
      (S := S) (C := C) (Cη := Cη)
      c σ hσ G hG q j hCη sη hsj Z U jU PA ψ hjU hψ s hs hmin hdvr
  dsimp only at hchart
  have hchartx := hchart hn x hx
  obtain ⟨R, hR, f, e, he, hf, P, hP, β, hβlocal, hβflat, hJ, hsection⟩ := hchartx
  obtain ⟨A, hA, hAtrait, K, hK, hAK, hfrac, ϖ, π, b, hϖ, hπ, g, hg, hw⟩ := hsection
  let := hR
  let p := (Polynomial.X : Polynomial R) ^ e - Polynomial.C f
  let D := AdjoinRoot p
  let : P.IsMaximal := hP
  let : P.IsPrime := hP.isPrime
  let : IsLocalRing D := root_local f e he hf P hP
  have hPmax : P = IsLocalRing.maximalIdeal D := IsLocalRing.eq_maximalIdeal hP
  have hunit : P.primeCompl ≤ IsUnit.submonoid D := by
    intro z hz
    change IsUnit z
    have hz' : z ∉ IsLocalRing.maximalIdeal D := hPmax ▸ hz
    exact not_not.mp hz'
  let θ : Localization.AtPrime P ≃ₐ[D] D :=
    (IsLocalization.atUnits D P.primeCompl (S := Localization.AtPrime P) hunit).symm
  have hθ : θ.toRingHom.comp (algebraMap D (Localization.AtPrime P)) = RingHom.id D := by
    apply RingHom.ext
    intro z
    exact θ.commutes z
  let := hβlocal
  let : IsLocalHom θ.toRingHom := IsLocalHom.of_surjective _ θ.surjective
  let β' := θ.toRingHom.comp β
  let : Module.Finite R D := (Polynomial.monic_X_pow_sub_C f he.ne').finite_adjoinRoot
  have hlocal : IsLocalHom (AdjoinRoot.of p) := by
    have hc : (IsLocalRing.maximalIdeal D).comap (AdjoinRoot.of p) =
        IsLocalRing.maximalIdeal R := by
      exact IsLocalRing.eq_maximalIdeal
        (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R)
          (IsLocalRing.maximalIdeal D))
    exact ((IsLocalRing.local_hom_TFAE _).out 5 1).mp hc
  let := hA
  let := hAtrait
  let := hK
  let := hAK
  let := hfrac
  refine ⟨R, hR, f, e, he, hf, inferInstance, β', inferInstance,
    hβflat.comp (.of_bijective θ.bijective), hlocal, ?_,
    A, hA, hAtrait, K, hK, hAK, hfrac, ϖ, π, b,
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hϖ, hπ, g, hg, hw⟩
  dsimp only [β']
  rw [← Ideal.map_map, hJ, Ideal.map_map]
  have hc : θ.toRingHom.comp
      ((algebraMap D (Localization.AtPrime P)).comp (AdjoinRoot.of p)) =
      AdjoinRoot.of p := by
    rw [← RingHom.comp_assoc, hθ, RingHom.id_comp]
  rw [hc]


end AlgebraicGeometry.Scheme
