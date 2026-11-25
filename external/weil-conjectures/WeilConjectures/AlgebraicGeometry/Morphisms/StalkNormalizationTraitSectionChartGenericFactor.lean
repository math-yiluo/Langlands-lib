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

import WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionRootPresentation
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian

/-!
# Tame local chart and its generic section factor

## References

* Stacks Project, Tags 0EYH and 0EYI(2)
* Stacks Project, Tag 0EYH, and the transverse section construction in 0EYI(2)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem root_maximalIdeal {R : Type u} [CommRing R] [IsLocalRing R]
    (f : R) (e : ℕ) (hf : f ∈ IsLocalRing.maximalIdeal R)
    [IsLocalRing (AdjoinRoot ((Polynomial.X : Polynomial R) ^ e - Polynomial.C f))]
    [IsLocalHom (AdjoinRoot.of ((Polynomial.X : Polynomial R) ^ e - Polynomial.C f))] :
    let p := (Polynomial.X : Polynomial R) ^ e - Polynomial.C f
    IsLocalRing.maximalIdeal (AdjoinRoot p) =
      (IsLocalRing.maximalIdeal R).map (AdjoinRoot.of p) ⊔
        Ideal.span {AdjoinRoot.root p} ∧
    AdjoinRoot.root p ^ e ∈ (IsLocalRing.maximalIdeal R).map (AdjoinRoot.of p) := by
  dsimp only
  let p := (Polynomial.X : Polynomial R) ^ e - Polynomial.C f
  let t := AdjoinRoot.root p
  let ρ := AdjoinRoot.of p
  let M := (IsLocalRing.maximalIdeal R).map ρ
  have hrel : t ^ e = ρ f := by
    have h := AdjoinRoot.eval₂_root p
    simpa only [p, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, sub_eq_zero] using h
  have hpow : t ^ e ∈ M := by
    rw [hrel]
    exact Ideal.mem_map_of_mem ρ hf
  have hM : M ≤ IsLocalRing.maximalIdeal (AdjoinRoot p) :=
    IsLocalRing.map_maximalIdeal_le ρ
  have ht : t ∈ IsLocalRing.maximalIdeal (AdjoinRoot p) :=
    (IsLocalRing.maximalIdeal.isMaximal (AdjoinRoot p)).isPrime.mem_of_pow_mem e (hM hpow)
  refine ⟨le_antisymm ?_ (sup_le hM (Ideal.span_le.mpr (by simpa using ht))), hpow⟩
  intro z hz
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective (g := p) z
  obtain ⟨q', hq⟩ := Polynomial.X_dvd_sub_C (p := q)
  have hdecomp : AdjoinRoot.mk p q = ρ (q.coeff 0) + t * AdjoinRoot.mk p q' := by
    have h := congrArg (AdjoinRoot.mk p) hq
    simp only [map_sub, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h
    exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
  have hprod : t * AdjoinRoot.mk p q' ∈ IsLocalRing.maximalIdeal (AdjoinRoot p) :=
    (IsLocalRing.maximalIdeal (AdjoinRoot p)).mul_mem_right _ ht
  have hc : ρ (q.coeff 0) ∈ IsLocalRing.maximalIdeal (AdjoinRoot p) := by
    have h := (IsLocalRing.maximalIdeal (AdjoinRoot p)).sub_mem hz hprod
    simpa only [hdecomp, add_sub_cancel_right] using h
  have hcR : q.coeff 0 ∈ IsLocalRing.maximalIdeal R := by
    rw [← IsLocalRing.maximalIdeal_comap ρ]
    exact hc
  rw [hdecomp]
  exact (M ⊔ Ideal.span {t}).add_mem
    ((show M ≤ M ⊔ Ideal.span {t} from le_sup_left) (Ideal.mem_map_of_mem ρ hcR))
    ((show Ideal.span {t} ≤ M ⊔ Ideal.span {t} from le_sup_right)
      ((Ideal.span {t}).mul_mem_right _ (Ideal.subset_span (by simp))))

/-- The tame local chart, before using splitting of the generic section fibre. -/
theorem GaloisCover.stalk_normalization_trait_section_chart_generic_factor {S C : Scheme.{u}}
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
      ∃ (D : CommRingCat.{u}) (_ : IsLocalRing D) (β : B →+* D),
        IsLocalHom β ∧ β.Flat ∧
        ∃ (t : D) (e : ℕ) (K : Type u) (_ : Field K)
          (ord : Kˣ →* Multiplicative ℤ) (π : Kˣ)
          (b : Spec (CommRingCat.of K) ⟶ Spec S.functionField),
          0 < e ∧
          IsLocalRing.maximalIdeal D = J.map β ⊔ Ideal.span {t} ∧
          t ^ e ∈ J.map β ∧ ord π = Multiplicative.ofAdd 1 ∧
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
  intro a n τ hn x hx B J
  obtain ⟨R, hR, f, e, he, hf, hD, β, hβlocal, hβflat, hlocal, hJ,
      A, hA, hAtrait, K, hK, hAK, hfrac, ϖ, π, b, hϖ, hπ, g, hg, hw⟩ :=
    GaloisCover.stalk_normalization_trait_section_root_presentation
      (S := S) (C := C) (Cη := Cη)
      c σ hσ G hG q j hCη sη hsj Z U jU PA ψ hjU hψ s hs hmin hdvr
      hn x hx
  let := hR
  let := hD
  let := hlocal
  let := hA
  let := hAtrait
  let := hK
  let := hAK
  let := hfrac
  let p := (Polynomial.X : Polynomial R) ^ e - Polynomial.C f
  have hroot := root_maximalIdeal f e hf
  refine ⟨CommRingCat.of (AdjoinRoot p), hD, β, hβlocal, hβflat,
    AdjoinRoot.root p, e, K, hK, Ring.ordOfUnits A K, π, b, he, ?_, ?_, ?_, g, hg, hw⟩
  · exact hroot.1.trans (congrArg (fun I ↦ I ⊔ Ideal.span {AdjoinRoot.root p}) hJ.symm)
  · exact hJ.symm ▸ hroot.2
  · simp only [Ring.ordOfUnits_apply, hπ,
      Ring.ordOf_algebraMap_of_irreducible hϖ]


end AlgebraicGeometry.Scheme
