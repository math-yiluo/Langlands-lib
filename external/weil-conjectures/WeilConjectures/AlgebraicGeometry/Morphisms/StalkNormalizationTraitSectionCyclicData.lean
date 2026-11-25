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

import WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionChartGenericFactor
import WeilConjectures.AlgebraicGeometry.Morphisms.GaloisCoverOpenFactorRationalPoint

/-!
# Cyclic local chart data along a split trait section

## References

* Stacks Project, Tags 0EYH and 0EYI(2)
* Stacks Project, Tags 0EYH and 0EYI(2), trait paragraph of 0EYJ
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A tame chart at a point over the trait section has one ramification coordinate,
and the split generic section supplies a root of its uniformizer in an unramified
trait fraction field. -/
theorem GaloisCover.stalk_normalization_trait_section_cyclic_data {S C : Scheme.{u}}
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
    (Z : GaloisCover G Cη) (hZ : ∃ z : Spec S.functionField ⟶ Z.P, z ≫ Z.π = sη)
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
          (ord : Kˣ →* Multiplicative ℤ) (π z : Kˣ),
          0 < e ∧
          IsLocalRing.maximalIdeal D = J.map β ⊔ Ideal.span {t} ∧
          t ^ e ∈ J.map β ∧ z ^ e = π ∧ ord π = Multiplicative.ofAdd 1 := by
  classical
  let : IsFinite PA.obj.hom := PA.property
  let : QuasiCompact (c ⁻¹ᵁ U).ι :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
      (inferInstance : QuasiCompact U.ι)
  dsimp only
  intro hn x hx
  have hchart := GaloisCover.stalk_normalization_trait_section_chart_generic_factor
    (S := S) (C := C) (Cη := Cη)
    c σ hσ G hG q j hCη sη hsj Z U jU PA ψ hjU hψ s hs hmin hdvr
  have hc := hchart hn x hx
  obtain ⟨D, hD, β, hβlocal, hβflat, t, e, K, hK, ord, π, b,
    he, hgen, hpow, hπ, g, hg, hw⟩ := hc
  let := hD
  let := hK
  let p : Polynomial K := Polynomial.X ^ e - Polynomial.C (π : K)
  have : Nontrivial (AdjoinRoot p) := AdjoinRoot.nontrivial p (by
    dsimp only [p]
    rw [Polynomial.degree_X_pow_sub_C he]
    exact_mod_cast ne_of_gt he)
  have hp := GaloisCover.open_factor_rational_point (Y := Cη) G Z S.functionField sη hZ
    K b (AdjoinRoot p) g hg hw
  obtain ⟨φ⟩ := hp
  have hz : φ (AdjoinRoot.root p) ^ e = (π : K) := by
    have hroot := AdjoinRoot.aeval_algHom_eq_zero p φ
    simpa only [p, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_self, RingHom.id_apply, sub_eq_zero] using hroot
  have hne : φ (AdjoinRoot.root p) ≠ 0 := by
    intro hzero
    have : (π : K) = 0 := by simpa [hzero, ne_of_gt he] using hz.symm
    exact π.ne_zero this
  let z : Kˣ := Units.mk0 (φ (AdjoinRoot.root p)) hne
  have hzunits : z ^ e = π := by
    apply Units.ext
    exact hz
  exact ⟨D, hD, β, hβlocal, hβflat, t, e, K, hK, ord, π, z,
    he, hgen, hpow, hzunits, hπ⟩

end AlgebraicGeometry.Scheme
