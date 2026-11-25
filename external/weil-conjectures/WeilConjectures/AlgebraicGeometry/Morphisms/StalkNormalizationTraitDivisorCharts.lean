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

public import Mathlib.RingTheory.AdjoinRoot

import WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationGenericComparison
import WeilConjectures.AlgebraicGeometry.Morphisms.NormalizationDenseOpen
import WeilConjectures.AlgebraicGeometry.Morphisms.RegularDivisorRootModelNormal
import WeilConjectures.AlgebraicGeometry.Morphisms.RegularDivisorPrescribedPuncturedRootChart
import WeilConjectures.RingTheory.RegularRingSmoothAscent
import Mathlib.RingTheory.TensorProduct.Quotient

/-! Tame charts with the trait divisor equation.

## References

* Stacks Project, Tags 0EYH, 0EYI and 0EYJ
* Stacks Project, Tags 0EYJ (trait reduction), 0EYG and 0EYH
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem normalization_iso_of_dense_open_model
    {X Y T : Scheme.{u}} (g : X ⟶ Y) [QuasiCompact g] [QuasiSeparated g]
    (q : T ⟶ Y) [IsIntegralHom q] [IsLocallyNoetherian T]
    (hn : ∀ z : T, IsDomain (T.presheaf.stalk z) ∧
      IsIntegrallyClosed (T.presheaf.stalk z))
    (V : T.Opens) (hV : Dense (V : Set T)) [QuasiCompact V.ι]
    (γ : X ≅ V.toScheme) (hγ : γ.hom ≫ V.ι ≫ q = g) :
    ∃ δ : g.normalization ≅ T, δ.hom ≫ q = g.fromNormalization := by
  let := isIso_fromNormalization_denseOpen hn V hV
  let a := g.normalizationDesc (γ.hom ≫ V.ι) q (by simpa using hγ.symm)
  have ha : a ≫ q = g.fromNormalization := Hom.normalizationDesc_comp ..
  have hga : g.toNormalization ≫ a = γ.hom ≫ V.ι :=
    Hom.toNormalization_normalizationDesc ..
  have hb : V.ι = (γ.inv ≫ g.toNormalization) ≫ a := by
    rw [Category.assoc, hga, Iso.inv_hom_id_assoc]
  let b := V.ι.normalizationDesc (γ.inv ≫ g.toNormalization) a hb
  let c := inv V.ι.fromNormalization ≫ b
  have hca : c ≫ a = 𝟙 T := by
    dsimp only [c, b]
    rw [Category.assoc, Hom.normalizationDesc_comp, IsIso.inv_hom_id]
  have hcq : c ≫ g.fromNormalization = q := by
    rw [← ha, ← Category.assoc, hca, Category.id_comp]
  have hj : V.ι.toNormalization = V.ι ≫ inv V.ι.fromNormalization := by
    apply (cancel_mono V.ι.fromNormalization).mp
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id,
      Hom.toNormalization_fromNormalization]
  have hvc : V.ι ≫ c = γ.inv ≫ g.toNormalization := by
    dsimp only [c]
    rw [← Category.assoc, ← hj, Hom.toNormalization_normalizationDesc]
  have hac : a ≫ c = 𝟙 g.normalization := by
    apply Hom.normalization.hom_ext g _ _ g.fromNormalization
    · rw [← Category.assoc, hga, Category.assoc, hvc, Iso.hom_inv_id_assoc,
        Category.comp_id]
    · rw [Category.assoc, hcq, ha]
    · exact Category.id_comp _
  exact ⟨⟨a, c, hac, hca⟩, ha⟩

private theorem smooth_trait_regular_quotient
    (A R : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing R] [Algebra A R] [Algebra.Smooth A R]
    (π : A) (hπ : Irreducible π) :
    IsRegularRing R ∧ IsSMulRegular R (algebraMap A R π) ∧
      IsRegularRing (R ⧸ Ideal.span {algebraMap A R π}) := by
  have hR : IsRegularRing R := Algebra.isRegularRing_of_smooth A R
  have hπreg : IsSMulRegular A π :=
    isLeftRegular_iff.mp (IsRegular.of_ne_zero' hπ.ne_zero).1
  have hf : IsSMulRegular R (algebraMap A R π) := hπreg.of_flat
  refine ⟨hR, hf, ?_⟩
  let I : Ideal A := IsLocalRing.maximalIdeal A
  let k := A ⧸ I
  let : Field k := Ideal.Quotient.field I
  have hT : IsRegularRing (TensorProduct A k R) :=
    Algebra.isRegularRing_of_smooth k (TensorProduct A k R)
  have hQ : IsRegularRing (R ⧸ I.map (algebraMap A R)) :=
    IsRegularRing.of_ringEquiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor R I).symm.toRingEquiv
  rw [show I = Ideal.span {π} from hπ.maximalIdeal_eq] at hQ
  rw [Ideal.map_span] at hQ
  rw [Set.image_singleton] at hQ
  exact hQ

private theorem fractionRing_away_uniformizer
    (A K : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (π : A) (hπ : Irreducible π) : IsLocalization.Away π K := by
  refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
  · rintro ⟨s, n, rfl⟩
    apply Ne.isUnit
    simpa only [map_zero] using
      (IsFractionRing.injective A K).ne (pow_ne_zero n hπ.ne_zero)
  · intro z
    obtain ⟨⟨r, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors A) z
    obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (mem_nonZeroDivisors_iff_ne_zero.mp s.property) hπ
    refine ⟨(r * ↑v⁻¹, ⟨π ^ n, n, rfl⟩), ?_⟩
    have hvK : algebraMap A K (v : A) ≠ 0 :=
      (v.isUnit.map (algebraMap A K)).ne_zero
    change z * algebraMap A K (π ^ n) = algebraMap A K (r * ↑v⁻¹)
    rw [map_mul]
    apply mul_right_cancel₀ hvK
    calc
      (z * algebraMap A K (π ^ n)) * algebraMap A K ↑v =
          z * algebraMap A K (s : A) := by rw [hv, map_mul]; ring
      _ = algebraMap A K r := hs
      _ = (algebraMap A K r * algebraMap A K ↑v⁻¹) * algebraMap A K ↑v := by
        rw [mul_assoc, ← map_mul]
        simp
  · intro x y hxy
    exact ⟨1, by simpa using (IsFractionRing.injective A K) hxy⟩

private theorem smooth_trait_affine_generic_open_over
    (A K : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (π : A) (hπ : Irreducible π)
    {L : Scheme.{u}} (d : L ⟶ Spec (CommRingCat.of A)) [Smooth d] (x : L) :
    let b := Spec.map (CommRingCat.ofHom (algebraMap A K))
    ∃ (R : CommRingCat.{u}) (φ : Spec R ⟶ L) (y : Spec R),
      Etale φ ∧ φ y = x ∧
      ∃ _a : Algebra A R, Algebra.Smooth A R ∧
        φ ≫ d = Spec.map (CommRingCat.ofHom (algebraMap A R)) ∧
        let D : (Spec R).Opens := PrimeSpectrum.basicOpen (algebraMap A R π)
        ∃ β : pullback (pullback.fst d b) φ ≅ D.toScheme,
          β.hom ≫ D.ι = pullback.snd (pullback.fst d b) φ := by
  have : IsLocalization.Away π K := fractionRing_away_uniformizer A K π hπ
  let b := Spec.map (CommRingCat.ofHom (algebraMap A K))
  have : IsOpenImmersion b := IsOpenImmersion.of_isLocalization π
  obtain ⟨V, hV, hxV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top x)
  let R := Γ(L, V)
  let φ : Spec R ⟶ L := hV.fromSpec
  let y : Spec R := hV.isoSpec.hom ⟨x, hxV⟩
  have hy : φ y = x := by
    change (hV.isoSpec.hom ≫ hV.fromSpec) ⟨x, hxV⟩ = x
    simp
  let a := (Spec.preimage (φ ≫ d)).hom.toAlgebra
  let : Algebra A R := a
  have hsmooth : Algebra.Smooth A R := by
    apply RingHom.Smooth.toAlgebra
    apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mp
    rw [Spec.map_preimage]
    infer_instance
  refine ⟨R, φ, y, inferInstance, hy, a, hsmooth, Spec.map_preimage (φ ≫ d) |>.symm, ?_⟩
  let D : (Spec R).Opens := PrimeSpectrum.basicOpen (algebraMap A R π)
  have hrange : Set.range (pullback.snd (pullback.fst d b) φ) = (D : Set (Spec R)) := by
    rw [IsOpenImmersion.range_pullbackSnd]
    rw [Scheme.Hom.opensRange_pullbackFst]
    change (φ ≫ d) ⁻¹' Set.range b = (D : Set (Spec R))
    rw [show Set.range b = (PrimeSpectrum.basicOpen π : Set (PrimeSpectrum A)) from
      PrimeSpectrum.localization_away_comap_range K π]
    rw [← Spec.map_preimage (φ ≫ d)]
    exact congrArg (fun O : (Spec R).Opens ↦ (O : Set (Spec R)))
      (PrimeSpectrum.comap_basicOpen (Spec.preimage (φ ≫ d)).hom π)
  let β : pullback (pullback.fst d b) φ ≅ D.toScheme :=
    IsOpenImmersion.isoOfRangeEq (pullback.snd (pullback.fst d b) φ) D.ι
      (hrange.trans (Scheme.Opens.range_ι D).symm)
  exact ⟨β, IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _⟩


private theorem smooth_trait_normalization_divisor_chart
    (A K : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Scheme.{u}} (d : L ⟶ Spec (CommRingCat.of A)) [Smooth d]
    (G : Type (u + 1)) [Group G] [Finite G] (hGA : IsUnit (Nat.card G : A))
    (W : GaloisCover G
      (pullback d (Spec.map (CommRingCat.ofHom (algebraMap A K)))))
    (x : L) (hx : d x = IsLocalRing.closedPoint A) :
    letI : IsFinite W.π := W.isFinite
    let b := Spec.map (CommRingCat.ofHom (algebraMap A K))
    let p := W.π ≫ pullback.fst d b
    ∃ (R : CommRingCat.{u}) (φ : Spec R ⟶ L) (y : Spec R) (ρ : A →+* R) (ϖ : A),
      Etale φ ∧ φ y = x ∧ IsLocalRing.maximalIdeal A = Ideal.span {ϖ} ∧
      φ ≫ d = Spec.map (CommRingCat.ofHom ρ) ∧ ρ ϖ ∈ y.asIdeal ∧
      ∃ (m : ℕ) (e : Fin m → ℕ), (∀ k, 0 < e k) ∧
        ∃ α : pullback p.fromNormalization φ ≅ Spec (CommRingCat.of (∀ k : Fin m,
            AdjoinRoot ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C (ρ ϖ)))),
          α.hom ≫ Spec.map (CommRingCat.ofHom
            (algebraMap R (∀ k : Fin m,
              AdjoinRoot ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C (ρ ϖ))))) =
            pullback.snd p.fromNormalization φ := by
  classical
  let : IsFinite W.π := W.isFinite
  dsimp only
  let b := Spec.map (CommRingCat.ofHom (algebraMap A K))
  let p := W.π ≫ pullback.fst d b
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hchart := smooth_trait_affine_generic_open_over A K
      ϖ hϖ d x
  dsimp only at hchart
  obtain ⟨R, φ, y, hφ, hy, ar, hsm, hφd, γ₀, hγ₀⟩ := hchart
  let : Algebra A R := ar
  have : Algebra.Smooth A R := hsm
  obtain ⟨hR, hf, hRf⟩ := smooth_trait_regular_quotient A R ϖ hϖ
  have : IsRegularRing R := hR
  have : IsRegularRing (R ⧸ Ideal.span {algebraMap A R ϖ}) := hRf
  have hRy : algebraMap A R ϖ ∈ y.asIdeal := by
    have hdy : (Spec.map (CommRingCat.ofHom
        (algebraMap A R))) y =
        IsLocalRing.closedPoint A := by
      rw [← hφd, Scheme.Hom.comp_apply]
      change d (φ y) = _
      rw [hy, hx]
    have hmem : ϖ ∈ IsLocalRing.maximalIdeal A := by
      rw [hϖ.maximalIdeal_eq]
      exact Ideal.mem_span_singleton_self ϖ
    change ϖ ∈ (PrimeSpectrum.comap (algebraMap A R) y).asIdeal
    rw [show PrimeSpectrum.comap (algebraMap A R) y =
      IsLocalRing.closedPoint A from hdy]
    exact hmem
  have hGR : IsUnit (Nat.card G : R) := by
    simpa only [map_natCast] using hGA.map (algebraMap A R)
  obtain ⟨T, χ, z, hχ, hz, m, e, he, hT, hg, hTg, γ, hγ⟩ :=
    GaloisCover.regular_divisor_prescribed_punctured_root_chart
      (pullback.fst d b) G W R φ (algebraMap A R ϖ)
      hGR hf γ₀ hγ₀ y
  let ρ := (Spec.preimage χ).hom.comp (algebraMap A R)
  let f : T := ρ ϖ
  have : Etale φ := hφ
  have : Etale χ := hχ
  let φ' := χ ≫ φ
  have hφ'd : φ' ≫ d = Spec.map (CommRingCat.ofHom ρ) := by
    dsimp only [φ', ρ]
    rw [Category.assoc, hφd]
    calc
      χ ≫ Spec.map (CommRingCat.ofHom (algebraMap A R)) =
          Spec.map (Spec.preimage χ) ≫
            Spec.map (CommRingCat.ofHom (algebraMap A R)) := by
        rw [Spec.map_preimage]
      _ = _ := by rw [← Spec.map_comp]; rfl
  have hρ : ρ ϖ ∈ z.asIdeal := by
    change (Spec.preimage χ).hom (algebraMap A R ϖ) ∈ z.asIdeal
    change algebraMap A R ϖ ∈
      (PrimeSpectrum.comap (Spec.preimage χ).hom z).asIdeal
    have hz' : PrimeSpectrum.comap (Spec.preimage χ).hom z = y := by
      change (Spec.map (Spec.preimage χ)) z = y
      rw [Spec.map_preimage]
      exact hz
    rw [hz']
    exact hRy
  have : IsRegularRing T := hT
  have : IsRegularRing (T ⧸ Ideal.span {f}) := hTg
  let B := ∀ k : Fin m,
    AdjoinRoot ((Polynomial.X : Polynomial T) ^ e k - Polynomial.C f)
  let N := Spec (CommRingCat.of B)
  let r := Spec.map (CommRingCat.ofHom (algebraMap T B))
  let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap T B f)
  have hnormal : ∀ z : N, IsDomain (N.presheaf.stalk z) ∧
      IsIntegrallyClosed (N.presheaf.stalk z) :=
    regular_divisor_root_model_normal T m f hg e he
  have hV : Dense (V : Set N) := by
    have (k : Fin m) : Module.Free T
        (AdjoinRoot ((Polynomial.X : Polynomial T) ^ e k - Polynomial.C f)) :=
      (Polynomial.monic_X_pow_sub_C f (he k).1.ne').free_adjoinRoot
    have hfB : IsSMulRegular B (algebraMap T B f) := hg.of_flat
    have hr : IsRegular (algebraMap T B f) :=
      (Commute.isRegular_iff (fun b ↦ Commute.all _ b)).mpr
        (isLeftRegular_iff.mpr hfB)
    have hinj : Function.Injective
        (algebraMap B (Localization.Away (algebraMap T B f))) :=
      IsLocalization.injective (M := Submonoid.powers (algebraMap T B f))
        (Localization.Away (algebraMap T B f)) (by
        rintro v ⟨l, rfl⟩
        exact (hr.pow l).mem_nonZeroDivisors)
    change Dense (↑(PrimeSpectrum.basicOpen (algebraMap T B f)) : Set (PrimeSpectrum B))
    rw [← PrimeSpectrum.localization_away_comap_range
      (Localization.Away (algebraMap T B f)) (algebraMap T B f)]
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
    exact bot_le
  let (k : Fin m) : Module.Finite T
      (AdjoinRoot ((Polynomial.X : Polynomial T) ^ e k - Polynomial.C f)) :=
    (Polynomial.monic_X_pow_sub_C f (he k).1.ne').finite_adjoinRoot
  have : Module.Finite T B := inferInstance
  have : IsFinite r := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  let : IsLocallyNoetherian L := LocallyOfFiniteType.isLocallyNoetherian d
  let : IsLocallyNoetherian (Spec T) := LocallyOfFiniteType.isLocallyNoetherian φ'
  let : IsLocallyNoetherian N := LocallyOfFiniteType.isLocallyNoetherian r
  obtain ⟨δ, hδ⟩ := normalization_iso_of_dense_open_model
    (pullback.snd p φ') r hnormal V hV γ hγ
  let α₀ := (asIso (p.normalizationPullback φ')).symm ≪≫ δ
  have hα₀ : α₀.hom ≫ r = pullback.snd p.fromNormalization φ' := by
    dsimp only [α₀, Iso.trans_hom, Iso.symm_hom]
    rw [Category.assoc, hδ]
    exact (IsIso.inv_comp_eq (p.normalizationPullback φ')).mpr
      (Hom.normalizationPullback_snd p φ').symm
  refine ⟨T, φ', z, ρ, ϖ, inferInstance, ?_, hϖ.maximalIdeal_eq, hφ'd, hρ,
    m, e, fun k ↦ (he k).1, α₀, hα₀⟩
  dsimp only [φ']
  rw [Scheme.Hom.comp_apply, hz, hy]

/-- A tame affine chart using the pullback of an actual trait uniformizer. -/
theorem GaloisCover.stalk_normalization_trait_divisor_charts {S C : Scheme.{u}}
    [IsNoetherian S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c] [GeometricallyConnected c]
    (σ : S ⟶ C) (hσ : σ ≫ c = 𝟙 S)
    (G : Type (u + 1)) [Group G] [Finite G]
    (hG : IsUnit (Nat.card G : Γ(S, ⊤)))
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c)
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
      ∃ (R : CommRingCat.{u}) (φ : Spec R ⟶ pullback c a) (y : Spec R)
        (ρ : S.presheaf.stalk s →+* R) (ϖ : S.presheaf.stalk s),
        Etale φ ∧ φ y = n x ∧
        IsLocalRing.maximalIdeal (S.presheaf.stalk s) = Ideal.span {ϖ} ∧
        φ ≫ pullback.snd c a = Spec.map (CommRingCat.ofHom ρ) ∧
        ρ ϖ ∈ y.asIdeal ∧
        ∃ (m : ℕ) (e : Fin m → ℕ), (∀ k, 0 < e k) ∧
          ∃ α : pullback n φ ≅ Spec (CommRingCat.of (∀ k : Fin m,
              AdjoinRoot ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C (ρ ϖ)))),
            α.hom ≫ Spec.map (CommRingCat.ofHom
              (algebraMap R (∀ k : Fin m,
                AdjoinRoot ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C (ρ ϖ))))) =
              pullback.snd n φ := by
  classical
  let : IsFinite PA.obj.hom := PA.property
  let : QuasiCompact (c ⁻¹ᵁ U).ι :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
      (inferInstance : QuasiCompact U.ι)
  let : IsDiscreteValuationRing (S.presheaf.stalk s) := hdvr
  dsimp only
  intro hn x hx
  let a := S.fromSpecStalk s
  let d := pullback.snd c a
  let n := pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization (pullback.fst c a)
  let : IsFinite n := hn
  have hcomparison := GaloisCover.stalk_normalization_generic_comparison
    c G q j hCη Z U jU PA ψ hjU hψ s hs hmin hdvr
  dsimp only at hcomparison
  obtain ⟨W, β, hβ⟩ := hcomparison
  let : IsFinite W.π := W.isFinite
  let b := Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) S.functionField))
  let p := W.π ≫ pullback.fst d b
  have hβ' : β.hom ≫ p.fromNormalization = n := hβ
  have hGA : IsUnit (Nat.card G : S.presheaf.stalk s) := by
    simpa only [map_natCast] using hG.map (S.presheaf.Γgerm s).hom
  have hnx : d (n x) = IsLocalRing.closedPoint (S.presheaf.stalk s) := by
    rw [hx]
    change (pullback.lift (a ≫ σ) (𝟙 _) _ ≫ pullback.snd c a) _ = _
    rw [pullback.lift_snd]
    rfl
  have hchart := smooth_trait_normalization_divisor_chart
    (S.presheaf.stalk s) S.functionField d G hGA W (n x) hnx
  dsimp only at hchart
  obtain ⟨R, φ, y, ρ, ϖ, hφ, hy, hϖ, hφd, hρ, m, e, he, α₀, hα₀⟩ := hchart
  let E : pullback n φ ≅ pullback p.fromNormalization φ :=
    asIso (pullback.map n φ p.fromNormalization φ β.hom (𝟙 _) (𝟙 _)
      (by simpa only [Category.comp_id] using hβ'.symm) (by simp))
  refine ⟨R, φ, y, ρ, ϖ, hφ, hy, hϖ, hφd, hρ, m, e, he, E ≪≫ α₀, ?_⟩
  change (E.hom ≫ α₀.hom) ≫ _ = pullback.snd n φ
  rw [Category.assoc, hα₀]
  change E.hom ≫ pullback.snd p.fromNormalization φ = pullback.snd n φ
  simp only [E, asIso_hom, pullback.map, pullback.lift_snd, Category.comp_id]


end AlgebraicGeometry.Scheme
