/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.DivisorIdealSheaf


public import Mathlib.RingTheory.FractionalIdeal.Operations
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.NoetherNormalization
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateCoverProduct
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.Mathlib.AlgebraicGeometry.Properties
public import WeilConjectures.Mathlib.RingTheory.NoetherNormalization
public import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# Integral curves are quasi-projective

WIP
-/

@[expose] public section

open Polynomial IsLocalRing

/-- Let `B` be a noetherian local domain of dimension at most one with fraction field `K`, and let
`g ∈ K` satisfy `p(g) = 1` for a polynomial `p` with coefficients in the maximal ideal `𝔪` of
`B`, i.e. `𝔪 B[g] = B[g]`. Then some positive power of `g⁻¹` lies in `𝔪`.

Indeed `h = g⁻¹` is integral over `B` with `hⁿ ∈ 𝔪 B[h]`, and the finite `B`-module `B[h]` is
fractional: `d B[h] ⊆ B` for some `d ≠ 0`, and `𝔪ᵏ ⊆ d B` as `𝔪` is the only nonzero prime.
Hence `h^{n(k+1)} ∈ 𝔪^{k+1} B[h] ⊆ 𝔪 B`. -/
theorem exists_pow_inv_mem_maximalIdeal {B K : Type*} [CommRing B] [IsLocalRing B] [IsDomain B]
    [IsNoetherianRing B] [Ring.KrullDimLE 1 B] [Field K] [Algebra B K] [IsFractionRing B K]
    (g : K) (p : B[X]) (hp : ∀ i, p.coeff i ∈ maximalIdeal B) (hpg : aeval g p = 1) :
    g ≠ 0 ∧ ∃ n > 0, ∃ b ∈ maximalIdeal B, algebraMap B K b = g⁻¹ ^ n := by
  have hinj := IsFractionRing.injective B K
  have hg : g ≠ 0 := by
    rintro rfl
    rw [← coeff_zero_eq_aeval_zero', ← map_one (algebraMap B K)] at hpg
    exact (maximalIdeal.isMaximal B).ne_top
      ((Ideal.eq_top_iff_one _).mpr (hinj hpg ▸ hp 0))
  let := invertibleOfNonzero hg
  set h := g⁻¹ with hh
  set n := p.natDegree
  -- `hⁿ = p̃(h)` for the reverse polynomial `p̃`
  have hrev : aeval h p.reverse = h ^ n := by
    have := eval₂_reverse_mul_pow (algebraMap B K) g p
    rw [← aeval_def, ← aeval_def, hpg, invOf_eq_inv] at this
    rw [← mul_one (aeval h p.reverse), ← mul_inv_cancel₀ (pow_ne_zero n hg), ← mul_assoc, this,
      one_mul, inv_pow]
  have hrevm (i : ℕ) : p.reverse.coeff i ∈ maximalIdeal B := by
    rw [coeff_reverse]
    exact hp _
  -- `h` is integral over `B`
  set q : B[X] := X ^ n - p.reverse
  have hq : aeval h q = 0 := by simp [q, hrev]
  have hqn : q.coeff n = 1 - p.coeff 0 := by
    simp [q, coeff_reverse, revAt_le le_rfl, n]
  have hu : IsUnit (q.coeff n) := by
    rw [hqn]
    exact isUnit_one_sub_self_of_mem_nonunits _ (hp 0)
  have hqdeg : q.natDegree = n := by
    refine natDegree_eq_of_le_of_coeff_ne_zero ?_ hu.ne_zero
    refine (natDegree_sub_le _ _).trans (max_le (natDegree_X_pow_le n) ?_)
    exact reverse_natDegree_le p
  have hint : IsIntegral B h := by
    obtain ⟨u, hu'⟩ := hu
    have h₁ := (isIntegral_leadingCoeff_smul q h hq).smul (↑u⁻¹ : B)
    rwa [smul_smul, leadingCoeff, hqdeg, ← hu', Units.inv_mul, one_smul] at h₁
  -- the finite `B`-module `B[h]` is fractional
  let M := Subalgebra.toSubmodule (Algebra.adjoin B {h})
  obtain ⟨d, hd, hdM⟩ :=
    FractionalIdeal.isFractional_of_fg (S := nonZeroDivisors B) hint.fg_adjoin_singleton
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  -- `𝔪ᵏ ⊆ (d)`
  obtain ⟨k, hk⟩ : ∃ k : ℕ, maximalIdeal B ^ k ≤ Ideal.span {d} := by
    refine Ideal.exists_pow_le_of_le_radical_of_fg ?_ (IsNoetherian.noetherian _)
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun P ⟨hdP, hP⟩ ↦ ?_
    have hP0 : P ≠ ⊥ := fun h0 ↦ hd0 (by simpa [h0] using hdP)
    exact ((hP.isMaximal_of_ne_bot hP0).eq_of_le (maximalIdeal.isMaximal B).ne_top
      (le_maximalIdeal hP.ne_top)).symm.le
  -- the image of `𝔪` in `K`
  let T : Submodule B K := Submodule.map (Algebra.linearMap B K) (maximalIdeal B)
  have hT : (maximalIdeal B ^ (k + 1)) • M ≤ T := by
    refine Submodule.smul_le.mpr fun a ha y hy ↦ ?_
    obtain ⟨b, hb⟩ := hdM y hy
    rw [pow_succ'] at ha
    refine Submodule.mul_induction_on ha (fun x hx z hz ↦ ?_) fun _ _ h₁ h₂ ↦ ?_
    · obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hk hz)
      refine ⟨x * c * b, Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hx), ?_⟩
      rw [← hc, smul_eq_mul, Algebra.linearMap_apply, map_mul, map_mul, hb, Algebra.smul_def,
        Algebra.smul_def, map_mul, map_mul]
      ring
    · rw [add_smul]
      exact T.add_mem h₁ h₂
  -- `h^{n j} ∈ 𝔪ʲ B[h]`
  have hmul {I J : Ideal B} {x y : K} (hx : x ∈ I • M) (hy : y ∈ J • M) :
      x * y ∈ (I * J) • M := by
    refine Submodule.smul_induction_on hx (fun a ha m hm ↦ ?_) fun _ _ h₁ h₂ ↦ ?_
    · refine Submodule.smul_induction_on hy (fun b hb m' hm' ↦ ?_) fun _ _ h₁ h₂ ↦ ?_
      · rw [smul_mul_smul_comm]
        exact Submodule.smul_mem_smul (Ideal.mul_mem_mul ha hb)
          ((Algebra.adjoin B {h}).mul_mem hm hm')
      · rw [mul_add]
        exact Submodule.add_mem _ h₁ h₂
    · rw [add_mul]
      exact Submodule.add_mem _ h₁ h₂
  have hhn : h ^ n ∈ maximalIdeal B • M := by
    rw [← hrev, aeval_eq_sum_range]
    refine Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem_smul (hrevm i) ?_
    exact (Algebra.adjoin B {h}).pow_mem (Algebra.subset_adjoin rfl) i
  have hpow (j : ℕ) : h ^ (n * j) ∈ maximalIdeal B ^ j • M := by
    induction j with
    | zero =>
      rw [mul_zero, pow_zero, pow_zero, Ideal.one_eq_top, Submodule.top_smul]
      exact (Algebra.adjoin B {h}).one_mem
    | succ j ih =>
      rw [mul_add, mul_one, pow_add h, mul_comm (h ^ (n * j)), pow_succ' (maximalIdeal B)]
      exact hmul hhn ih
  -- conclusion
  have hn : 0 < n := by
    refine Nat.pos_of_ne_zero fun hn0 ↦ ?_
    have := hrevm 0
    rw [coeff_zero_reverse] at this
    have hp1 : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero hn0
    rw [hp1, aeval_C, ← map_one (algebraMap B K)] at hpg
    exact (maximalIdeal.isMaximal B).ne_top
      ((Ideal.eq_top_iff_one _).mpr (hinj hpg ▸ hp 0))
  obtain ⟨b, hb, hb'⟩ := hT (hpow (k + 1))
  exact ⟨hg, n * (k + 1), Nat.mul_pos hn k.succ_pos, b, hb, by rw [← hb', Algebra.linearMap_apply]⟩

open Polynomial in
/-- If `𝔪 B[γ] = B[γ]` for an ideal `𝔪` of `B`, then `p(γ) = 1` for a polynomial `p` with
coefficients in `𝔪`. -/
lemma exists_aeval_eq_one_of_map_eq_top {B K : Type*} [CommRing B] [CommRing K] [Algebra B K]
    (γ : K) (I : Ideal B) (h : Ideal.map (algebraMap B (Algebra.adjoin B {γ})) I = ⊤) :
    ∃ p : B[X], (∀ i, p.coeff i ∈ I) ∧ aeval γ p = 1 := by
  set S := Algebra.adjoin B {γ}
  let φ : B[X] →ₐ[B] S := aeval ⟨γ, Algebra.self_mem_adjoin_singleton B γ⟩
  have hφ (q : B[X]) : (φ q : K) = aeval γ q := by
    rw [← Subalgebra.val_apply, ← aeval_algHom_apply]
    rfl
  have hsurj : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    have hy' : y ∈ (aeval (R := B) γ).range := by rwa [← Algebra.adjoin_singleton_eq_range_aeval]
    obtain ⟨q, rfl⟩ := hy'
    exact ⟨q, Subtype.ext (hφ q)⟩
  have hmap : Ideal.map (algebraMap B S) I = Ideal.map (φ : B[X] →+* S) (Ideal.map C I) := by
    rw [Ideal.map_map]
    congr 1
    rw [← Polynomial.algebraMap_eq]
    exact φ.comp_algebraMap.symm
  rw [hmap] at h
  obtain ⟨q, hq, hq1⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).mp (h ▸ Submodule.mem_top :
    (1 : S) ∈ Ideal.map (φ : B[X] →+* S) (Ideal.map C I))
  refine ⟨q, fun i ↦ Ideal.mem_map_C_iff.mp hq i, ?_⟩
  rw [← hφ, hq1]
  rfl

namespace AlgebraicGeometry

universe u

open CategoryTheory Limits TopologicalSpace

variable {X : Scheme.{u}}

/-- Let `U` be a nonempty affine open of an integral separated scheme `X` and `x ∉ U`. Let `R` be a
domain with an injection into the function field through which `Γ(X, U)` and `𝒪_{X,x}` factor.
Then no prime of `R` lies over the maximal ideal of `𝒪_{X,x}`: such a prime `P` would map to `x`
along `Spec R ⟶ Spec 𝒪_{X,x} ⟶ X` and into `U` along `Spec R ⟶ U`, and these two morphisms
agree since they agree at the generic point and `X` is separated. -/
lemma comap_ne_maximalIdeal_of_notMem [IsIntegral X] [X.IsSeparated] {U : X.Opens}
    (hU : IsAffineOpen U) [Nonempty U] {x : X} (hx : x ∉ U) {R : Type u} [CommRing R]
    [IsDomain R] (α : Γ(X, U) →+* R) (β : X.presheaf.stalk x →+* R) (ι : R →+* X.functionField)
    (hι : Function.Injective ι) (hα : ι.comp α = (X.germToFunctionField U).hom)
    (hβ : ι.comp β = algebraMap (X.presheaf.stalk x) X.functionField)
    (P : Ideal R) [P.IsPrime] : P.comap β ≠ IsLocalRing.maximalIdeal _ := by
  intro hP
  have hη : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have : IsDominant (Spec.map (CommRingCat.ofHom ι)) := by
    constructor
    exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical ι).mpr
      ((RingHom.injective_iff_ker_eq_bot _).mp hι ▸ bot_le)
  have key : Spec.map (CommRingCat.ofHom α) ≫ hU.fromSpec =
      Spec.map (CommRingCat.ofHom β) ≫ X.fromSpecStalk x := by
    refine ext_of_isDominant (Spec.map (CommRingCat.ofHom ι)) ?_
    rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, hα, hβ, CommRingCat.ofHom_hom]
    exact (hU.fromSpecStalk_eq_fromSpecStalk hη).trans
      (Scheme.SpecMap_stalkSpecializes_fromSpecStalk
        ((genericPoint_spec X).specializes trivial)).symm
  let z : Spec (CommRingCat.of R) := ⟨P, inferInstance⟩
  have h₁ : (Spec.map (CommRingCat.ofHom α) ≫ hU.fromSpec) z ∈ U := by
    rw [Scheme.Hom.comp_apply]
    exact hU.range_fromSpec.subset ⟨_, rfl⟩
  have h₂ : Spec.map (CommRingCat.ofHom β) z = IsLocalRing.closedPoint _ := PrimeSpectrum.ext hP
  have h₃ : (Spec.map (CommRingCat.ofHom β) ≫ X.fromSpecStalk x) z = x := by
    rw [Scheme.Hom.comp_apply, h₂]
    exact Scheme.fromSpecStalk_closedPoint
  rw [key, h₃] at h₁
  exact hx h₁

/-- Let `U` be a nonempty affine open of an integral separated scheme `X`, let `x ∉ U` and let `S`
be a subalgebra of the function field over `𝒪_{X,x}` such that every element of `Γ(X, U)` is
integral over `S`. Then `𝔪_x S = S`: otherwise a prime of the integral extension `S[Γ(X, U)]`
would lie over `𝔪_x`, contradicting `AlgebraicGeometry.comap_ne_maximalIdeal_of_notMem`. -/
lemma map_maximalIdeal_eq_top_of_notMem [IsIntegral X] [X.IsSeparated] {U : X.Opens}
    (hU : IsAffineOpen U) [Nonempty U] {x : X} (hx : x ∉ U)
    (S : Subalgebra (X.presheaf.stalk x) X.functionField)
    (hint : ∀ a : Γ(X, U), _root_.IsIntegral S (X.germToFunctionField U a)) :
    Ideal.map (algebraMap (X.presheaf.stalk x) S) (IsLocalRing.maximalIdeal _) = ⊤ := by
  by_contra hI
  let R := Algebra.adjoin S (Set.range (X.germToFunctionField U))
  have : Algebra.IsIntegral S R :=
    Algebra.IsIntegral.adjoin fun _ ⟨a, ha⟩ ↦ ha ▸ hint a
  have hinj : Function.Injective (algebraMap S R) := fun a b h ↦
    Subtype.ext (congrArg (fun r : R ↦ (r : X.functionField)) h)
  have hI' : Ideal.map (algebraMap S R)
      (Ideal.map (algebraMap (X.presheaf.stalk x) S) (IsLocalRing.maximalIdeal _)) ≠ ⊤ := by
    rwa [Ne, Ideal.map_eq_top_iff _ hinj (algebraMap_isIntegral_iff.mpr inferInstance)]
  obtain ⟨P, hPmax, hP⟩ := Ideal.exists_le_maximal _ hI'
  let α : Γ(X, U) →+* R := (X.germToFunctionField U).hom.codRestrict R
    fun a ↦ Algebra.subset_adjoin ⟨a, rfl⟩
  let β : X.presheaf.stalk x →+* R :=
    (algebraMap S R).comp (algebraMap (X.presheaf.stalk x) S)
  refine comap_ne_maximalIdeal_of_notMem hU hx α β (R.val.toRingHom) Subtype.val_injective
    (RingHom.ext fun _ ↦ rfl) (RingHom.ext fun _ ↦ rfl) P ?_
  refine ((IsLocalRing.maximalIdeal.isMaximal _).eq_of_le ?_ ?_).symm
  · exact (Ideal.comap_ne_top _ hPmax.ne_top)
  · intro b hb
    exact hP (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hb))

end AlgebraicGeometry

/-- **Noether normalization in dimension at most one.** A finitely generated algebra `A` of
dimension at most one over a field `k` is integral over `k[g]` for some `g ∈ A`. -/
theorem exists_forall_isIntegral_adjoin_singleton {k A : Type*} [Field k] [CommRing A]
    [Nontrivial A] [Algebra k A] [Algebra.FiniteType k A] (hA : ringKrullDim A ≤ 1) :
    ∃ g : A, ∀ a : A, IsIntegral (Algebra.adjoin k {g}) a := by
  classical
  obtain ⟨d, φ, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  have hd : d ≤ 1 := by
    rw [ringKrullDim_eq_of_finite_inj_algHom_mvPolynomial φ hinj hfin] at hA
    exact_mod_cast hA
  let g : A := if h : 0 < d then φ (MvPolynomial.X ⟨0, h⟩) else 0
  have hle : φ.range ≤ Algebra.adjoin k {g} := by
    rw [← Algebra.map_top, ← MvPolynomial.adjoin_range_X, AlgHom.map_adjoin,
      Algebra.adjoin_le_iff]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    have hi : i = ⟨0, i.pos⟩ := Fin.ext (by omega)
    refine Algebra.subset_adjoin ?_
    rw [Set.mem_singleton_iff, hi]
    simp [g, i.pos]
  refine ⟨g, fun a ↦ ?_⟩
  let := φ.toRingHom.toAlgebra
  have ha : IsIntegral (MvPolynomial (Fin d) k) a := hfin.to_isIntegral a
  exact ha.map_of_comp_eq ((Subalgebra.inclusion hle).toRingHom.comp φ.rangeRestrict.toRingHom)
    (RingHom.id A) (RingHom.ext fun _ ↦ rfl)

namespace AlgebraicGeometry

universe u

open CategoryTheory Limits TopologicalSpace IsLocalRing

variable {X : Scheme.{u}}

/-- For a nonempty affine open `U` of an integral curve `X` over a field `K` there is a nonzero
`f ∈ Γ(X, U)` such that `f⁻¹` lies in the maximal ideal of `𝒪_{X,x}` for every `x ∉ U`: `f` has a
pole at every point of the boundary of `U` (Stacks, Tag 09NB).

Choose `g` with `Γ(X, U)` integral over `K[g]` (Noether normalization). For `x ∉ U`, separatedness
gives `𝔪_x 𝒪_{X,x}[g] = 𝒪_{X,x}[g]` (`AlgebraicGeometry.map_maximalIdeal_eq_top_of_notMem`), so a
power of `g⁻¹` lies in `𝔪_x` (`exists_pow_inv_mem_maximalIdeal`); as the boundary is finite,
`f = g^N` works for a common `N`. -/
theorem exists_inv_mem_maximalIdeal_of_notMem {K : Type u} [Field K] (p : X ⟶ Spec (.of K))
    [IsCurve p] [IsIntegral X] {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] :
    ∃ f : Γ(X, U), X.germToFunctionField U f ≠ 0 ∧ ∀ x ∉ U, ∃ b ∈ maximalIdeal
      (X.presheaf.stalk x), algebraMap _ X.functionField b = (X.germToFunctionField U f)⁻¹ := by
  classical
  have := Scheme.isSeparated_of_isSeparated_hom p
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace X := (quasiCompact_iff_compactSpace p).mp inferInstance
  have : IsNoetherian X := ⟨⟩
  -- `Γ(X, U)` is a finitely generated `K`-algebra of dimension at most one
  let : Algebra K Γ(X, U) :=
    ((p.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
  have : Algebra.FiniteType K Γ(X, U) :=
    RingHom.FiniteType.comp (HasRingHomProperty.appLE @LocallyOfFiniteType p inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top) (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm.surjective)
  have hdimA : ringKrullDim Γ(X, U) ≤ 1 := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact (IsHomeomorph.topologicalKrullDim_eq _
      (Scheme.homeoOfIso hU.isoSpec).isHomeomorph).symm.trans_le
      ((topologicalKrullDim_subspace_le X U).trans (IsCurve.krullDim_le_one p))
  obtain ⟨g, hg⟩ := exists_forall_isIntegral_adjoin_singleton (k := K) hdimA
  set γ := X.germToFunctionField U g
  -- the image of `K[g]` lies in `𝒪_{X,x}[γ]`
  have hmem (x : X) (y : Algebra.adjoin K {g}) :
      X.germToFunctionField U y ∈ Algebra.adjoin (X.presheaf.stalk x) {γ} := by
    obtain ⟨y, hy⟩ := y
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      obtain rfl : y = g := hy
      exact Algebra.self_mem_adjoin_singleton _ _
    | algebraMap c =>
      have : Nonempty (⊤ : X.Opens) := ⟨⟨x, trivial⟩⟩
      have e : X.germToFunctionField U (algebraMap K Γ(X, U) c) = algebraMap
          (X.presheaf.stalk x) X.functionField (X.presheaf.germ ⊤ x trivial
            (p.appTop ((Scheme.ΓSpecIso (.of K)).inv c))) := by
        rw [Scheme.algebraMap_germ_eq_germToFunctionField]
        exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
      rw [e]
      exact Subalgebra.algebraMap_mem _ _
    | add y z _ _ hy hz =>
      rw [map_add]
      exact Subalgebra.add_mem _ hy hz
    | mul y z _ _ hy hz =>
      rw [map_mul]
      exact Subalgebra.mul_mem _ hy hz
  -- at every boundary point a power of `γ⁻¹` lies in the maximal ideal
  have key (x : X) (hx : x ∉ U) : γ ≠ 0 ∧ ∃ n > 0, ∃ b ∈ maximalIdeal (X.presheaf.stalk x),
      algebraMap _ X.functionField b = γ⁻¹ ^ n := by
    have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := Ring.krullDimLE_iff.mpr
      ((ringKrullDim_stalk_le_topologicalKrullDim x).trans (IsCurve.krullDim_le_one p))
    let S := Algebra.adjoin (X.presheaf.stalk x) {γ}
    have hint (a : Γ(X, U)) : _root_.IsIntegral S (X.germToFunctionField U a) :=
      (hg a).map_of_comp_eq (((X.germToFunctionField U).hom.comp
        (Algebra.adjoin K {g}).val.toRingHom).codRestrict S (hmem x))
        (X.germToFunctionField U).hom (RingHom.ext fun _ ↦ rfl)
    obtain ⟨q, hq, hq1⟩ := exists_aeval_eq_one_of_map_eq_top γ _
      (map_maximalIdeal_eq_top_of_notMem hU hx S hint)
    exact exists_pow_inv_mem_maximalIdeal γ q hq hq1
  by_cases hne : ∃ x, x ∉ U
  swap
  · simp only [not_exists, not_not] at hne
    exact ⟨1, by simp, fun x hx ↦ (hx (hne x)).elim⟩
  obtain ⟨x₀, hx₀⟩ := hne
  have hγ : γ ≠ 0 := (key x₀ hx₀).1
  choose n hn b hb hb' using fun x (hx : x ∉ U) ↦ (key x hx).2
  -- the boundary is finite
  have hfin : ((U : Set X)ᶜ).Finite := U.isOpen.finite_compl_of_topologicalKrullDim_le_one
    (IsCurve.krullDim_le_one p) (Set.nonempty_iff_ne_empty.mpr fun h ↦ by
      obtain ⟨y⟩ := ‹Nonempty U›
      exact (h ▸ y.2 : y.1 ∈ (∅ : Set X)))
  let N : ℕ := ∏ x ∈ hfin.toFinset.attach, n x.1 (hfin.mem_toFinset.mp x.2)
  have hN (x : X) (hx : x ∉ U) : n x hx ∣ N :=
    Finset.dvd_prod_of_mem (fun x : hfin.toFinset ↦ n x.1 (hfin.mem_toFinset.mp x.2))
      (Finset.mem_attach _ ⟨x, hfin.mem_toFinset.mpr hx⟩)
  have hNpos : 0 < N := Finset.prod_pos fun x _ ↦ hn _ _
  refine ⟨g ^ N, by simpa using pow_ne_zero N hγ, fun x hx ↦ ?_⟩
  obtain ⟨c, hc⟩ := hN x hx
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
    omega
  refine ⟨b x hx ^ c, Ideal.pow_mem_of_mem _ (hb x hx) c (Nat.pos_of_ne_zero hc0), ?_⟩
  rw [map_pow, hb', map_pow, ← pow_mul, ← hc, inv_pow]

/-- Sections of an integral scheme over nonempty opens `Vᵢ` with the same image in the function
field glue to a section over `⋃ᵢ Vᵢ`. -/
lemma Scheme.exists_gluing_of_germToFunctionField_eq [IsIntegral X] {ι : Type u}
    (V : ι → X.Opens) [∀ i, Nonempty (V i)] (s : ∀ i, Γ(X, V i)) (φ : X.functionField)
    (hs : ∀ i, X.germToFunctionField (V i) (s i) = φ) :
    ∃ t : Γ(X, ⨆ i, V i), ∀ i, X.presheaf.map (homOfLE (le_iSup V i)).op t = s i := by
  obtain ⟨t, ht, -⟩ := X.sheaf.existsUnique_gluing V s fun i j ↦ by
    obtain ⟨y, hyi, hyj⟩ := nonempty_preirreducible_inter (V i).isOpen (V j).isOpen
      (Set.nonempty_coe_sort.mp (inferInstance : Nonempty (V i)))
      (Set.nonempty_coe_sort.mp (inferInstance : Nonempty (V j)))
    have : Nonempty (V i ⊓ V j : X.Opens) := ⟨⟨y, hyi, hyj⟩⟩
    refine X.germToFunctionField_injective (V i ⊓ V j) ?_
    exact ((TopCat.Presheaf.germ_res_apply X.presheaf (Opens.infLELeft (V i) (V j)) _ _
      (s i)).trans (hs i)).trans ((TopCat.Presheaf.germ_res_apply X.presheaf
        (Opens.infLERight (V i) (V j)) _ _ (s j)).trans (hs j)).symm
  exact ⟨t, ht⟩

/-- Restriction of sections is compatible with the maps to the function field. -/
lemma Scheme.germToFunctionField_map_quasiProjective [IsIntegral X] {U V : X.Opens} (h : V ≤ U)
    [Nonempty V] [Nonempty U] (s : Γ(X, U)) :
    X.germToFunctionField V (X.presheaf.map (homOfLE h).op s) = X.germToFunctionField U s :=
  TopCat.Presheaf.germ_res_apply _ _ _ _ _

/-- **A coordinate cover with an affine chart of an integral curve** (Stacks, Tag 09NB). For a
nonempty affine open `U` of an integral curve `X` over a field, there is a coordinate cover of `X`
by two charts, one of which is `U`: the second chart `W` is the locus where `f⁻¹` is regular, for
`f ∈ Γ(X, U)` with a pole at every boundary point of `U`
(`AlgebraicGeometry.exists_inv_mem_maximalIdeal_of_notMem`), and the ratios are `f` and `f⁻¹`. -/
theorem exists_coordinateCover_of_isAffineOpen {K : Type u} [Field K] (p : X ⟶ Spec (.of K))
    [IsCurve p] [IsIntegral X] {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] :
    ∃ 𝒟 : X.CoordinateCover (ULift.{u} Bool), 𝒟.U ⟨false⟩ = U := by
  classical
  obtain ⟨f, hf0, hf⟩ := exists_inv_mem_maximalIdeal_of_notMem p hU
  choose b hb hb' using hf
  choose V hxV e he using fun (x : {x : X // x ∉ U}) ↦ X.presheaf.exists_germ_eq (b x.1 x.2)
  set φ := (X.germToFunctionField U f)⁻¹
  -- the pieces of the second chart: `D(f)` and neighbourhoods of the boundary points
  have hfu : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f) :=
    X.isUnit_map_of_le_basicOpen f le_rfl
  have hη : genericPoint X ∈ X.basicOpen f := by
    have hηU : genericPoint X ∈ U :=
      ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
    rw [Scheme.mem_basicOpen X f _ hηU]
    exact isUnit_iff_ne_zero.mpr hf0
  let V' : Option {x : X // x ∉ U} → X.Opens
    | none => X.basicOpen f
    | some x => V x
  have hV' (i) : Nonempty (V' i) := by
    rcases i with _ | x
    · exact ⟨⟨_, hη⟩⟩
    · exact ⟨⟨x.1, hxV x⟩⟩
  let s' : ∀ i, Γ(X, V' i)
    | none => ↑hfu.unit⁻¹
    | some x => e x
  have hs' (i) : X.germToFunctionField (V' i) (s' i) = φ := by
    rcases i with _ | x
    · have := hV' none
      have h1 := congrArg (X.germToFunctionField (X.basicOpen f)) hfu.mul_val_inv
      rw [map_mul, map_one, Scheme.germToFunctionField_map_quasiProjective] at h1
      exact (eq_inv_of_mul_eq_one_right h1)
    · have := hV' (some x)
      rw [← Scheme.algebraMap_germ_eq_germToFunctionField X (hxV x)]
      exact (congrArg _ (he x)).trans (hb' x.1 x.2)
  let W : X.Opens := ⨆ i, V' i
  obtain ⟨t, ht⟩ : ∃ t : Γ(X, W), ∀ i, X.presheaf.map (homOfLE (le_iSup V' i)).op t = s' i :=
    Scheme.exists_gluing_of_germToFunctionField_eq V' s' φ hs'
  have hfW : X.basicOpen f ≤ W := le_iSup V' none
  have hUW : Nonempty (U ⊓ W : X.Opens) := ⟨⟨_, X.basicOpen_le f hη, hfW hη⟩⟩
  have hW : Nonempty W := ⟨⟨_, hfW hη⟩⟩
  have htφ : X.germToFunctionField W t = φ := by
    rw [← hs' none, ← ht none, Scheme.germToFunctionField_map_quasiProjective]
  -- `f t = 1` on `U ∩ W`
  have hab : X.presheaf.map (homOfLE (inf_le_left : U ⊓ W ≤ U)).op f *
      X.presheaf.map (homOfLE (inf_le_right : U ⊓ W ≤ W)).op t = 1 := by
    refine X.germToFunctionField_injective (U ⊓ W) ?_
    rw [map_mul, map_one, Scheme.germToFunctionField_map_quasiProjective,
      Scheme.germToFunctionField_map_quasiProjective, htφ]
    exact mul_inv_cancel₀ hf0
  have hunit₁ := IsUnit.of_mul_eq_one _ hab
  have hunit₂ := IsUnit.of_mul_eq_one_right _ hab
  have ha : X.basicOpen f = U ⊓ W := by
    refine le_antisymm (le_inf (X.basicOpen_le f) hfW) ?_
    have := X.basicOpen_of_isUnit hunit₁
    rw [Scheme.basicOpen_res] at this
    exact this.ge.trans inf_le_right
  have hb₀ : X.basicOpen t = U ⊓ W := by
    refine le_antisymm (fun y hy ↦ ⟨?_, X.basicOpen_le t hy⟩) ?_
    · have := X.basicOpen_of_isUnit hunit₂
      rw [Scheme.basicOpen_res] at this
      exact this.ge.trans inf_le_right
    · by_contra hyU
      obtain ⟨i, hyi⟩ := Opens.mem_iSup.mp (X.basicOpen_le t hy)
      rw [Scheme.mem_basicOpen X t y (X.basicOpen_le t hy), ← TopCat.Presheaf.germ_res_apply _
        (homOfLE (le_iSup V' i)) y hyi, ht i] at hy
      have hgerm : X.presheaf.germ (V' i) y hyi (s' i) = b y hyU := by
        refine IsFractionRing.injective (X.presheaf.stalk y) X.functionField ?_
        have := hV' i
        rw [Scheme.algebraMap_germ_eq_germToFunctionField, hs' i, hb' y hyU]
      rw [hgerm] at hy
      exact hb y hyU hy
  have hcov : U ⊔ W = ⊤ := by
    refine eq_top_iff.mpr fun y _ ↦ ?_
    by_cases hy : y ∈ U
    · exact Or.inl hy
    · exact Or.inr (Opens.mem_iSup.mpr ⟨some ⟨y, hy⟩, hxV ⟨y, hy⟩⟩)
  exact ⟨Scheme.CoordinateCover.ofPair f t ha hb₀ hab hcov, rfl⟩

/-- **Integral curves have ample coordinate covers** (Stacks, Tag 09ND). An integral curve over a
field has a coordinate cover by finitely many affine charts: the product of the two-chart covers
of `AlgebraicGeometry.exists_coordinateCover_of_isAffineOpen` for a finite cover by nonempty
affine opens (`AlgebraicGeometry.Scheme.CoordinateCover.exists_isAffineOpen_of_iSup_eq_top`). -/
theorem IsCurve.exists_coordinateCover {K : Type u} [Field K] (p : X ⟶ Spec (.of K))
    [IsCurve p] [IsIntegral X] :
    ∃ (β : Type u) (_ : Finite β) (𝒟 : X.CoordinateCover β), ∀ i, IsAffineOpen (𝒟.U i) := by
  classical
  have : CompactSpace X := (quasiCompact_iff_compactSpace p).mp inferInstance
  let 𝒱 : Type u := {V : X.affineOpens // ((V : X.Opens) : Set X).Nonempty}
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun V : 𝒱 ↦ ((V.1 : X.Opens) : Set X))
    (fun V ↦ V.1.1.isOpen) fun y _ ↦ by
      obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
      exact Set.mem_iUnion.mpr ⟨⟨⟨V, hV⟩, ⟨y, hyV⟩⟩, hyV⟩
  have hne (V : T) : Nonempty (V.1.1 : X.Opens) := V.1.2.to_subtype
  choose 𝒟 h𝒟 using fun V : T ↦ exists_coordinateCover_of_isAffineOpen p V.1.1.2
  refine Scheme.CoordinateCover.exists_isAffineOpen_of_iSup_eq_top 𝒟 (fun _ ↦ ⟨false⟩)
    (fun V ↦ (h𝒟 V).symm ▸ V.1.1.2) (eq_top_iff.mpr fun y _ ↦ ?_)
  obtain ⟨V, hVT, hyV⟩ := Set.mem_iUnion₂.mp (hT (Set.mem_univ y))
  exact Opens.mem_iSup.mpr ⟨⟨V, hVT⟩, (h𝒟 ⟨V, hVT⟩).symm ▸ hyV⟩

end AlgebraicGeometry
