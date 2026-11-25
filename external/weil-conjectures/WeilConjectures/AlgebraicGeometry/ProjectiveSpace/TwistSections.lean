/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.MonomialCech
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfSections
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.Mathlib.Algebra.Category.Ring.Constructions
public import WeilConjectures.Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous
public import WeilConjectures.Topology.Sheaves.CechComparison

/-!
# The Čech complex of the twisting sheaves on projective space

Let `k` be a commutative ring and `Uᵢ = D₊(xᵢ)` the standard opens of `ℙ(n; Spec k)`. For a
nonempty set `s` of coordinates, the sections of `𝒪(m)` over `U_s = ⋂_{i ∈ s} Uᵢ` are the
degree-`m` part of `k[xᵢ, xⱼ⁻¹ : j ∈ s]`: every section is uniquely a finite `k`-linear
combination of Laurent monomials `xᵉ` with `∑ eᵢ = m` and `eᵢ ≥ 0` for `i ∉ s`, and the
restriction maps are the inclusions. Hence the Čech complex of `𝒪(m)` on the standard covering
is the monomial Čech complex `ProjectiveSpace.monomialCechComplex n k m`
(`ProjectiveSpace.cechComplexTwistIso`); this is the first step in computing the cohomology of
`𝒪(m)`.

The computation goes through the integral model `Proj ℤ[Tᵢ]`, of which `ℙ(n; Spec k)` is the
base change and `𝒪(m)` the pullback of the twisting sheaf:

* on `Proj R[Tᵢ]`, the Laurent monomial `xᵉ` is the section `x^{e + N 1_s} / (∏_{i ∈ s} Tᵢ)^N` of
  `𝒪(m)` over `D₊(∏_{i ∈ s} Tᵢ)` (`Proj.twistMonomial`); for `i ∈ s`, `xᵢ ^ m` is a free
  generator there, and `xᵉ = (xᵉ / xᵢ ^ m) • xᵢ ^ m`;
* the functions on `D₊(∏_{i ∈ s} Tᵢ)` of the integral model form the degree-zero localization
  `ℤ[Tᵢ]_{(∏_{i ∈ s} Tᵢ)}`, which is free over `ℤ` on the Laurent monomials of degree `0`
  (`MvPolynomial.awayMonomialBasis`);
* the preimage `U_s` of `D₊(∏_{i ∈ s} Tᵢ)` in `ℙ(n; Spec k)` is the base change of this affine
  open along `Spec k ⟶ Spec ℤ`, so its functions form the pushout `k ⊗ ℤ[Tᵢ]_{(∏_{i ∈ s} Tᵢ)}`,
  which is free over `k` on the same monomials (`ProjectiveSpace.bijective_sum_awayMonomial`);
* pulling back the monomial sections gives the description of the sections of `𝒪(m)` over `U_s`
  (`ProjectiveSpace.bijective_sum_twistMonomialSection`).

## Main definitions

- `AlgebraicGeometry.ProjectiveSpace.twistMonomialSection`: the Laurent monomial `xᵉ` as a
  section of `𝒪(m)` over `U_s`.
- `AlgebraicGeometry.ProjectiveSpace.cechComplexTwistIso`: the Čech complex of `𝒪(m)` on the
  standard covering of `ℙ(n; Spec k)` is the monomial Čech complex.

## Main statements

- `AlgebraicGeometry.ProjectiveSpace.bijective_sum_twistMonomialSection`: the Laurent monomials
  form a `k`-basis of the sections of `𝒪(m)` over `U_s`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Proj

open ProjectiveSpectrum.Twist HomogeneousLocalization MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : Type u} [Fintype n] {R : Type u} [CommRing R] {s : Set n} {m : ℤ}

/-- A point lies in `D₊(∏_{i ∈ s} Xᵢ)` if and only if it lies in every `D₊(Xᵢ)`, `i ∈ s`. -/
lemma mem_basicOpen_monomialToNat_indicator {x : Proj (homogeneousSubmodule n R)} :
    x ∈ Proj.basicOpen _ (monomialToNat R (s.indicator 1)) ↔
      ∀ i ∈ s, x ∈ Proj.basicOpen (homogeneousSubmodule n R) (X i) := by
  simp only [Proj.mem_basicOpen]
  change monomialToNat R (s.indicator 1) ∉ x.asHomogeneousIdeal.toIdeal ↔
    ∀ i ∈ s, X i ∉ x.asHomogeneousIdeal.toIdeal
  rw [monomialToNat_mem_iff]
  constructor
  · intro h i hi hX
    exact h ⟨i, by simp [Set.indicator_of_mem hi], hX⟩
  · rintro h ⟨i, hi, hX⟩
    by_cases his : i ∈ s
    · exact h i his hX
    · simp [Set.indicator_of_notMem his] at hi

lemma basicOpen_monomialToNat_indicator_mono {s t : Set n} (h : t ⊆ s) :
    Proj.basicOpen (homogeneousSubmodule n R) (monomialToNat R (s.indicator 1)) ≤
      Proj.basicOpen _ (monomialToNat R (t.indicator 1)) := fun _ hx ↦
  mem_basicOpen_monomialToNat_indicator.2 fun i hi ↦
    mem_basicOpen_monomialToNat_indicator.1 hx i (h hi)



variable (R m) in
/-- **The section `xᵃ / xᵇ` of `𝒪(m)`** over an open `U` of `Proj R[Xᵢ]` on which `xᵇ` does not
vanish, for nonnegative exponent vectors `a`, `b` with `∑ aᵢ = ∑ bᵢ + m`. -/
noncomputable def twistMonomialFraction {a b : n → ℤ} (h : ∑ i, a i = ∑ i, b i + m) (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (U : (Proj (homogeneousSubmodule n R)).Opens)
    (hU : ∀ x ∈ U, monomialToNat R b ∉ x.asHomogeneousIdeal) :
    Γ(twist (homogeneousSubmodule n R) m, U) :=
  ⟨fun x ↦ degreePart.mk ⟨monomialToNat R a, monomialToNat_mem a⟩
    ⟨monomialToNat R b, monomialToNat_mem b⟩ (hU x.1 x.2) (by
      rw [cast_sum_toNat ha, cast_sum_toNat hb, h]),
    isLocallyFraction_mk (by rw [cast_sum_toNat ha, cast_sum_toNat hb, h]) _ _
      fun x ↦ hU x.1 x.2⟩

lemma coe_twistMonomialFraction_apply {a b : n → ℤ} (h : ∑ i, a i = ∑ i, b i + m) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (U : (Proj (homogeneousSubmodule n R)).Opens)
    (hU : ∀ x ∈ U, monomialToNat R b ∉ x.asHomogeneousIdeal) (x : U) :
    ((twistMonomialFraction (R := R) (m := m) h ha hb U hU).1 x :
      Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
      Localization.mk (monomialToNat R a) ⟨monomialToNat R b, hU x.1 x.2⟩ :=
  rfl


lemma monomialToNat_nsmul_indicator_notMem {x : Proj (homogeneousSubmodule n R)}
    (hx : x ∈ Proj.basicOpen _ (monomialToNat R (s.indicator 1))) (N : ℕ) :
    monomialToNat R (N • s.indicator (1 : n → ℤ)) ∉ x.asHomogeneousIdeal := by
  rw [← monomialToNat_pow (indicator_one_nonneg s)]
  exact fun h ↦ hx (x.isPrime.mem_of_pow_mem N h)

lemma sum_add_nsmul_indicator_eq {e : n → ℤ} (he : ∑ i, e i = m) (N : ℕ) :
    ∑ i, (e + N • s.indicator (1 : n → ℤ)) i = ∑ i, (N • s.indicator (1 : n → ℤ)) i + m := by
  simp only [Pi.add_apply, Finset.sum_add_distrib, he]
  ring

variable (R s) in
/-- **The Laurent monomial `xᵉ` as a section of `𝒪(m)`** over `D₊(∏_{i ∈ s} Xᵢ)`, for an
exponent vector `e` with `∑ eᵢ = m` and `eᵢ ≥ 0` for `i ∉ s`. -/
noncomputable def twistMonomial (e : laurentExponents s m) :
    Γ(twist (homogeneousSubmodule n R) m,
      Proj.basicOpen _ (monomialToNat R (s.indicator 1))) :=
  twistMonomialFraction (R := R) (m := m) (sum_add_nsmul_indicator_eq e.2.1 (negExponentSum e.1))
    (add_nsmul_indicator_nonneg e.2.2 (neg_le_negExponentSum e.1))
    (nsmul_nonneg (indicator_one_nonneg s) _) _
    fun _ hx ↦ monomialToNat_nsmul_indicator_notMem hx _

lemma coe_twistMonomial_apply (e : laurentExponents s m)
    (x : Proj.basicOpen (homogeneousSubmodule n R) (monomialToNat R (s.indicator 1))) :
    ((twistMonomial R s e).1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
      Localization.mk (monomialToNat R (e.1 + negExponentSum e.1 • s.indicator 1))
        ⟨monomialToNat R (negExponentSum e.1 • s.indicator 1),
          monomialToNat_nsmul_indicator_notMem x.2 _⟩ :=
  rfl

/-- The Laurent monomial `xᵉ` on `D₊(∏_{i ∈ t} Xᵢ)` restricts to the Laurent monomial `xᵉ` on
the smaller open `D₊(∏_{i ∈ s} Xᵢ)`, for `t ⊆ s`. -/
lemma twist_presheaf_map_twistMonomial {t : Set n} (hts : t ⊆ s) (e : laurentExponents t m) :
    (twist (homogeneousSubmodule n R) m).presheaf.map
        (homOfLE (basicOpen_monomialToNat_indicator_mono (R := R) hts)).op
        (twistMonomial R t e) =
      twistMonomial R s ⟨e.1, e.2.1, fun i hi ↦ e.2.2 i fun h ↦ hi (hts h)⟩ := by
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  rw [twist_presheaf_map_apply, coe_twistMonomial_apply, coe_twistMonomial_apply]
  have h0 := indicator_one_nonneg s
  have h0' := indicator_one_nonneg t
  refine mk_monomialToNat_eq_mk (add_nsmul_indicator_nonneg e.2.2 (neg_le_negExponentSum e.1))
    (nsmul_nonneg h0' _) (add_nsmul_indicator_nonneg (fun i hi ↦ e.2.2 i fun h ↦ hi (hts h))
      (neg_le_negExponentSum e.1)) (nsmul_nonneg h0 _) ?_ _ _
  abel



variable (s m) in
open Classical in
/-- The exponent vector `m eᵢ` of the monomial `Xᵢ ^ m`, for `i ∈ s`. -/
noncomputable def singleExponent {i : n} (hi : i ∈ s) : laurentExponents s m :=
  ⟨Pi.single i m, by simp, fun j hj ↦ by
    rw [Pi.single_apply, ite_eq_right fun h : j = i ↦ hj (h ▸ hi)]⟩

/-- `xᵢ ^ m` is a free generator of `𝒪(m)` on `D₊(∏_{j ∈ s} Xⱼ)`, for `i ∈ s`. -/
lemma isFreeGenerator_twistMonomial_singleExponent {i : n} (hi : i ∈ s) :
    Scheme.Modules.IsFreeGenerator (twistMonomial R s (singleExponent (s := s) (m := m) hi)) := by
  refine isFreeGenerator_twist_of_mul_eq_one _
    (twistMonomial R s (singleExponent (s := s) (m := -m) hi))
    fun x ↦ ?_
  rw [coe_twistMonomial_apply, coe_twistMonomial_apply, Localization.mk_mul,
    ← Localization.mk_one]
  have h0 := indicator_one_nonneg s
  have ha := add_nsmul_indicator_nonneg (singleExponent (s := s) (m := m) hi).2.2
    (neg_le_negExponentSum (singleExponent (s := s) (m := m) hi).1)
  have ha' := add_nsmul_indicator_nonneg (singleExponent (s := s) (m := -m) hi).2.2
    (neg_le_negExponentSum (singleExponent (s := s) (m := -m) hi).1)
  have hN := nsmul_nonneg h0 (negExponentSum (singleExponent (s := s) (m := m) hi).1)
  have hN' := nsmul_nonneg h0 (negExponentSum (singleExponent (s := s) (m := -m) hi).1)
  refine mk_eq_mk_of_monomialToNat (add_nonneg ha ha') (add_nonneg hN hN') le_rfl le_rfl
    (monomialToNat_mul ha ha') ?_ monomialToNat_zero.symm monomialToNat_zero.symm ?_
  · exact monomialToNat_mul hN hN'
  · ext j
    simp only [singleExponent, Pi.add_apply, Pi.zero_apply, Pi.smul_apply, Pi.single_apply]
    split_ifs <;> ring

/-- The value at a point of the function `xᵉ` on `D₊(∏_{i ∈ s} Xᵢ)`. -/
lemma val_awayToSection_awayMonomial_apply (e : laurentExponents s 0)
    (x : Proj.basicOpen (homogeneousSubmodule n R) (monomialToNat R (s.indicator 1))) :
    ((Proj.awayToSection _ _ (awayMonomial R s e)).1 x).val =
      Localization.mk (monomialToNat R (e.1 + negExponentSum e.1 • s.indicator 1))
        ⟨monomialToNat R (negExponentSum e.1 • s.indicator 1),
          monomialToNat_nsmul_indicator_notMem x.2 _⟩ := by
  have := ProjectiveSpectrum.Proj.awayToSection_apply (homogeneousSubmodule n R)
    (monomialToNat R (s.indicator 1)) (awayMonomial R s e) x
  erw [this]
  rw [awayMonomial, Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk',
    RingHom.id_apply, ← Localization.mk_eq_mk']
  have h0 := indicator_one_nonneg s
  have ha := add_nsmul_indicator_nonneg e.2.2 (neg_le_negExponentSum e.1)
  exact mk_eq_mk_of_monomialToNat ha (nsmul_nonneg h0 _) ha (nsmul_nonneg h0 _) rfl
    (monomialToNat_pow h0 _) rfl rfl rfl

open Classical in
variable (m) in
/-- The exponent vector `e - m eᵢ` of `xᵉ / xᵢ ^ m`, for `i ∈ s`. -/
noncomputable def shiftExponent {i : n} (hi : i ∈ s) (e : laurentExponents s m) :
    laurentExponents s 0 :=
  ⟨e.1 - Pi.single i m, by simp [Finset.sum_sub_distrib, e.2.1], fun j hj ↦ by
    rw [Pi.sub_apply, Pi.single_apply, ite_eq_right fun h : j = i ↦ hj (h ▸ hi), sub_zero]
    exact e.2.2 j hj⟩

/-- **`xᵉ = (xᵉ / xᵢ ^ m) xᵢ ^ m`** in `𝒪(m)` over `D₊(∏_{j ∈ s} Xⱼ)`, for `i ∈ s`. -/
lemma twistMonomial_eq_smul {i : n} (hi : i ∈ s) (e : laurentExponents s m) :
    twistMonomial R s e = Proj.awayToSection _ _ (awayMonomial R s (shiftExponent m hi e)) •
      twistMonomial R s (singleExponent (s := s) (m := m) hi) := by
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  change ((twistMonomial R s e).1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) = _
  rw [coe_twist_smul_apply, coe_twistMonomial_apply, coe_twistMonomial_apply,
    val_awayToSection_awayMonomial_apply, Localization.mk_mul]
  have h0 := indicator_one_nonneg s
  have ha := add_nsmul_indicator_nonneg e.2.2 (neg_le_negExponentSum e.1)
  have hb := add_nsmul_indicator_nonneg (shiftExponent m hi e).2.2
    (neg_le_negExponentSum (shiftExponent m hi e).1)
  have hc := add_nsmul_indicator_nonneg (singleExponent (s := s) (m := m) hi).2.2
    (neg_le_negExponentSum (singleExponent (s := s) (m := m) hi).1)
  have hN := nsmul_nonneg h0 (negExponentSum (shiftExponent m hi e).1)
  have hN' := nsmul_nonneg h0 (negExponentSum (singleExponent (s := s) (m := m) hi).1)
  refine mk_eq_mk_of_monomialToNat ha (nsmul_nonneg h0 _) (add_nonneg hb hc)
    (add_nonneg hN hN') rfl rfl (monomialToNat_mul hb hc) (monomialToNat_mul hN hN') ?_
  ext j
  simp only [shiftExponent, singleExponent, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    Pi.single_apply]
  split_ifs <;> ring

end AlgebraicGeometry.Proj

namespace AlgebraicGeometry.ProjectiveSpace

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n : Type u) (S : Scheme.{u})

/-- The preimage in `ℙ(n; S)` of an open `W` of the integral model `ℙⁿ_ℤ` is the base change of
`W` along `S ⟶ Spec ℤ`. -/
lemma isPullback_preimage (W : (Proj.projectiveSpaceOverAffine n (ULift.{u} ℤ)).Opens) :
    IsPullback ((toProjInt n S).resLE W (toProjInt n S ⁻¹ᵁ W) le_rfl)
      ((toProjInt n S ⁻¹ᵁ W).ι ≫ ℙ(n; S) ↘ S) (terminal.from W.toScheme) (terminal.from S) := by
  have h := (isPullback_morphismRestrict (toProjInt n S) W).paste_vert
    (isPullback_over_toProjInt n S).flip
  have hr : (toProjInt n S).resLE W (toProjInt n S ⁻¹ᵁ W) le_rfl = toProjInt n S ∣_ W :=
    Scheme.Hom.resLE_eq_morphismRestrict ..
  exact h.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by rw [Iso.refl_hom, Category.comp_id]; exact hr.symm.trans (Category.id_comp _).symm)
    (by rw [Iso.refl_hom, Category.comp_id]; exact (Category.id_comp _).symm)
    (terminal.hom_ext _ _) (terminal.hom_ext _ _)


variable {n} [Fintype n]

/-- The monomial basis of `ℤ[Xᵢ]_{(∏_{i ∈ s} Xᵢ)}`, as a `ℤ`-basis. -/
noncomputable def awayMonomialBasisInt (s : Set n) :
    Module.Basis (laurentExponents s 0) ℤ
      (HomogeneousLocalization.Away (homogeneousSubmodule n (ULift.{u} ℤ))
        (monomialToNat (ULift.{u} ℤ) (s.indicator 1))) :=
  (awayMonomialBasis (ULift.{u} ℤ) s).mapCoeffs ULift.ringEquiv fun c x ↦ by
    conv_rhs => rw [show c = ((c.down : ℤ) : ULift.{u} ℤ) from ULift.ext (by simp)]
    rw [Int.cast_smul_eq_zsmul]
    rfl

@[simp]
lemma awayMonomialBasisInt_apply (s : Set n) (e : laurentExponents s 0) :
    awayMonomialBasisInt s e = awayMonomial (ULift.{u} ℤ) s e := by
  simp [awayMonomialBasisInt]

lemma indicatorDegree_pos {s : Set n} (hs : s.Nonempty) : 0 < indicatorDegree s := by
  obtain ⟨i, hi⟩ := hs
  have : 0 < (s.indicator (1 : n → ℤ) i).toNat := by simp [Set.indicator_of_mem hi]
  exact this.trans_le (Finset.single_le_sum (f := fun j ↦ (s.indicator (1 : n → ℤ) j).toNat)
    (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i))

variable (n) in
/-- The open `D₊(∏_{i ∈ s} Xᵢ)` of the integral model `ℙⁿ_ℤ`. -/
noncomputable abbrev basicOpenInt (s : Set n) :
    (Proj.projectiveSpaceOverAffine n (ULift.{u} ℤ)).Opens :=
  Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (monomialToNat _ (s.indicator 1))

/-- **The functions on `⋂_{i ∈ s} D₊(xᵢ) ⊆ ℙ(n; Spec k)`**: every function is uniquely a finite
`k`-linear combination of the Laurent monomials `xᵉ`, `∑ eᵢ = 0`, `eᵢ ≥ 0` for `i ∉ s`. This is
the base change to `k` of the monomial basis of `ℤ[Xᵢ]_{(∏_{i ∈ s} Xᵢ)}`. -/
theorem bijective_sum_awayMonomial (k : Type u) [CommRing k] {s : Set n} (hs : s.Nonempty) :
    Function.Bijective fun c : laurentExponents s 0 →₀ k ↦ c.sum fun e r ↦
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (ℙ(n; Spec (.of k)) ↘ Spec (.of k)).appTop ≫
        ℙ(n; Spec (.of k)).presheaf.map (homOfLE le_top).op) r *
      (Proj.awayToSection _ _ ≫ (toProjInt n (Spec (.of k))).appLE (basicOpenInt n s)
        (toProjInt n (Spec (.of k)) ⁻¹ᵁ basicOpenInt n s) le_rfl)
        (awayMonomial (ULift.{u} ℤ) s e) := by
  have hdeg := indicatorDegree_pos hs
  have hf := monomialToNat_indicator_mem (ULift.{u} ℤ) s
  have hW : IsAffineOpen (basicOpenInt n s) := Proj.isAffineOpen_basicOpen _ _ hf hdeg
  have : IsAffine (basicOpenInt n s).toScheme := hW
  have hpo := isPushout_appTop_of_isPullback (isPullback_preimage n (Spec (.of k))
    (basicOpenInt n s))
  have hpo' := hpo.of_iso (Iso.refl _)
    ((basicOpenInt n s).topIso ≪≫ (Proj.basicOpenIsoAway _ _ hf hdeg).symm)
    (Scheme.ΓSpecIso (.of k)) (toProjInt n (Spec (.of k)) ⁻¹ᵁ basicOpenInt n s).topIso
    (f' := Scheme.Hom.appTop (terminal.from (basicOpenInt n s).toScheme) ≫
      (basicOpenInt n s).topIso.hom ≫
      (Proj.basicOpenIsoAway _ _ hf hdeg).inv)
    (g' := Scheme.Hom.appTop (terminal.from (Spec (.of k))) ≫ (Scheme.ΓSpecIso (.of k)).hom)
    (inl' := Proj.awayToSection _ _ ≫ (toProjInt n (Spec (.of k))).appLE (basicOpenInt n s)
        (toProjInt n (Spec (.of k)) ⁻¹ᵁ basicOpenInt n s) le_rfl)
    (inr' := (Scheme.ΓSpecIso (.of k)).inv ≫ (ℙ(n; Spec (.of k)) ↘ Spec (.of k)).appTop ≫
        ℙ(n; Spec (.of k)).presheaf.map (homOfLE le_top).op)
    (by simp) (by simp) ?_ ?_
  · convert CommRingCat.IsPushout.bijective_sum_mul hpo' surjective_intCastRingHom_Γ_terminal
      (awayMonomialBasisInt s) using 1
    ext c
    simp
  · rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Iso.trans_hom, Iso.symm_hom,
      Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      ← Proj.basicOpenIsoAway_hom _ _ hf hdeg, Category.assoc]
    erw [Iso.inv_hom_id_assoc]
  · rw [Iso.hom_inv_id_assoc, Scheme.Hom.comp_appTop, Category.assoc,
      Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom, ← Functor.map_comp]
    rfl

section Twist

open Scheme.Modules

variable {m : ℤ}

/-- **The Laurent monomial `xᵉ` as a section of `𝒪(m)`** over `⋂_{i ∈ s} D₊(xᵢ) ⊆ ℙ(n; S)`, for
an exponent vector `e` with `∑ eᵢ = m` and `eᵢ ≥ 0` for `i ∉ s`: the pullback of the section
`xᵉ` of `𝒪(m)` on the integral model. -/
noncomputable def twistMonomialSection (s : Set n) (e : laurentExponents s m) :
    Γ(twist n S m, toProjInt n S ⁻¹ᵁ basicOpenInt n s) :=
  pullbackSection (toProjInt n S) (Proj.twistMonomial (ULift.{u} ℤ) s e)

variable {S}

lemma twist_presheaf_map_twistMonomialSection {s t : Set n} (hts : t ⊆ s)
    (e : laurentExponents t m) :
    (twist n S m).presheaf.map (homOfLE ((toProjInt n S).preimage_mono
        (Proj.basicOpen_monomialToNat_indicator_mono (R := ULift.{u} ℤ) hts))).op
        (twistMonomialSection S t e) =
      twistMonomialSection S s ⟨e.1, e.2.1, fun i hi ↦ e.2.2 i fun h ↦ hi (hts h)⟩ := by
  have h := pullbackSection_map (toProjInt n S)
    (Proj.basicOpen_monomialToNat_indicator_mono (R := ULift.{u} ℤ) hts)
    (Proj.twistMonomial (ULift.{u} ℤ) t e)
  rw [Proj.twist_presheaf_map_twistMonomial hts] at h
  exact h.symm

lemma twistMonomialSection_eq_smul {s : Set n} {i : n} (hi : i ∈ s) (e : laurentExponents s m) :
    twistMonomialSection S s e =
      (Proj.awayToSection _ _ ≫ (toProjInt n S).appLE (basicOpenInt n s)
        (toProjInt n S ⁻¹ᵁ basicOpenInt n s) le_rfl)
        (awayMonomial (ULift.{u} ℤ) s (Proj.shiftExponent m hi e)) •
        twistMonomialSection S s (Proj.singleExponent (s := s) (m := m) hi) := by
  rw [twistMonomialSection, Proj.twistMonomial_eq_smul hi e, pullbackSection_smul,
    Scheme.Hom.appLE_eq_app]
  rfl

lemma isFreeGenerator_twistMonomialSection_singleExponent {s : Set n} {i : n} (hi : i ∈ s) :
    IsFreeGenerator (twistMonomialSection S s (Proj.singleExponent (s := s) (m := m) hi)) :=
  (Proj.isFreeGenerator_twistMonomial_singleExponent hi).pullback_unit_app (toProjInt n S)

open Classical in
variable (m) in
/-- Shifting exponent vectors by `m eᵢ`, for `i ∈ s`, identifies the Laurent monomials of
degree `m` regular on `⋂_{j ∈ s} D₊(xⱼ)` with those of degree `0`. -/
noncomputable def shiftExponentEquiv {s : Set n} {i : n} (hi : i ∈ s) :
    laurentExponents s m ≃ laurentExponents s 0 where
  toFun := Proj.shiftExponent m hi
  invFun e := ⟨e.1 + Pi.single i m, by simp [Finset.sum_add_distrib, e.2.1], fun j hj ↦ by
    rw [Pi.add_apply, Pi.single_apply, ite_eq_right fun h : j = i ↦ hj (h ▸ hi), add_zero]
    exact e.2.2 j hj⟩
  left_inv e := Subtype.ext (by simp [Proj.shiftExponent])
  right_inv e := Subtype.ext (by simp [Proj.shiftExponent])

/-- **The sections of `𝒪(m)` over `⋂_{i ∈ s} D₊(xᵢ) ⊆ ℙ(n; Spec k)`** for nonempty `s`: every
section is uniquely a finite `k`-linear combination of the Laurent monomials `xᵉ` with
`∑ eᵢ = m` and `eᵢ ≥ 0` for `i ∉ s`. -/
theorem bijective_sum_twistMonomialSection (k : Type u) [CommRing k] {s : Set n}
    (hs : s.Nonempty) (m : ℤ) :
    Function.Bijective fun c : laurentExponents s m →₀ k ↦ c.sum fun e r ↦
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (ℙ(n; Spec (.of k)) ↘ Spec (.of k)).appTop ≫
        ℙ(n; Spec (.of k)).presheaf.map
          (homOfLE (le_top : toProjInt n (Spec (.of k)) ⁻¹ᵁ basicOpenInt n s ≤ ⊤)).op) r •
        twistMonomialSection (Spec (.of k)) s e := by
  obtain ⟨i, hi⟩ := hs
  have hfun : (fun c : laurentExponents s m →₀ k ↦ c.sum fun e r ↦
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (ℙ(n; Spec (.of k)) ↘ Spec (.of k)).appTop ≫
        ℙ(n; Spec (.of k)).presheaf.map
          (homOfLE (le_top : toProjInt n (Spec (.of k)) ⁻¹ᵁ basicOpenInt n s ≤ ⊤)).op) r •
        twistMonomialSection (Spec (.of k)) s e) =
      (fun r ↦ r • twistMonomialSection (Spec (.of k)) s
        (Proj.singleExponent (s := s) (m := m) hi)) ∘
      (fun c : laurentExponents s 0 →₀ k ↦ c.sum fun e r ↦
        ((Scheme.ΓSpecIso (.of k)).inv ≫ (ℙ(n; Spec (.of k)) ↘ Spec (.of k)).appTop ≫
          ℙ(n; Spec (.of k)).presheaf.map
          (homOfLE (le_top : toProjInt n (Spec (.of k)) ⁻¹ᵁ basicOpenInt n s ≤ ⊤)).op) r *
        (Proj.awayToSection _ _ ≫ (toProjInt n (Spec (.of k))).appLE (basicOpenInt n s)
          (toProjInt n (Spec (.of k)) ⁻¹ᵁ basicOpenInt n s) le_rfl)
          (awayMonomial (ULift.{u} ℤ) s e)) ∘
      Finsupp.equivMapDomain (shiftExponentEquiv m hi) := by
    funext c
    simp only [Function.comp_apply, Finsupp.sum_equivMapDomain]
    rw [Finsupp.sum, Finsupp.sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun e _ ↦ ?_
    rw [twistMonomialSection_eq_smul hi e, mul_smul]
    rfl
  rw [hfun]
  exact (isFreeGenerator_twistMonomialSection_singleExponent hi).bijective.comp
    ((bijective_sum_awayMonomial k ⟨i, hi⟩).comp
      (Finsupp.domCongr (M := k) (shiftExponentEquiv m hi)).bijective)

end Twist

section Cech

open Scheme.Modules Opposite


/-- The preimage of `D₊(∏_{i ∈ s} Xᵢ)` is contained in the standard open `D₊(xᵢ)`, `i ∈ s`. -/
lemma preimage_basicOpenInt_le_standardOpen {s : Set n} {i : n} (hi : i ∈ s) :
    toProjInt n S ⁻¹ᵁ basicOpenInt n s ≤ standardOpen n S i := fun _ hx ↦
  Proj.mem_basicOpen_monomialToNat_indicator.1 hx i hi

/-- **The intersection `U_σ = D₊(x_{σ 0}) ∩ ⋯ ∩ D₊(x_{σ p})` of standard opens** of `ℙ(n; S)` is
the preimage of `D₊(∏_{i ∈ σ} Xᵢ)`. -/
lemma preimage_basicOpenInt_range {p : ℕ} (σ : Fin (p + 1) → n) :
    toProjInt n S ⁻¹ᵁ basicOpenInt n (Set.range σ) = ⨅ l, standardOpen n S (σ l) := by
  refine le_antisymm
    (le_iInf fun l ↦ preimage_basicOpenInt_le_standardOpen S (Set.mem_range_self l))
    fun x hx ↦ ?_
  refine Proj.mem_basicOpen_monomialToNat_indicator.2 ?_
  rintro _ ⟨l, rfl⟩
  exact (iInf_le (fun l ↦ standardOpen n S (σ l)) l) hx

variable (k : Type u) [CommRing k] (m : ℤ)

/-- The `k`-linear map sending a finitely supported family of coefficients `(cₑ)` to the section
`∑ cₑ xᵉ` of `𝒪(m)` over `⋂_{i ∈ s} D₊(xᵢ) ⊆ ℙ(n; Spec k)`. -/
noncomputable def twistMonomialLinearMap (s : Set n) :
    (laurentExponents s m →₀ k) →ₗ[k] (ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (ℙ(n; Spec (.of k)) ↘ Spec (.of k)).appTop).hom).obj
        ((twist n (Spec (.of k)) m).presheafModuleCat.obj
          (op (toProjInt n (Spec (.of k)) ⁻¹ᵁ basicOpenInt n s))) :=
  Finsupp.linearCombination k fun e ↦ twistMonomialSection (Spec (.of k)) s e

variable {k m}

lemma bijective_twistMonomialLinearMap {s : Set n} (hs : s.Nonempty) :
    Function.Bijective (twistMonomialLinearMap k m s) :=
  bijective_sum_twistMonomialSection k hs m

/-- The sections `∑ cₑ xᵉ` are compatible with restriction. -/
lemma twistMonomialLinearMap_mapDomain {s t : Set n} (hts : t ⊆ s)
    (c : laurentExponents t m →₀ k) :
    twistMonomialLinearMap k m s (c.mapDomain (Set.inclusion (laurentExponents_mono hts m))) =
      (twist n (Spec (.of k)) m).presheafModuleCat.map (homOfLE ((toProjInt n _).preimage_mono
        (Proj.basicOpen_monomialToNat_indicator_mono (R := ULift.{u} ℤ) hts))).op
        (twistMonomialLinearMap k m t c) := by
  rw [twistMonomialLinearMap, twistMonomialLinearMap, Finsupp.linearCombination_mapDomain,
    Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, map_finsuppSum]
  refine Finsupp.sum_congr fun e _ ↦ ?_
  rw [ModuleCat.restrictScalars.smul_def, ModuleCat.restrictScalars.smul_def]
  erw [(((twist n (Spec (.of k)) m).presheafModuleCat.map _).hom).map_smul]
  congr 1
  exact (twist_presheaf_map_twistMonomialSection hts e).symm

variable (k m) in
/-- The degree-`p` component of the comparison map from the monomial Čech complex to the Čech
complex of `𝒪(m)` on the standard covering of `ℙ(n; Spec k)`, as a function: a family of
finitely supported coefficients `(c_σ)` goes to the family of sections `∑ c_{σ,e} xᵉ` over
`U_σ`. -/
noncomputable def monomialCechToCechFun (p : ℕ) (c : ProjectiveSpace.MonomialCechCochain n k m p) :
    ((cechComplexFunctor (standardOpen n (Spec (.of k)))).obj
      (twist n (Spec (.of k)) m).presheafModuleCat).X p :=
  (ModuleCat.piIsoPi (fun σ : Fin (p + 1) → n ↦
      (twist n (Spec (.of k)) m).presheafModuleCat.obj
        (op (∏ᶜ fun l ↦ standardOpen n (Spec (.of k)) (σ l))))).inv fun σ ↦
    (twist n (Spec (.of k)) m).presheafModuleCat.map
      (homOfLE ((TopCat.Presheaf.piObj_le_iInf _ σ).trans
        (preimage_basicOpenInt_range _ σ).ge)).op
      (twistMonomialLinearMap k m (Set.range σ) (Finsupp.supportedEquivFinsupp _ (c σ)))

lemma cechComplexFunctorπ_monomialCechToCechFun (p : ℕ)
    (c : ProjectiveSpace.MonomialCechCochain n k m p) (σ : Fin (p + 1) → n) :
    TopCat.Presheaf.cechComplexFunctorπ (standardOpen n (Spec (.of k)))
      (twist n (Spec (.of k)) m).presheafModuleCat p σ (monomialCechToCechFun k m p c) =
      (twist n (Spec (.of k)) m).presheafModuleCat.map
        (homOfLE ((TopCat.Presheaf.piObj_le_iInf _ σ).trans
          (preimage_basicOpenInt_range _ σ).ge)).op
        (twistMonomialLinearMap k m (Set.range σ) (Finsupp.supportedEquivFinsupp _ (c σ))) :=
  TopCat.Presheaf.cechComplexFunctorπ_piIsoPi_inv _ _ _ σ

variable (k m) in
/-- The degree-`p` component of the comparison map from the monomial Čech complex to the Čech
complex of `𝒪(m)` on the standard covering of `ℙ(n; Spec k)`, as a `k`-linear map. -/
noncomputable def monomialCechToCech (p : ℕ) :
    ProjectiveSpace.MonomialCechCochain n k m p →ₗ[k] (ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (ℙ(n; Spec (.of k)) ↘ Spec (.of k)).appTop).hom).obj
        (((cechComplexFunctor (standardOpen n (Spec (.of k)))).obj
          (twist n (Spec (.of k)) m).presheafModuleCat).X p) where
  toFun := monomialCechToCechFun k m p
  map_add' c c' := by
    refine TopCat.Presheaf.cechComplexFunctor_ext (standardOpen n (Spec (.of k)))
      (twist n (Spec (.of k)) m).presheafModuleCat fun σ ↦ ?_
    change _ = TopCat.Presheaf.cechComplexFunctorπ (standardOpen n (Spec (.of k)))
      (twist n (Spec (.of k)) m).presheafModuleCat p σ
      (monomialCechToCechFun k m p c + monomialCechToCechFun k m p c')
    rw [map_add, cechComplexFunctorπ_monomialCechToCechFun,
      cechComplexFunctorπ_monomialCechToCechFun, cechComplexFunctorπ_monomialCechToCechFun]
    simp only [Pi.add_apply, map_add]
  map_smul' r c := by
    refine TopCat.Presheaf.cechComplexFunctor_ext (standardOpen n (Spec (.of k)))
      (twist n (Spec (.of k)) m).presheafModuleCat fun σ ↦ ?_
    change _ = TopCat.Presheaf.cechComplexFunctorπ (standardOpen n (Spec (.of k)))
      (twist n (Spec (.of k)) m).presheafModuleCat p σ
      (((Scheme.ΓSpecIso (.of k)).inv ≫ (ℙ(n; Spec (.of k)) ↘ Spec (.of k)).appTop).hom r •
        monomialCechToCechFun k m p c)
    rw [(TopCat.Presheaf.cechComplexFunctorπ (standardOpen n (Spec (.of k)))
      (twist n (Spec (.of k)) m).presheafModuleCat p σ).hom.map_smul,
      cechComplexFunctorπ_monomialCechToCechFun, cechComplexFunctorπ_monomialCechToCechFun,
      Pi.smul_apply, LinearEquiv.map_smul, LinearMap.map_smul,
      ModuleCat.restrictScalars.smul_def]
    exact ((twist n (Spec (.of k)) m).presheafModuleCat.map _).hom.map_smul _ _

omit [Fintype n] in
lemma supportedEquivFinsupp_apply (s : Set (n → ℤ)) (x : Finsupp.supported k k s) (e : s) :
    Finsupp.supportedEquivFinsupp s x e = (x : (n → ℤ) →₀ k) e := by
  simp

/-- The differential of the monomial Čech complex, on the coefficients of a component. -/
lemma supportedEquivFinsupp_monomialCechComplex_d (p : ℕ)
    (c : ProjectiveSpace.MonomialCechCochain n k m p) (τ : Fin (p + 2) → n) :
    Finsupp.supportedEquivFinsupp (laurentExponents (Set.range τ) m)
        (((ProjectiveSpace.monomialCechComplex n k m).d p (p + 1)).hom c τ) =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
        (Finsupp.supportedEquivFinsupp (laurentExponents (Set.range (τ ∘ i.succAbove)) m)
          (c (τ ∘ i.succAbove))).mapDomain
          (Set.inclusion (laurentExponents_mono (Set.range_comp_subset_range _ _) m)) := by
  ext e
  rw [supportedEquivFinsupp_apply, Finsupp.finsetSum_apply]
  have h := ProjectiveSpace.monomialCechComplex_d_apply p c τ e.1
  refine h.trans (Finset.sum_congr rfl fun i _ ↦ ?_)
  rw [Finsupp.smul_apply]
  congr 1
  by_cases he : e.1 ∈ laurentExponents (Set.range (τ ∘ i.succAbove)) m
  · rw [show e = Set.inclusion (laurentExponents_mono (Set.range_comp_subset_range _ _) m)
        ⟨e.1, he⟩ from rfl, Finsupp.mapDomain_apply_of_injective (Set.inclusion_injective _),
      supportedEquivFinsupp_apply]
  · rw [Finsupp.mapDomain_of_notMem_range _ _ fun ⟨e', he'⟩ ↦ he (he' ▸ e'.2)]
    exact ProjectiveSpace.MonomialCechCochain.coeff_eq_zero_of_notMem c _ he

/-- The comparison maps commute with the differentials. -/
lemma monomialCechToCechFun_d (p : ℕ) (c : ProjectiveSpace.MonomialCechCochain n k m p) :
    ((cechComplexFunctor (standardOpen n (Spec (.of k)))).obj
      (twist n (Spec (.of k)) m).presheafModuleCat).d p (p + 1)
        (monomialCechToCechFun k m p c) =
      monomialCechToCechFun k m (p + 1)
        (((ProjectiveSpace.monomialCechComplex n k m).d p (p + 1)).hom c) := by
  refine TopCat.Presheaf.cechComplexFunctor_ext (standardOpen n (Spec (.of k)))
    (twist n (Spec (.of k)) m).presheafModuleCat fun τ ↦ ?_
  rw [TopCat.Presheaf.cechComplexFunctorπ_d_apply, cechComplexFunctorπ_monomialCechToCechFun,
    supportedEquivFinsupp_monomialCechComplex_d, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have h : (∏ᶜ fun l ↦ standardOpen n (Spec (.of k)) (τ l)) ≤
      toProjInt n (Spec (.of k)) ⁻¹ᵁ basicOpenInt n (Set.range (τ ∘ i.succAbove)) :=
    (TopCat.Presheaf.piObj_le_iInf _ τ).trans ((preimage_basicOpenInt_range _ τ).ge.trans
      ((toProjInt n _).preimage_mono (Proj.basicOpen_monomialToNat_indicator_mono
        (Set.range_comp_subset_range _ _))))
  rw [cechComplexFunctorπ_monomialCechToCechFun, map_zsmul, map_zsmul]
  congr 1
  rw [twistMonomialLinearMap_mapDomain, TopCat.Presheaf.map_map_apply _ _ _ (homOfLE h).op]
  · exact TopCat.Presheaf.map_map_apply _ _ _ (homOfLE h).op _
  · exact Set.range_comp_subset_range _ _

/-- The comparison maps are bijective. -/
lemma bijective_monomialCechToCech (p : ℕ) :
    Function.Bijective (monomialCechToCech k m (n := n) p) := by
  have hle (σ : Fin (p + 1) → n) : toProjInt n (Spec (.of k)) ⁻¹ᵁ basicOpenInt n (Set.range σ) ≤
      ∏ᶜ fun l ↦ standardOpen n (Spec (.of k)) (σ l) :=
    (preimage_basicOpenInt_range _ σ).le.trans (TopCat.Presheaf.iInf_le_piObj _ σ)
  have hne (σ : Fin (p + 1) → n) : (Set.range σ).Nonempty := Set.range_nonempty σ
  constructor
  · intro c c' hcc
    change monomialCechToCechFun k m p c = monomialCechToCechFun k m p c' at hcc
    funext σ
    have hπ := congrArg (fun x ↦ (twist n (Spec (.of k)) m).presheafModuleCat.map
      (homOfLE (hle σ)).op (TopCat.Presheaf.cechComplexFunctorπ (standardOpen n (Spec (.of k)))
        (twist n (Spec (.of k)) m).presheafModuleCat p σ x)) hcc
    simp only [cechComplexFunctorπ_monomialCechToCechFun] at hπ
    rw [TopCat.Presheaf.map_map_apply _ _ _ (𝟙 _), TopCat.Presheaf.map_map_apply _ _ _ (𝟙 _),
      TopCat.Presheaf.map_apply_self, TopCat.Presheaf.map_apply_self] at hπ
    exact (Finsupp.supportedEquivFinsupp _).injective
      ((bijective_twistMonomialLinearMap (hne σ)).1 hπ)
  · intro x
    choose y hy using fun σ : Fin (p + 1) → n ↦
      (bijective_twistMonomialLinearMap (k := k) (m := m) (hne σ)).2
        ((twist n (Spec (.of k)) m).presheafModuleCat.map (homOfLE (hle σ)).op
          (TopCat.Presheaf.cechComplexFunctorπ (standardOpen n (Spec (.of k)))
            (twist n (Spec (.of k)) m).presheafModuleCat p σ x))
    refine ⟨fun σ ↦ (Finsupp.supportedEquivFinsupp (M := k) (R := k)
      (laurentExponents (Set.range σ) m)).symm (y σ), ?_⟩
    refine TopCat.Presheaf.cechComplexFunctor_ext (standardOpen n (Spec (.of k)))
      (twist n (Spec (.of k)) m).presheafModuleCat fun σ ↦ ?_
    change TopCat.Presheaf.cechComplexFunctorπ (standardOpen n (Spec (.of k)))
      (twist n (Spec (.of k)) m).presheafModuleCat p σ (monomialCechToCechFun k m p _) = _
    rw [cechComplexFunctorπ_monomialCechToCechFun, LinearEquiv.apply_symm_apply, hy,
      TopCat.Presheaf.map_map_apply _ _ _ (𝟙 _), TopCat.Presheaf.map_apply_self]

variable (n k m) in
/-- **The Čech complex of `𝒪(m)` on the standard covering of `ℙ(n; Spec k)` is the monomial Čech
complex**, as complexes of `k`-modules: the section `∑ cₑ xᵉ` over `U_σ` corresponds to the
family of coefficients `(cₑ)`. -/
noncomputable def cechComplexTwistIso :
    ((ModuleCat.restrictScalars
        ((Scheme.ΓSpecIso (.of k)).inv ≫
          (ℙ(n; Spec (.of k)) ↘ Spec (.of k)).appTop).hom).mapHomologicalComplex _).obj
      ((cechComplexFunctor (standardOpen n (Spec (.of k)))).obj
        (twist n (Spec (.of k)) m).presheafModuleCat) ≅
      ProjectiveSpace.monomialCechComplex n k m :=
  (HomologicalComplex.Hom.isoOfComponents (fun p ↦
    (LinearEquiv.ofBijective (monomialCechToCech k m p)
      (bijective_monomialCechToCech p)).toModuleIso) (by
    rintro p _ rfl
    ext c
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, Functor.mapHomologicalComplex_obj_d,
      LinearEquiv.toModuleIso_hom, ModuleCat.hom_ofHom]
    exact monomialCechToCechFun_d p c)).symm

end Cech

end AlgebraicGeometry.ProjectiveSpace
