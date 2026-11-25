/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Polynomial.Derivation
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.Modules.LocalDerivation
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TwistSections

/-!
# The canonical sheaf of the projective line

Let `k` be a field and `ℙ¹_k = ProjectiveLine (Spec k)`, covered by the standard opens
`U₀ = D₊(x₀)` and `U₁ = D₊(x₁)` with coordinates `t = x₁ / x₀` and `s = x₀ / x₁`. We show
`Ω¹_{ℙ¹/k} ≅ 𝒪(-2)`.

The sheaf of differentials has no local description in this library yet; we only use its
universal property. The derivation `d / dt` of `Γ(U₀) = k[t]`, with values in `𝒪(-2)` through
its generator `x₀⁻²` over `U₀`, and `-d / ds` on `U₁`, extend to local derivations over the
affine opens `U₀` and `U₁` (`AlgebraicGeometry.Scheme.Modules.LocalDerivation.ofIsAffineOpen`),
agree on `U₀ ∩ U₁` by the chain rule, and glue to a derivation `𝒪 → 𝒪(-2)`, that is a morphism
`Ω¹ ⟶ 𝒪(-2)`. Conversely the generators `x₀⁻²` and `x₁⁻²` of `𝒪(-2)` go to `dt` and `-ds`,
which satisfy the same transition rule `dt = -t² ds` (`x₀⁻² = t² x₁⁻²`). Both composites are the
identity, as two derivations agreeing on the coordinates agree.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace MvPolynomial HomogeneousLocalization

noncomputable section

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : Type u} [Fintype n] {R : Type u} [CommRing R] {s : Set n}

/-- The product of two Laurent monomials is the Laurent monomial of the sum of the exponents. -/
lemma awayMonomial_mul (e e' e'' : laurentExponents s 0) (h : e''.1 = e.1 + e'.1) :
    awayMonomial R s e * awayMonomial R s e' = awayMonomial R s e'' := by
  apply HomogeneousLocalization.val_injective
  have h0 := indicator_one_nonneg s
  have ha := add_nsmul_indicator_nonneg e.2.2 (neg_le_negExponentSum e.1)
  have ha' := add_nsmul_indicator_nonneg e'.2.2 (neg_le_negExponentSum e'.1)
  have ha'' := add_nsmul_indicator_nonneg e''.2.2 (neg_le_negExponentSum e''.1)
  rw [HomogeneousLocalization.val_mul, awayMonomial, awayMonomial, awayMonomial, Away.val_mk,
    Away.val_mk, Away.val_mk, Localization.mk_mul]
  refine mk_eq_mk_of_monomialToNat (add_nonneg ha ha')
    (add_nonneg (nsmul_nonneg h0 (negExponentSum e.1)) (nsmul_nonneg h0 (negExponentSum e'.1)))
    ha'' (nsmul_nonneg h0 (negExponentSum e''.1)) (monomialToNat_mul ha ha') ?_ rfl ?_ ?_
  · simp only [Submonoid.coe_mul, monomialToNat_pow h0]
    exact monomialToNat_mul (nsmul_nonneg h0 _) (nsmul_nonneg h0 _)
  · simp only [monomialToNat_pow h0]
  · rw [h]
    abel

/-- The Laurent monomial with exponent `0` is `1`. -/
lemma awayMonomial_zero (e : laurentExponents s 0) (h : e.1 = 0) : awayMonomial R s e = 1 := by
  apply HomogeneousLocalization.val_injective
  have h0 := indicator_one_nonneg s
  rw [HomogeneousLocalization.val_one, awayMonomial, Away.val_mk, ← Localization.mk_one]
  refine mk_eq_mk_of_monomialToNat (add_nsmul_indicator_nonneg e.2.2 (neg_le_negExponentSum e.1))
    (nsmul_nonneg h0 (negExponentSum e.1)) le_rfl le_rfl rfl ?_ monomialToNat_zero.symm
    monomialToNat_zero.symm ?_
  · simp only [monomialToNat_pow h0]
  · rw [h]
    simp

/-- The `m`-th power of a Laurent monomial is the Laurent monomial of `m` times the exponent. -/
lemma awayMonomial_pow (e : laurentExponents s 0) (m : ℕ) (e' : laurentExponents s 0)
    (h : e'.1 = m • e.1) : awayMonomial R s e' = awayMonomial R s e ^ m := by
  induction m generalizing e' with
  | zero => exact (awayMonomial_zero (R := R) e' (by simpa using h)).trans (pow_zero _).symm
  | succ m ih =>
    let e₀ : laurentExponents s 0 := ⟨m • e.1, by
      simp only [Pi.smul_apply, nsmul_eq_mul, ← Finset.mul_sum, e.2.1, mul_zero], fun i hi ↦
      nsmul_nonneg (e.2.2 i hi) m⟩
    rw [pow_succ, ← ih e₀ rfl, awayMonomial_mul e₀ e e' (by rw [h, succ_nsmul])]

/-- The function `xᵉ` on `D₊(∏_{i ∈ t} Xᵢ)` restricts to the function `xᵉ` on the smaller open
`D₊(∏_{i ∈ s} Xᵢ)`, for `t ⊆ s`. -/
lemma presheaf_map_awayToSection_awayMonomial {t : Set n} (hts : t ⊆ s)
    (e : laurentExponents t 0) :
    (Proj (homogeneousSubmodule n R)).presheaf.map
        (homOfLE (basicOpen_monomialToNat_indicator_mono (R := R) hts)).op
        (Proj.awayToSection _ _ (awayMonomial R t e)) =
      Proj.awayToSection _ _
        (awayMonomial R s ⟨e.1, e.2.1, fun i hi ↦ e.2.2 i fun h ↦ hi (hts h)⟩) := by
  refine Subtype.ext (funext fun x ↦ HomogeneousLocalization.val_injective _ ?_)
  change ((Proj.awayToSection _ _ (awayMonomial R t e)).1 ⟨x.1, _⟩).val = _
  rw [val_awayToSection_awayMonomial_apply, val_awayToSection_awayMonomial_apply]
  have h0 := indicator_one_nonneg s
  have h0' := indicator_one_nonneg t
  refine mk_monomialToNat_eq_mk (add_nsmul_indicator_nonneg e.2.2 (neg_le_negExponentSum e.1))
    (nsmul_nonneg h0' _) (add_nsmul_indicator_nonneg (fun i hi ↦ e.2.2 i fun h ↦ hi (hts h))
      (neg_le_negExponentSum e.1)) (nsmul_nonneg h0 _) ?_ _ _
  abel

end AlgebraicGeometry.Proj

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M N : X.Modules} {ι : Type*} {U : ι → X.Opens} {e : ∀ i, Γ(M, U i)}

lemma isGlueValue_app (φ : M ⟶ N) {V : X.Opens} (m : Γ(M, V)) :
    IsGlueValue e (fun i ↦ φ.app (U i) (e i)) m (φ.app V m) := by
  intro i W hW hWi a ha
  rw [← Hom.app_presheaf_map, ← ha, Hom.app_smul, Hom.app_presheaf_map]

/-- Two morphisms out of a module with free generators `e i` over an open cover agree if they
agree on the generators. -/
lemma hom_ext_of_isFreeGenerator (hU : ⨆ i, U i = ⊤) (he : ∀ i, IsFreeGenerator (e i))
    {φ ψ : M ⟶ N} (h : ∀ i, φ.app (U i) (e i) = ψ.app (U i) (e i)) : φ = ψ := by
  refine hom_ext _ _ fun V ↦ ?_
  ext m
  have hψ := isGlueValue_app (e := e) ψ m
  simp only [← h] at hψ
  exact (isGlueValue_app φ m).unique hU he hψ

lemma glueHom_app_self {f : ∀ i, Γ(N, U i)} (hU : ⨆ i, U i = ⊤) (he : ∀ i, IsFreeGenerator (e i))
    (hc : ∀ i j (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) (a b : Γ(X, W)),
      a • M.presheaf.map (homOfLE hi).op (e i) = b • M.presheaf.map (homOfLE hj).op (e j) →
        a • N.presheaf.map (homOfLE hi).op (f i) = b • N.presheaf.map (homOfLE hj).op (f j))
    (i : ι) : (glueHom hU he hc).app (U i) (e i) = f i := by
  have := isGlueValue_glueHom_app hU he hc (e i) i (U i) le_rfl le_rfl 1
    (by rw [one_smul])
  rwa [presheaf_map_id_apply, presheaf_map_id_apply, one_smul] at this

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.ProjectiveLine

open ProjectiveSpace Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

/-- The open `⋂_{i ∈ s} D₊(xᵢ)` of `ℙ¹_k`. -/
abbrev chart (s : Set (ULift.{u} (Fin 2))) : (ProjectiveLine (Spec (.of k))).Opens :=
  toProjInt _ (Spec (.of k)) ⁻¹ᵁ basicOpenInt _ s

lemma chart_mono {s t : Set (ULift.{u} (Fin 2))} (hts : t ⊆ s) : chart k s ≤ chart k t :=
  (toProjInt _ _).preimage_mono (Proj.basicOpen_monomialToNat_indicator_mono hts)

/-- The functions on `⋂_{i ∈ s} D₊(xᵢ)` coming from the degree-zero localization of
`ℤ[x₀, x₁]` away from `∏_{i ∈ s} xᵢ`. -/
def chartFun (s : Set (ULift.{u} (Fin 2))) :
    Away (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
      (monomialToNat (ULift.{u} ℤ) (s.indicator 1)) →+*
      Γ(ProjectiveLine (Spec (.of k)), chart k s) :=
  (Proj.awayToSection _ _ ≫ (toProjInt _ (Spec (.of k))).appLE (basicOpenInt _ s)
    (chart k s) le_rfl).hom

/-- The constant functions on an open of `ℙ¹_k`. -/
def chartConst (V : (ProjectiveLine (Spec (.of k))).Opens) :
    k →+* Γ(ProjectiveLine (Spec (.of k)), V) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).appTop ≫
    (ProjectiveLine (Spec (.of k))).presheaf.map (homOfLE le_top).op).hom

lemma presheaf_map_chartConst {V W : (ProjectiveLine (Spec (.of k))).Opens} (h : W ≤ V) (c : k) :
    (ProjectiveLine (Spec (.of k))).presheaf.map (homOfLE h).op (chartConst k V c) =
      chartConst k W c := by
  simp only [chartConst, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [Scheme.presheaf_map_map_apply]
  rfl

lemma presheaf_map_chartFun_awayMonomial {s t : Set (ULift.{u} (Fin 2))} (hts : t ⊆ s)
    (e : laurentExponents t 0) :
    (ProjectiveLine (Spec (.of k))).presheaf.map (homOfLE (chart_mono k hts)).op
        (chartFun k t (awayMonomial _ t e)) =
      chartFun k s (awayMonomial _ s ⟨e.1, e.2.1, fun i hi ↦ e.2.2 i fun h ↦ hi (hts h)⟩) := by
  have h1 := ConcreteCategory.congr_hom (Scheme.Hom.appLE_map (toProjInt _ (Spec (.of k)))
    (U := basicOpenInt _ t) (le_rfl : chart k t ≤ _) (homOfLE (chart_mono k hts)).op)
    (Proj.awayToSection _ _ (awayMonomial _ t e))
  have h2 := ConcreteCategory.congr_hom (Scheme.Hom.map_appLE (toProjInt _ (Spec (.of k)))
    (U := basicOpenInt _ s) (V := chart k s) le_rfl
    (homOfLE (Proj.basicOpen_monomialToNat_indicator_mono (R := ULift.{u} ℤ) hts)).op)
    (Proj.awayToSection _ _ (awayMonomial _ t e))
  rw [CommRingCat.comp_apply] at h1 h2
  erw [Proj.presheaf_map_awayToSection_awayMonomial hts] at h2
  exact h1.trans h2.symm

section Coordinates

variable {i j : ULift.{u} (Fin 2)} (hij : i ≠ j)

include hij in
lemma eq_or_eq_of_ne (l : ULift.{u} (Fin 2)) : l = i ∨ l = j := by
  obtain ⟨⟨i, hi⟩⟩ := i
  obtain ⟨⟨j, hj⟩⟩ := j
  obtain ⟨⟨l, hl⟩⟩ := l
  simp only [ne_eq, ULift.up.injEq, Fin.mk.injEq] at hij ⊢
  omega

include hij in
lemma sum_eq_add_of_ne {M : Type*} [AddCommMonoid M] (f : ULift.{u} (Fin 2) → M) :
    ∑ l, f l = f i + f j :=
  Fintype.sum_eq_add i j hij fun l hl ↦ ((eq_or_eq_of_ne hij l).elim hl.1 hl.2).elim

/-- The exponent vector of the affine coordinate `xⱼ / xᵢ` on `D₊(xᵢ)`. -/
def coordExp : laurentExponents ({i} : Set (ULift.{u} (Fin 2))) 0 :=
  ⟨Pi.single j 1 - Pi.single i 1, by simp [Finset.sum_sub_distrib], fun l hl ↦ by
    rw [Set.mem_singleton_iff] at hl
    simp only [Pi.sub_apply, Pi.single_apply, ite_eq_right hl, sub_zero]
    split_ifs <;> norm_num⟩

/-- The affine coordinate `xⱼ / xᵢ` on `D₊(xᵢ)`. -/
def coord : Γ(ProjectiveLine (Spec (.of k)), chart k {i}) :=
  chartFun k {i} (awayMonomial _ {i} (coordExp (i := i) (j := j)))

/-- Every Laurent monomial regular on `D₊(xᵢ)` is a power of `xⱼ / xᵢ`. -/
def coordExpEquiv : ℕ ≃ laurentExponents ({i} : Set (ULift.{u} (Fin 2))) 0 where
  toFun m := ⟨m • (coordExp (i := i) (j := j)).1, by
    simp only [Pi.smul_apply, nsmul_eq_mul, ← Finset.mul_sum, (coordExp (i := i) (j := j)).2.1,
      mul_zero],
    fun l hl ↦ nsmul_nonneg ((coordExp (i := i) (j := j)).2.2 l hl) m⟩
  invFun e := (e.1 j).toNat
  left_inv m := by simp [coordExp, hij.symm]
  right_inv e := by
    have hj := e.2.2 j (by simpa using hij.symm)
    have hs := e.2.1
    rw [sum_eq_add_of_ne hij] at hs
    refine Subtype.ext (funext fun l ↦ ?_)
    rcases eq_or_eq_of_ne hij l with rfl | rfl
    · simp [coordExp, hij]
      omega
    · simp [coordExp, hij.symm]
      omega

lemma chartFun_coordExpEquiv (m : ℕ) :
    chartFun k {i} (awayMonomial _ _ (coordExpEquiv hij m)) = coord k (i := i) (j := j) ^ m := by
  rw [coord, ← map_pow, ← Proj.awayMonomial_pow _ m (coordExpEquiv hij m) rfl]

/-- The ring homomorphism `k[X] → Γ(D₊(xᵢ))`, `X ↦ xⱼ / xᵢ`. -/
def polyToChart : Polynomial k →+* Γ(ProjectiveLine (Spec (.of k)), chart k {i}) :=
  Polynomial.eval₂RingHom (chartConst k (chart k {i})) (coord k (i := i) (j := j))

include hij in
/-- **The functions on the standard chart `D₊(xᵢ)` of `ℙ¹_k` are the polynomials in
`xⱼ / xᵢ`.** -/
lemma bijective_polyToChart : Function.Bijective (polyToChart k (i := i) (j := j)) := by
  have hB := bijective_sum_awayMonomial (n := ULift.{u} (Fin 2)) k (Set.singleton_nonempty i)
  let g : Polynomial k ≃ (laurentExponents ({i} : Set (ULift.{u} (Fin 2))) 0 →₀ k) :=
    (Polynomial.toFinsuppIso k).toEquiv.trans
      ((AddMonoidAlgebra.coeffEquiv (R := k) (M := ℕ)).trans
        (Finsupp.equivCongrLeft (coordExpEquiv hij)))
  convert hB.comp g.bijective using 1
  funext p
  rw [Function.comp_apply]
  simp only [g, Equiv.trans_apply, RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv,
    Polynomial.toFinsuppIso_apply, AddMonoidAlgebra.coeffEquiv_apply,
    Finsupp.equivCongrLeft_apply, Finsupp.sum_equivMapDomain]
  rw [polyToChart, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_sum, Polynomial.sum_def,
    Finsupp.sum, Polynomial.support_toFinsupp]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [Polynomial.toFinsupp_apply, ← chartFun_coordExpEquiv k hij]
  rfl

/-- The ring isomorphism `k[X] ≅ Γ(D₊(xᵢ))`, `X ↦ xⱼ / xᵢ`. -/
def polyEquivChart : Polynomial k ≃+* Γ(ProjectiveLine (Spec (.of k)), chart k {i}) :=
  RingEquiv.ofBijective _ (bijective_polyToChart k hij)

lemma polyEquivChart_apply (p : Polynomial k) :
    polyEquivChart k hij p = polyToChart k (i := i) (j := j) p :=
  rfl

lemma polyEquivChart_symm_coord :
    (polyEquivChart k hij).symm (coord k (i := i) (j := j)) = Polynomial.X :=
  (polyEquivChart k hij).symm_apply_eq.2 (by simp [polyEquivChart_apply, polyToChart])

lemma polyEquivChart_symm_chartConst (c : k) :
    (polyEquivChart k hij).symm (chartConst k _ c) = Polynomial.C c :=
  (polyEquivChart k hij).symm_apply_eq.2 (by simp [polyEquivChart_apply, polyToChart])

end Coordinates

section Charts

lemma isAffineOpen_chart {s : Set (ULift.{u} (Fin 2))} (hs : s.Nonempty) :
    IsAffineOpen (chart k s) := by
  have : IsAffineHom (toProjInt (ULift.{u} (Fin 2)) (Spec (.of k))) :=
    MorphismProperty.pullback_snd (P := @IsAffineHom) _ _ inferInstance
  exact (Proj.isAffineOpen_basicOpen _ _ (monomialToNat_indicator_mem (ULift.{u} ℤ) s)
    (indicatorDegree_pos hs)).preimage _

/-- The generator `xᵢ⁻²` of `𝒪(-2)` over `D₊(xᵢ)`. -/
def twistGen (i : ULift.{u} (Fin 2)) :
    Γ(twist (ULift.{u} (Fin 2)) (Spec (.of k)) (-2), chart k {i}) :=
  twistMonomialSection (Spec (.of k)) {i}
    (Proj.singleExponent (s := {i}) (m := -2) (Set.mem_singleton i))

lemma isFreeGenerator_twistGen (i : ULift.{u} (Fin 2)) : IsFreeGenerator (twistGen k i) :=
  isFreeGenerator_twistMonomialSection_singleExponent _

variable {i j : ULift.{u} (Fin 2)} (hij : i ≠ j) (σ : ℤ)

/-- The derivation `σ d / d(xⱼ / xᵢ)` of `Γ(D₊(xᵢ)) = k[xⱼ / xᵢ]`, with values in `𝒪(-2)`
through its generator `xᵢ⁻²`. -/
def chartDerivation :
    Γ(ProjectiveLine (Spec (.of k)), chart k {i}) →+
      Γ(twist (ULift.{u} (Fin 2)) (Spec (.of k)) (-2), chart k {i}) where
  toFun f := σ • ((polyEquivChart k hij
    (Polynomial.derivative ((polyEquivChart k hij).symm f))) • twistGen k i)
  map_zero' := by simp
  map_add' f g := by simp [add_smul]

lemma chartDerivation_apply (f : Γ(ProjectiveLine (Spec (.of k)), chart k {i})) :
    chartDerivation k hij σ f = σ • ((polyEquivChart k hij
      (Polynomial.derivative ((polyEquivChart k hij).symm f))) • twistGen k i) :=
  rfl

lemma chartDerivation_mul (f g : Γ(ProjectiveLine (Spec (.of k)), chart k {i})) :
    chartDerivation k hij σ (f * g) =
      f • chartDerivation k hij σ g + g • chartDerivation k hij σ f := by
  simp only [chartDerivation_apply, map_mul, Polynomial.derivative_mul, map_add,
    RingEquiv.apply_symm_apply, add_smul, mul_smul, smul_add]
  module

lemma chartDerivation_coord :
    chartDerivation k hij σ (coord k (i := i) (j := j)) = σ • twistGen k i := by
  simp [chartDerivation_apply, polyEquivChart_symm_coord]

lemma chartDerivation_chartConst (c : k) : chartDerivation k hij σ (chartConst k _ c) = 0 := by
  simp [chartDerivation_apply, polyEquivChart_symm_chartConst]

/-- The local derivation over `D₊(xᵢ)` extending `chartDerivation`. -/
def chartLocalDerivation : LocalDerivation (twist (ULift.{u} (Fin 2)) (Spec (.of k)) (-2))
    (chart k {i}) :=
  LocalDerivation.ofIsAffineOpen (isAffineOpen_chart k (Set.singleton_nonempty i))
    (chartDerivation k hij σ) (chartDerivation_mul k hij σ)

end Charts

section Overlap

/-- The intersection `D₊(x₀) ∩ D₊(x₁)`. -/
abbrev overlap : (ProjectiveLine (Spec (.of k))).Opens := chart k Set.univ

lemma overlap_le_chart (i : ULift.{u} (Fin 2)) : overlap k ≤ chart k {i} :=
  chart_mono k (Set.subset_univ _)

lemma mem_chart_iff {s : Set (ULift.{u} (Fin 2))} {x : ProjectiveLine (Spec (.of k))} :
    x ∈ chart k s ↔ ∀ i ∈ s, x ∈ standardOpen _ (Spec (.of k)) i :=
  Proj.mem_basicOpen_monomialToNat_indicator

lemma chart_singleton (i : ULift.{u} (Fin 2)) : chart k {i} = standardOpen _ (Spec (.of k)) i :=
  Opens.ext (Set.ext fun _ ↦ (mem_chart_iff k).trans (by simp))

lemma le_overlap {i j : ULift.{u} (Fin 2)} (hij : i ≠ j) {W : (ProjectiveLine (Spec (.of k))).Opens}
    (hi : W ≤ chart k {i}) (hj : W ≤ chart k {j}) : W ≤ overlap k := fun _ hx ↦
  (mem_chart_iff k).2 fun l _ ↦ (eq_or_eq_of_ne hij l).elim
    (fun h ↦ h ▸ chart_singleton k i ▸ hi hx) fun h ↦ h ▸ chart_singleton k j ▸ hj hx

lemma iSup_chart : ⨆ i, chart k {i} = ⊤ := by
  simp only [chart_singleton, iSup_standardOpen]

variable {i j : ULift.{u} (Fin 2)}

/-- The Laurent monomial `xⱼ / xᵢ` on the overlap. -/
def overlapCoordExp (i j : ULift.{u} (Fin 2)) :
    laurentExponents (Set.univ : Set (ULift.{u} (Fin 2))) 0 :=
  ⟨(coordExp (i := i) (j := j)).1, (coordExp (i := i) (j := j)).2.1, fun _ hl ↦ (hl trivial).elim⟩

lemma coord_restrict :
    (ProjectiveLine (Spec (.of k))).presheaf.map (homOfLE (overlap_le_chart k i)).op
        (coord k (i := i) (j := j)) =
      chartFun k Set.univ (awayMonomial _ _ (overlapCoordExp i j)) :=
  presheaf_map_chartFun_awayMonomial k (Set.subset_univ _) _

lemma coord_mul_coord :
    (ProjectiveLine (Spec (.of k))).presheaf.map (homOfLE (overlap_le_chart k i)).op
        (coord k (i := i) (j := j)) *
      (ProjectiveLine (Spec (.of k))).presheaf.map (homOfLE (overlap_le_chart k j)).op
        (coord k (i := j) (j := i)) = 1 := by
  rw [coord_restrict, coord_restrict, ← map_mul,
    Proj.awayMonomial_mul _ _ ⟨0, by simp, fun _ _ ↦ le_rfl⟩ (by
      funext l
      simp only [overlapCoordExp, coordExp, Pi.zero_apply, Pi.add_apply, Pi.sub_apply]
      ring),
    Proj.awayMonomial_zero _ rfl, map_one]

lemma twistGen_restrict :
    (twist (ULift.{u} (Fin 2)) (Spec (.of k)) (-2)).presheaf.map
        (homOfLE (overlap_le_chart k i)).op (twistGen k i) =
      ((ProjectiveLine (Spec (.of k))).presheaf.map (homOfLE (overlap_le_chart k i)).op
        (coord k (i := i) (j := j))) ^ 2 •
      (twist (ULift.{u} (Fin 2)) (Spec (.of k)) (-2)).presheaf.map
        (homOfLE (overlap_le_chart k j)).op (twistGen k j) := by
  have hi := twist_presheaf_map_twistMonomialSection (S := Spec (.of k)) (m := -2)
    (Set.subset_univ {i}) (Proj.singleExponent (s := {i}) (m := -2) (Set.mem_singleton i))
  have hj := twist_presheaf_map_twistMonomialSection (S := Spec (.of k)) (m := -2)
    (Set.subset_univ {j}) (Proj.singleExponent (s := {j}) (m := -2) (Set.mem_singleton j))
  rw [twistGen, twistGen, hi, hj, twistMonomialSection_eq_smul (Set.mem_univ j), coord_restrict,
    ← map_pow, ← Proj.awayMonomial_pow _ 2 _ ?_]
  · rfl
  · funext l
    simp only [Proj.shiftExponent, Proj.singleExponent, overlapCoordExp, coordExp, Pi.sub_apply,
      Pi.smul_apply, Pi.single_apply]
    split_ifs <;> simp_all

lemma closure_overlap (hij : i ≠ j) :
    Subring.closure (Set.range (chartConst k (overlap k)) ∪
      {(ProjectiveLine (Spec (.of k))).presheaf.map (homOfLE (overlap_le_chart k i)).op
        (coord k (i := i) (j := j)),
       (ProjectiveLine (Spec (.of k))).presheaf.map (homOfLE (overlap_le_chart k j)).op
        (coord k (i := j) (j := i))}) = ⊤ := by
  set T := Subring.closure (Set.range (chartConst k (overlap k)) ∪
      {(ProjectiveLine (Spec (.of k))).presheaf.map (homOfLE (overlap_le_chart k i)).op
        (coord k (i := i) (j := j)),
       (ProjectiveLine (Spec (.of k))).presheaf.map (homOfLE (overlap_le_chart k j)).op
        (coord k (i := j) (j := i))})
  have hmono (e : laurentExponents (Set.univ : Set (ULift.{u} (Fin 2))) 0) :
      chartFun k Set.univ (awayMonomial _ _ e) ∈ T := by
    have hs := e.2.1
    rw [sum_eq_add_of_ne hij] at hs
    rcases le_total 0 (e.1 j) with h | h
    · rw [Proj.awayMonomial_pow (overlapCoordExp i j) (e.1 j).toNat e ?_, map_pow,
        ← coord_restrict]
      · exact T.pow_mem (Subring.subset_closure (by simp)) _
      · funext l
        rcases eq_or_eq_of_ne hij l with rfl | rfl
        · simp [overlapCoordExp, coordExp, hij]
          omega
        · simp [overlapCoordExp, coordExp, hij.symm]
          omega
    · rw [Proj.awayMonomial_pow (overlapCoordExp j i) (e.1 i).toNat e ?_, map_pow,
        ← coord_restrict]
      · exact T.pow_mem (Subring.subset_closure (by simp)) _
      · funext l
        rcases eq_or_eq_of_ne hij l with rfl | rfl
        · simp [overlapCoordExp, coordExp, hij]
          omega
        · simp [overlapCoordExp, coordExp, hij.symm]
          omega
  refine eq_top_iff.2 fun f _ ↦ ?_
  obtain ⟨c, rfl⟩ := (bijective_sum_awayMonomial (n := ULift.{u} (Fin 2)) k
    (Set.univ_nonempty (α := ULift.{u} (Fin 2)))).2 f
  refine Subring.sum_mem _ fun e _ ↦ Subring.mul_mem _
    (Subring.subset_closure (Or.inl ⟨c e, rfl⟩)) (hmono e)

end Overlap

section Glue

variable {i j : ULift.{u} (Fin 2)}

omit [Field k] in
lemma neg_sq_smul_neg_zsmul_sq_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {x y : R} (h : x * y = 1) (τ : ℤ) (g : M) : -(y ^ 2) • -τ • x ^ 2 • g = τ • g := by
  rw [neg_smul, neg_smul, smul_neg, neg_neg, smul_comm (y ^ 2) τ, smul_smul, ← mul_pow,
    mul_comm y x, h, one_pow, one_smul]

lemma chartLocalDerivation_app_self (hij : i ≠ j) (σ : ℤ)
    (f : Γ(ProjectiveLine (Spec (.of k)), chart k {i})) :
    (chartLocalDerivation k hij σ).app (chart k {i}) le_rfl f = chartDerivation k hij σ f :=
  LocalDerivation.ofIsAffineOpen_app_self _ _ _ f

lemma chartLocalDerivation_app_restrict (hij : i ≠ j) (σ : ℤ)
    {W : (ProjectiveLine (Spec (.of k))).Opens}
    (hW : W ≤ chart k {i}) (f : Γ(ProjectiveLine (Spec (.of k)), chart k {i})) :
    (chartLocalDerivation k hij σ).app W hW
        ((ProjectiveLine (Spec (.of k))).presheaf.map (homOfLE hW).op f) =
      (twist (ULift.{u} (Fin 2)) (Spec (.of k)) (-2)).presheaf.map (homOfLE hW).op
        (chartDerivation k hij σ f) := by
  rw [← chartLocalDerivation_app_self k hij σ f]
  exact (chartLocalDerivation k hij σ).naturality _ _ le_rfl hW f

/-- **The chain rule on `D₊(x₀) ∩ D₊(x₁)`.** The derivations `σ d/d(xⱼ/xᵢ)` on `D₊(xᵢ)` and
`τ d/d(xᵢ/xⱼ)` on `D₊(xⱼ)`, with values in `𝒪(-2)` through `xᵢ⁻²` and `xⱼ⁻²`, agree on the
overlap if `σ = -τ`. -/
lemma chartLocalDerivation_agree (hij : i ≠ j) (σ τ : ℤ) (hστ : σ = -τ)
    (W : (ProjectiveLine (Spec (.of k))).Opens) (hi : W ≤ chart k {i}) (hj : W ≤ chart k {j})
    (a : Γ(ProjectiveLine (Spec (.of k)), W)) :
    (chartLocalDerivation k hij σ).app W hi a = (chartLocalDerivation k hij.symm τ).app W hj a := by
  set D₁ := (chartLocalDerivation k hij σ).restrict (overlap_le_chart k i)
  set D₂ := (chartLocalDerivation k hij.symm τ).restrict (overlap_le_chart k j)
  have hD₁ : ∀ f, D₁.app (overlap k) le_rfl
      ((ProjectiveLine (Spec (.of k))).presheaf.map (homOfLE (overlap_le_chart k i)).op f) =
      (twist (ULift.{u} (Fin 2)) (Spec (.of k)) (-2)).presheaf.map
        (homOfLE (overlap_le_chart k i)).op (chartDerivation k hij σ f) :=
    chartLocalDerivation_app_restrict k hij σ _
  have hD₂ : ∀ f, D₂.app (overlap k) le_rfl
      ((ProjectiveLine (Spec (.of k))).presheaf.map (homOfLE (overlap_le_chart k j)).op f) =
      (twist (ULift.{u} (Fin 2)) (Spec (.of k)) (-2)).presheaf.map
        (homOfLE (overlap_le_chart k j)).op (chartDerivation k hij.symm τ f) :=
    chartLocalDerivation_app_restrict k hij.symm τ _
  have hc := coord_mul_coord k (i := i) (j := j)
  have hc' := coord_mul_coord k (i := j) (j := i)
  have hg := twistGen_restrict k (i := i) (j := j)
  have key : ∀ a, D₁.app (overlap k) le_rfl a = D₂.app (overlap k) le_rfl a := by
    refine LocalDerivation.app_eq_of_closure D₁ D₂ le_rfl _ (closure_overlap k hij) ?_
    rintro a (⟨c, rfl⟩ | rfl | rfl)
    · conv_lhs => rw [← presheaf_map_chartConst k (overlap_le_chart k i) c]
      conv_rhs => rw [← presheaf_map_chartConst k (overlap_le_chart k j) c]
      rw [hD₁, hD₂, chartDerivation_chartConst, chartDerivation_chartConst, map_zero, map_zero]
    · rw [hD₁, D₂.app_eq_neg_sq_smul_of_mul_eq_one le_rfl hc, hD₂, chartDerivation_coord,
        chartDerivation_coord, map_zsmul, map_zsmul, hg, hστ]
      module
    · rw [hD₂, D₁.app_eq_neg_sq_smul_of_mul_eq_one le_rfl hc', hD₁, chartDerivation_coord,
        chartDerivation_coord, map_zsmul, map_zsmul, hg, hστ]
      exact neg_sq_smul_neg_zsmul_sq_smul hc _ _
  exact LocalDerivation.ext_of_isAffineOpen (isAffineOpen_chart k (Set.univ_nonempty)) D₁ D₂ key W
    (le_overlap k hij hi hj) a

/-- The other homogeneous coordinate. -/
def other (i : ULift.{u} (Fin 2)) : ULift.{u} (Fin 2) :=
  ⟨i.down.rev⟩

lemma ne_other (i : ULift.{u} (Fin 2)) : i ≠ other i := by
  obtain ⟨⟨i, hi⟩⟩ := i
  simp only [other, ne_eq, ULift.up.injEq, Fin.ext_iff, Fin.val_rev]
  omega

lemma other_eq (hij : i ≠ j) : other i = j :=
  ((eq_or_eq_of_ne (ne_other i) j).resolve_left hij.symm).symm

/-- The sign `1` on `D₊(x₀)` and `-1` on `D₊(x₁)`. -/
def sign (i : ULift.{u} (Fin 2)) : ℤ :=
  if i = ⟨0⟩ then 1 else -1

lemma sign_eq_neg (hij : i ≠ j) : sign i = -sign j := by
  obtain ⟨⟨i, hi⟩⟩ := i
  obtain ⟨⟨j, hj⟩⟩ := j
  simp only [ne_eq, ULift.up.injEq, Fin.mk.injEq] at hij
  simp only [sign, ULift.up.injEq, Fin.ext_iff]
  split_ifs <;> omega

/-- The derivation `sign i • d / d(x_{other i} / xᵢ)` over `D₊(xᵢ)`. -/
def localD (i : ULift.{u} (Fin 2)) :
    LocalDerivation (twist (ULift.{u} (Fin 2)) (Spec (.of k)) (-2)) (chart k {i}) :=
  chartLocalDerivation k (ne_other i) (sign i)

lemma chartLocalDerivation_congr {j' : ULift.{u} (Fin 2)} (hij : i ≠ j) (hij' : i ≠ j')
    (h : j = j') (σ : ℤ) : chartLocalDerivation k hij σ = chartLocalDerivation k hij' σ := by
  subst h
  rfl

lemma localD_agree (i j : ULift.{u} (Fin 2)) (W : (ProjectiveLine (Spec (.of k))).Opens)
    (hi : W ≤ chart k {i}) (hj : W ≤ chart k {j}) (a : Γ(ProjectiveLine (Spec (.of k)), W)) :
    (localD k i).app W hi a = (localD k j).app W hj a := by
  by_cases hij : i = j
  · subst hij
    rfl
  · rw [localD, localD, chartLocalDerivation_congr k (ne_other i) hij (other_eq hij),
      chartLocalDerivation_congr k (ne_other j) (Ne.symm hij) (other_eq (Ne.symm hij))]
    exact chartLocalDerivation_agree k hij _ _ (sign_eq_neg hij) W hi hj a

/-- **The derivation `𝒪 → 𝒪(-2)`** on `ℙ¹_k`, given by `d/dt` on `D₊(x₀)` and `-d/ds` on
`D₊(x₁)`. -/
def twistDerivation : LocalDerivation (twist (ULift.{u} (Fin 2)) (Spec (.of k)) (-2)) ⊤ :=
  LocalDerivation.glueCover (fun i ↦ chart k {i}) (iSup_chart k) (localD k) (localD_agree k)

lemma twistDerivation_app (i : ULift.{u} (Fin 2)) (W : (ProjectiveLine (Spec (.of k))).Opens)
    (hW : W ≤ chart k {i}) (a : Γ(ProjectiveLine (Spec (.of k)), W)) :
    (twistDerivation k).app W le_top a = (localD k i).app W hW a :=
  LocalDerivation.glueCover_app _ _ _ _ i W hW a

lemma appLE_top_eq_chartConst (W : (ProjectiveLine (Spec (.of k))).Opens)
    (e : W ≤ (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) ⁻¹ᵁ ⊤) (c : Γ(Spec (.of k), ⊤)) :
    (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).appLE ⊤ W e c =
      chartConst k W ((Scheme.ΓSpecIso (.of k)).hom c) := by
  simp only [chartConst, Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.coe_comp,
    Function.comp_apply]
  rw [← CommRingCat.comp_apply (Scheme.ΓSpecIso _).hom, Iso.hom_inv_id, CommRingCat.id_apply]
  rfl

lemma twistDerivation_appLE (U : (Spec (.of k)).Opens) (V : (ProjectiveLine (Spec (.of k))).Opens)
    (e : V ≤ (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) ⁻¹ᵁ U) (c : Γ(Spec (.of k), U)) :
    (twistDerivation k).app V le_top
      ((ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).appLE U V e c) = 0 := by
  by_cases hV : V = ⊥
  · subst hV
    have := subsingleton_sections_bot (twist (ULift.{u} (Fin 2)) (Spec (.of k)) (-2))
    exact Subsingleton.elim _ _
  obtain ⟨x, hx⟩ := (Opens.ne_bot_iff_nonempty V).1 hV
  obtain rfl : U = ⊤ := eq_top_iff.2 fun y _ ↦ Subsingleton.elim
    ((ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).base x) y ▸ e hx
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨_, (twist (ULift.{u} (Fin 2)) (Spec (.of k)) (-2)).isSheaf⟩
    (fun i ↦ V ⊓ chart k {i}) V (fun _ ↦ homOfLE inf_le_left) (fun y hy ↦ ?_) _ 0 fun i ↦ ?_
  · obtain ⟨i, hi⟩ := Opens.mem_iSup.mp ((iSup_chart k).ge (Set.mem_univ y))
    exact Opens.mem_iSup.mpr ⟨i, hy, hi⟩
  · rw [map_zero, ← (twistDerivation k).naturality V _ le_top inf_le_left]
    have h1 : (ProjectiveLine (Spec (.of k))).presheaf.map
        (homOfLE (inf_le_left : V ⊓ chart k {i} ≤ V)).op
          ((ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).appLE ⊤ V e c) =
        (ProjectiveLine (Spec (.of k))).presheaf.map
          (homOfLE (inf_le_right : V ⊓ chart k {i} ≤ chart k {i})).op
          (chartConst k (chart k {i}) ((Scheme.ΓSpecIso (.of k)).hom c)) := by
      rw [presheaf_map_chartConst, ← appLE_top_eq_chartConst k _ (inf_le_left.trans e)]
      exact ConcreteCategory.congr_hom (Scheme.Hom.appLE_map _ e _) c
    rw [h1, twistDerivation_app k i _ inf_le_right, localD, chartLocalDerivation_app_restrict,
      chartDerivation_chartConst, map_zero]

end Glue

section Differentials

/-- The universal derivation `d : 𝒪 → Ω¹_{ℙ¹/k}`, as a local derivation. -/
def dΩ : LocalDerivation (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).relativeDifferentials ⊤ :=
  LocalDerivation.ofDerivation'
    (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).relativeDifferentialsDerivation

/-- **The morphism `Ω¹_{ℙ¹/k} ⟶ 𝒪(-2)`** induced by the derivation `twistDerivation`. -/
def toTwist : (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).relativeDifferentials ⟶
    twist (ULift.{u} (Fin 2)) (Spec (.of k)) (-2) :=
  ((ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).relativeDifferentialsHomEquiv _).symm
    (LocalDerivation.toDerivation' _ (twistDerivation k) (twistDerivation_appLE k))

lemma toTwist_app_dΩ (V : (ProjectiveLine (Spec (.of k))).Opens)
    (a : Γ(ProjectiveLine (Spec (.of k)), V)) :
    (toTwist k).app V ((dΩ k).app V le_top a) = (twistDerivation k).app V le_top a := by
  have := ((ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).relativeDifferentialsHomEquiv
    _).apply_symm_apply (LocalDerivation.toDerivation' _ (twistDerivation k)
      (twistDerivation_appLE k))
  exact congrArg (fun d ↦ d.d (X := Opposite.op V) a) this

/-- The local generator `± d(x_{other i} / xᵢ)` of `Ω¹_{ℙ¹/k}` over `D₊(xᵢ)`. -/
def omegaGen (i : ULift.{u} (Fin 2)) :
    Γ((ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).relativeDifferentials, chart k {i}) :=
  sign i • (dΩ k).app _ le_top (coord k (i := i) (j := other i))

lemma omegaGen_compat (i j : ULift.{u} (Fin 2)) (W : (ProjectiveLine (Spec (.of k))).Opens)
    (hi : W ≤ chart k {i}) (hj : W ≤ chart k {j}) (a b : Γ(ProjectiveLine (Spec (.of k)), W))
    (h : a • (twist (ULift.{u} (Fin 2)) (Spec (.of k)) (-2)).presheaf.map (homOfLE hi).op
        (twistGen k i) =
      b • (twist (ULift.{u} (Fin 2)) (Spec (.of k)) (-2)).presheaf.map (homOfLE hj).op
        (twistGen k j)) :
    a • (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).relativeDifferentials.presheaf.map
        (homOfLE hi).op (omegaGen k i) =
      b • (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).relativeDifferentials.presheaf.map
        (homOfLE hj).op (omegaGen k j) := by
  by_cases hij : i = j
  · subst hij
    rw [((isFreeGenerator_twistGen k i).map hi).smul_left_injective h]
  have hW := le_overlap k hij hi hj
  set c := (ProjectiveLine (Spec (.of k))).presheaf.map (homOfLE hi).op (coord k (i := i) (j := j))
  set c' := (ProjectiveLine (Spec (.of k))).presheaf.map (homOfLE hj).op
    (coord k (i := j) (j := i))
  have hres {l : ULift.{u} (Fin 2)} (hl : W ≤ chart k {l})
      (x : Γ(ProjectiveLine (Spec (.of k)), chart k {l})) :
      (ProjectiveLine (Spec (.of k))).presheaf.map (homOfLE hW).op
        ((ProjectiveLine (Spec (.of k))).presheaf.map (homOfLE (overlap_le_chart k l)).op x) =
      (ProjectiveLine (Spec (.of k))).presheaf.map (homOfLE hl).op x := by
    rw [Scheme.presheaf_map_map_apply]
    rfl
  have hcc : c * c' = 1 := by
    have := congrArg ((ProjectiveLine (Spec (.of k))).presheaf.map (homOfLE hW).op)
      (coord_mul_coord k (i := i) (j := j))
    rwa [map_mul, map_one, hres hi, hres hj] at this
  have hg : (twist (ULift.{u} (Fin 2)) (Spec (.of k)) (-2)).presheaf.map (homOfLE hi).op
      (twistGen k i) = c ^ 2 • (twist (ULift.{u} (Fin 2)) (Spec (.of k)) (-2)).presheaf.map
        (homOfLE hj).op (twistGen k j) := by
    have := congrArg ((twist (ULift.{u} (Fin 2)) (Spec (.of k)) (-2)).presheaf.map
      (homOfLE hW).op) (twistGen_restrict k (i := i) (j := j))
    rwa [map_smul, map_pow, hres hi, presheaf_map_homOfLE_map_homOfLE,
      presheaf_map_homOfLE_map_homOfLE] at this
  rw [hg, smul_smul] at h
  have hb : b = a * c ^ 2 := (((isFreeGenerator_twistGen k j).map hj).smul_left_injective h).symm
  have hd {l : ULift.{u} (Fin 2)} (hl : W ≤ chart k {l})
      (x : Γ(ProjectiveLine (Spec (.of k)), chart k {l})) :
      (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).relativeDifferentials.presheaf.map
        (homOfLE hl).op ((dΩ k).app _ le_top x) =
      (dΩ k).app W le_top ((ProjectiveLine (Spec (.of k))).presheaf.map (homOfLE hl).op x) :=
    ((dΩ k).naturality _ _ le_top hl x).symm
  rw [omegaGen, omegaGen, other_eq hij, other_eq (Ne.symm hij), map_zsmul, map_zsmul, hd hi,
    hd hj, (dΩ k).app_eq_neg_sq_smul_of_mul_eq_one le_top hcc, sign_eq_neg hij, hb]
  module

/-- **The morphism `𝒪(-2) ⟶ Ω¹_{ℙ¹/k}`** sending the generator `xᵢ⁻²` over `D₊(xᵢ)` to
`± d(x_{other i} / xᵢ)`. -/
def fromTwist : twist (ULift.{u} (Fin 2)) (Spec (.of k)) (-2) ⟶
    (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).relativeDifferentials :=
  glueHom (iSup_chart k) (isFreeGenerator_twistGen k) (omegaGen_compat k)

lemma fromTwist_twistGen (i : ULift.{u} (Fin 2)) :
    (fromTwist k).app (chart k {i}) (twistGen k i) = omegaGen k i :=
  glueHom_app_self _ _ _ i

lemma sign_mul_self (i : ULift.{u} (Fin 2)) : sign i * sign i = 1 := by
  unfold sign
  split_ifs <;> norm_num

lemma fromTwist_comp_toTwist : fromTwist k ≫ toTwist k = 𝟙 _ := by
  refine hom_ext_of_isFreeGenerator (iSup_chart k) (isFreeGenerator_twistGen k) fun i ↦ ?_
  change (toTwist k).app _ ((fromTwist k).app _ (twistGen k i)) = twistGen k i
  rw [fromTwist_twistGen, omegaGen, map_zsmul, toTwist_app_dΩ, twistDerivation_app k i _ le_rfl,
    localD, chartLocalDerivation_app_self, chartDerivation_coord, smul_smul, sign_mul_self,
    one_smul]

lemma dΩ_chartConst (W : (ProjectiveLine (Spec (.of k))).Opens) (c : k) :
    (dΩ k).app W le_top (chartConst k W c) = 0 := by
  have e : W ≤ (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) ⁻¹ᵁ ⊤ := le_top
  have h := appLE_top_eq_chartConst k W e ((Scheme.ΓSpecIso (.of k)).inv c)
  have hc : (Scheme.ΓSpecIso (.of k)).hom ((Scheme.ΓSpecIso (.of k)).inv c) = c := by simp
  rw [hc] at h
  rw [← h, Scheme.Hom.appLE_eq_pullbackPresheafToPresheaf_app, CommRingCat.comp_apply,
    CommRingCat.comp_apply]
  exact (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).relativeDifferentialsDerivation.d_app _

lemma closure_chart {i j : ULift.{u} (Fin 2)} (hij : i ≠ j) :
    Subring.closure (Set.range (chartConst k (chart k {i})) ∪ {coord k (i := i) (j := j)}) = ⊤ := by
  refine eq_top_iff.2 ?_
  rintro f -
  obtain ⟨p, rfl⟩ := (bijective_polyToChart k hij).2 f
  induction p using Polynomial.induction_on with
  | C a => exact Subring.subset_closure (Or.inl ⟨a, by simp [polyToChart]⟩)
  | add p q hp hq => rw [map_add]; exact Subring.add_mem _ hp hq
  | monomial n a h =>
    rw [pow_succ, ← mul_assoc, map_mul]
    exact Subring.mul_mem _ h (Subring.subset_closure (Or.inr (by simp [polyToChart])))

lemma fromTwist_twistDerivation (W : (ProjectiveLine (Spec (.of k))).Opens)
    (a : Γ(ProjectiveLine (Spec (.of k)), W)) :
    (fromTwist k).app W ((twistDerivation k).app W le_top a) = (dΩ k).app W le_top a := by
  refine LocalDerivation.ext_of_cover (fun i ↦ chart k {i}) (iSup_chart k)
    ((twistDerivation k).postcomp (fromTwist k)) (dΩ k) (fun i W hW a ↦ ?_) W a
  refine LocalDerivation.ext_of_isAffineOpen (isAffineOpen_chart k (Set.singleton_nonempty i))
    (((twistDerivation k).postcomp (fromTwist k)).restrict le_top) ((dΩ k).restrict le_top)
    (fun a ↦ ?_) W hW a
  refine LocalDerivation.app_eq_of_closure _ _ le_rfl _ (closure_chart k (ne_other i)) ?_ a
  rintro a (⟨c, rfl⟩ | rfl)
  · simp only [LocalDerivation.restrict_app, LocalDerivation.postcomp_app]
    rw [twistDerivation_app k i _ le_rfl, localD, chartLocalDerivation_app_self,
      chartDerivation_chartConst, map_zero, dΩ_chartConst]
  · simp only [LocalDerivation.restrict_app, LocalDerivation.postcomp_app]
    rw [twistDerivation_app k i _ le_rfl, localD, chartLocalDerivation_app_self,
      chartDerivation_coord, map_zsmul, fromTwist_twistGen, omegaGen, smul_smul, sign_mul_self,
      one_smul]

lemma toTwist_comp_fromTwist : toTwist k ≫ fromTwist k = 𝟙 _ := by
  apply ((ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).relativeDifferentialsHomEquiv _).injective
  rw [Scheme.Hom.relativeDifferentialsHomEquiv_apply,
    Scheme.Hom.relativeDifferentialsHomEquiv_apply]
  ext V a
  change (fromTwist k).app V.unop ((toTwist k).app V.unop ((dΩ k).app V.unop le_top a)) =
    (dΩ k).app V.unop le_top a
  rw [toTwist_app_dΩ, fromTwist_twistDerivation]

/-- **The canonical sheaf of `ℙ¹_k`**: `Ω¹_{ℙ¹/k} ≅ 𝒪(-2)`. -/
def relativeDifferentialsIsoTwist :
    (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).relativeDifferentials ≅
      twist (ULift.{u} (Fin 2)) (Spec (.of k)) (-2) where
  hom := toTwist k
  inv := fromTwist k
  hom_inv_id := toTwist_comp_fromTwist k
  inv_hom_id := fromTwist_comp_toTwist k

end Differentials

end AlgebraicGeometry.ProjectiveLine
