import Langlands.Global.Factors.CuspidalPairSchemeAutomorphy
import Langlands.Global.AdelicBlockParabolicCharacters
import Langlands.Global.AdelicEisensteinSeries

/-! # The cuspidal-pair Eisenstein series as a group-scheme Eisenstein series

On the points of the group scheme `GL_N`, `N = r + t + 2`, the Eisenstein series of a
cuspidal-pair section at `s` is the group-scheme Eisenstein series of the transported section at
the parameter `s λ₁`, where `λ₁ = ((t + 1) det₁ - (r + 1) det₂) / N` is built from the block
determinant characters of the scheme block parabolic. See the paired Markdown. -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry NumberField TensorProduct
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Global.CuspidalPairEisenstein

open Langlands.GeneralLinear
open Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear
open AdelicBlockEisensteinGeometry AdelicGroupPoints GeneralLinearGroupPoints
open AdelicBlockParabolic AdelicBlockDeterminantCharacter PrimitiveAdelicHeight

variable (F : Type u) [Field F] [NumberField F] (r t : ℕ)

/-- The first block of the upper two-block shape. -/
def firstBlock : Fin (blockShape r t).length := ⟨0, Nat.zero_lt_two⟩

/-- The second block of the upper two-block shape. -/
def secondBlock : Fin (blockShape r t).length := ⟨1, Nat.one_lt_two⟩

theorem eq_firstBlock_or_eq_secondBlock (i : Fin (blockShape r t).length) :
    i = firstBlock r t ∨ i = secondBlock r t := by
  rcases i with ⟨k, hk⟩
  change k < 2 at hk
  simp only [firstBlock, secondBlock, Fin.mk.injEq]
  omega

theorem firstBlock_ne_secondBlock : firstBlock r t ≠ secondBlock r t := by
  simp [firstBlock, secondBlock]

theorem prod_blocks {M : Type*} [CommMonoid M] (f : Fin (blockShape r t).length → M) :
    ∏ i, f i = f (firstBlock r t) * f (secondBlock r t) := by
  have huniv : (Finset.univ : Finset (Fin (blockShape r t).length)) =
      {firstBlock r t, secondBlock r t} := by
    ext i
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact eq_firstBlock_or_eq_secondBlock r t i
  rw [huniv, Finset.prod_pair (firstBlock_ne_secondBlock r t)]

theorem prod_filter_firstBlock {M : Type*} [CommMonoid M]
    (f : Fin (blockShape r t).length → M) :
    ∏ j ∈ Finset.univ.filter (fun j => firstBlock r t < j), f j = f (secondBlock r t) := by
  have h : Finset.univ.filter (fun j : Fin (blockShape r t).length => firstBlock r t < j) =
      {secondBlock r t} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rcases eq_firstBlock_or_eq_secondBlock r t j with rfl | rfl
    · simp [firstBlock, secondBlock]
    · simp [firstBlock, secondBlock, Fin.lt_def]
  rw [h, Finset.prod_singleton]

theorem prod_filter_secondBlock {M : Type*} [CommMonoid M]
    (f : Fin (blockShape r t).length → M) :
    ∏ j ∈ Finset.univ.filter (fun j => secondBlock r t < j), f j = 1 := by
  have h : Finset.univ.filter (fun j : Fin (blockShape r t).length => secondBlock r t < j) =
      ∅ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    rcases eq_firstBlock_or_eq_secondBlock r t j with rfl | rfl
    · simp [firstBlock, secondBlock, Fin.lt_def]
    · exact lt_irrefl _
  rw [h, Finset.prod_empty]

/-- The direction `λ₁ = ((t + 1) det₁ - (r + 1) det₂) / N` of Shahidi's line in
`X^*(P) ⊗ ℂ`, `N = r + t + 2`, for the scheme block parabolic of type `(r + 1, t + 1)`. -/
def lineParameter :
    ComplexCharacterParameter F
      (blockParabolicScheme (Fin (r + t + 2)) (CommRingCat.of F)
        (blockShapeWeight (blockShape r t))) :=
  (((t + 1 : ℕ) : ℂ) / ((r + t + 2 : ℕ) : ℂ)) ⊗ₜ[ℤ]
      parabolicBlockCharacter (blockShape r t) (CommRingCat.of F) (firstBlock r t) +
    (-(((r + 1 : ℕ) : ℂ) / ((r + t + 2 : ℕ) : ℂ))) ⊗ₜ[ℤ]
      parabolicBlockCharacter (blockShape r t) (CommRingCat.of F) (secondBlock r t)

/-- The block-modulus character of the upper two-block parabolic in terms of the two
block determinant norms. -/
theorem log_parabolicCharacter (q : Full F (blockShape r t)) :
    Real.log ((parabolicCharacter F (blockShape r t) q : ℝ≥0) : ℝ) =
      ((t + 1 : ℕ) : ℝ) * Real.log ((blockDeterminantNorm F (blockShape r t) (firstBlock r t)
          ((blockShape r t).leviProjection (Adeles F) q) : ℝ≥0) : ℝ) -
        ((r + 1 : ℕ) : ℝ) * Real.log ((blockDeterminantNorm F (blockShape r t) (secondBlock r t)
          ((blockShape r t).leviProjection (Adeles F) q) : ℝ≥0) : ℝ) := by
  set m := (blockShape r t).leviProjection (Adeles F) q
  have hq : parabolicCharacter F (blockShape r t) q = leviCharacter F (blockShape r t) m := rfl
  have hlevi : leviCharacter F (blockShape r t) m =
      blockDeterminantNorm F (blockShape r t) (firstBlock r t) m ^ (t + 1) /
        blockDeterminantNorm F (blockShape r t) (secondBlock r t) m ^ (r + 1) := by
    rw [leviCharacter_apply, prod_blocks, prod_filter_firstBlock, prod_filter_secondBlock,
      mul_one]
    rfl
  rw [hq, hlevi]
  have ha : (0 : ℝ) < ((blockDeterminantNorm F (blockShape r t) (firstBlock r t) m : ℝ≥0) : ℝ) :=
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
  have hb : (0 : ℝ) < ((blockDeterminantNorm F (blockShape r t) (secondBlock r t) m : ℝ≥0) : ℝ) :=
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
  simp only [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val, NNReal.coe_div, NNReal.coe_pow]
  rw [Real.log_div (pow_pos ha _).ne' (pow_pos hb _).ne', Real.log_pow, Real.log_pow]

local instance cuspidalPairSeriesGLAffine (n : ℕ) :
    IsAffine (groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance cuspidalPairSeriesParabolicAffine :
    IsAffine (blockParabolicScheme (Fin (r + t + 2)) (CommRingCat.of F)
      (blockShapeWeight (blockShape r t))).X.left :=
  blockParabolic_isAffine F (blockShape r t)

local instance cuspidalPairSeriesParabolicClosed :
    IsClosedImmersion (blockParabolicHom (Fin (r + t + 2)) (CommRingCat.of F)
      (blockShapeWeight (blockShape r t))).hom.hom.left :=
  isClosedSubgroup_blockParabolicHom (Fin (r + t + 2)) (CommRingCat.of F)
    (blockShapeWeight (blockShape r t))

/-- **The twist on the line.** Shahidi's twist `H(g)^s = δ_P(g)^(s/N)` of the matrix model is
the group-scheme twist `m_P(g)^λ` at `λ = s λ₁`, for the Iwasawa height of the standard
maximal compact subgroup. -/
theorem heightPower_eq_schemeHeightPower (s : ℂ)
    (g : AdelicGroupPoints F (groupScheme (Fin (r + t + 2)) (CommRingCat.of F))) :
    heightPower F r t s (adelicHomeomorph F (r + t + 2) g) =
      (isIwasawaCompact_blockParabolic F (blockShape r t)).heightPower
        (s • lineParameter F r t) g := by
  set hK := isIwasawaCompact_blockParabolic F (blockShape r t)
  obtain ⟨q, k, hqk⟩ := AdelicBlockScalarSections.exists_parabolic_mul_standardCompact F
    (blockShape r t) (adelicHomeomorph F (r + t + 2) g)
  rw [heightPower_eq s q k.property hqk.symm]
  let S := CommAlgCat.of F (AdeleRing (𝓞 F) F)
  let y := (blockParabolicPointsEquiv F (blockShape r t) S).symm q
  have hy : adelicHomeomorph F (r + t + 2)
      (map F _ _ (blockParabolicHom (Fin (r + t + 2)) (CommRingCat.of F)
        (blockShapeWeight (blockShape r t))) y) = q.val := by
    change affinePointsEquiv (Fin (r + t + 2)) (CommRingCat.of F) S
      ((blockParabolicScheme (Fin (r + t + 2)) (CommRingCat.of F)
        (blockShapeWeight (blockShape r t))).affinePointsTarget
          (blockParabolicHom (Fin (r + t + 2)) (CommRingCat.of F)
            (blockShapeWeight (blockShape r t))) S y) = q.val
    rw [← blockParabolicPointsEquiv_val, MulEquiv.apply_symm_apply]
  let z := (adelicHomeomorph F (r + t + 2)).symm k.val
  have hz : z ∈ standardCompactPoints F (r + t + 2) := by
    change (adelicHomeomorph F (r + t + 2)) z ∈ standardCompact F (r + t + 2)
    rw [ContinuousMulEquiv.apply_symm_apply]
    exact k.property
  have hg : map F _ _ (blockParabolicHom (Fin (r + t + 2)) (CommRingCat.of F)
      (blockShapeWeight (blockShape r t))) y * z = g := by
    apply (adelicHomeomorph F (r + t + 2)).injective
    rw [map_mul, hy, ContinuousMulEquiv.apply_symm_apply, hqk]
  have hyq : blockParabolicPointsEquiv F (blockShape r t) S y = q := MulEquiv.apply_symm_apply _ _
  change _ = Complex.exp (complexParameterPairing F _ (s • lineParameter F r t) (hK.height g))
  rw [hK.height_eq hz hg, map_smul, LinearMap.smul_apply, lineParameter, map_add,
    LinearMap.add_apply, complexParameterPairing_tmul, complexParameterPairing_tmul,
    characterLog_parabolicBlockCharacter, characterLog_parabolicBlockCharacter, hyq,
    log_parabolicCharacter]
  congr 1
  push_cast
  ring

section Cosets

local notation "GLN" => groupScheme (Fin (r + t + 2)) (CommRingCat.of F)
local notation "PN" => blockParabolicScheme (Fin (r + t + 2)) (CommRingCat.of F)
  (blockShapeWeight (blockShape r t))
local notation "pN" => blockParabolicHom (Fin (r + t + 2)) (CommRingCat.of F)
  (blockShapeWeight (blockShape r t))

theorem rational_generalLinear_injective :
    Function.Injective (AdelicGroupPoints.rational F GLN) := by
  intro x y h
  apply (rationalEquiv F (r + t + 2)).injective
  apply AdelicGL.rational_injective F (r + t + 2)
  rw [← adelicEquiv_rational, ← adelicEquiv_rational, h]

/-- The rational points of the scheme `GL_N` inside its adelic points, as rational matrices. -/
def rationalPointsEquiv : rationalSubgroup F GLN ≃* RationalGL F (r + t + 2) :=
  (MonoidHom.ofInjective (rational_generalLinear_injective F r t)).symm.trans
    (rationalEquiv F (r + t + 2))

theorem rational_rationalPointsEquiv (c0 : rationalSubgroup F GLN) :
    AdelicGL.rational F (r + t + 2) (rationalPointsEquiv F r t c0) =
      adelicHomeomorph F (r + t + 2) c0.val := by
  obtain ⟨x, hx⟩ := c0.property
  have hc0 : c0 = MonoidHom.ofInjective (rational_generalLinear_injective F r t) x :=
    Subtype.ext hx.symm
  have hsymm : (MonoidHom.ofInjective (rational_generalLinear_injective F r t)).symm c0 = x := by
    rw [MulEquiv.symm_apply_eq, hc0]
  rw [rationalPointsEquiv, MulEquiv.trans_apply]
  erw [hsymm]
  rw [← hx]
  exact (adelicEquiv_rational F (r + t + 2) x).symm

theorem adelicHomeomorph_map_rational_blockParabolic (x : RationalGroupPoints F PN) :
    adelicHomeomorph F (r + t + 2) (map F PN GLN pN (AdelicGroupPoints.rational F PN x)) =
      AdelicGL.rational F (r + t + 2)
        (blockParabolicPointsEquiv F (blockShape r t) (CommAlgCat.of F F) x).val := by
  have hx := (DFunLike.congr_fun (rational_naturality F PN pN) x).symm
  change map F PN GLN pN (AdelicGroupPoints.rational F PN x) =
    AdelicGroupPoints.rational F GLN ((PN).affinePointsTarget pN (CommAlgCat.of F F) x) at hx
  rw [hx]
  exact adelicEquiv_rational F (r + t + 2) _

theorem mem_parabolicRationalSubgroup_iff (c0 : rationalSubgroup F GLN) :
    c0 ∈ parabolicRationalSubgroup F pN ↔
      rationalPointsEquiv F r t c0 ∈ (blockShape r t).parabolic F := by
  rw [parabolicRationalSubgroup, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, hx⟩
    have h := adelicHomeomorph_map_rational_blockParabolic F r t x
    change map F PN GLN pN (AdelicGroupPoints.rational F PN x) = c0.val at hx
    rw [hx, ← rational_rationalPointsEquiv] at h
    rw [AdelicGL.rational_injective F (r + t + 2) h]
    exact (blockParabolicPointsEquiv F (blockShape r t) (CommAlgCat.of F F) x).property
  · intro h
    let x := (blockParabolicPointsEquiv F (blockShape r t) (CommAlgCat.of F F)).symm ⟨_, h⟩
    refine ⟨AdelicGroupPoints.rational F PN x, ⟨x, rfl⟩, ?_⟩
    apply (adelicHomeomorph F (r + t + 2)).injective
    change adelicHomeomorph F (r + t + 2)
      (map F PN GLN pN (AdelicGroupPoints.rational F PN x)) = _
    rw [adelicHomeomorph_map_rational_blockParabolic, MulEquiv.apply_symm_apply,
      rational_rationalPointsEquiv]

/-- The coset spaces `P(F) \ G(F)` of the scheme model and of the matrix model agree. -/
def parabolicCosetsEquiv :
    ParabolicRationalCosets F pN ≃
      Quotient (QuotientGroup.rightRel ((blockShape r t).parabolic F)) :=
  Quotient.congr (rationalPointsEquiv F r t).toEquiv fun a b => by
    rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply,
      mem_parabolicRationalSubgroup_iff]
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, map_mul, map_inv]

end Cosets

section Series

variable {F r t} [CompactSpace (AdeleQuotient F)]
  {T : Automorphic.CuspidalOperatorRealization F r}
  {T' : Automorphic.CuspidalOperatorRealization F t} {φ : AdelicGL F (r + t + 2) → ℂ}

/-- Sections are left invariant under the rational points of the parabolic. -/
theorem isSection_rational_mul (hφ : IsSection T T' φ) (c0 : RationalGL F (r + t + 2))
    (hc0 : c0 ∈ (blockShape r t).parabolic F) (x : AdelicGL F (r + t + 2)) :
    φ (AdelicGL.rational F (r + t + 2) c0 * x) = φ x :=
  AdelicBlockScalarSections.realizedSection_rational F (blockShape r t) (blockRealizations T T')
    (realizedSection hφ) ⟨c0, hc0⟩ x

omit [CompactSpace (AdeleQuotient F)] in
/-- Shahidi's twist is left invariant under the rational points of the parabolic. -/
theorem heightPower_rational_mul (s : ℂ) (c0 : RationalGL F (r + t + 2))
    (hc0 : c0 ∈ (blockShape r t).parabolic F) (x : AdelicGL F (r + t + 2)) :
    heightPower F r t s (AdelicGL.rational F (r + t + 2) c0 * x) = heightPower F r t s x := by
  obtain ⟨q, k, hqk⟩ := AdelicBlockScalarSections.exists_parabolic_mul_standardCompact F
    (blockShape r t) x
  let q' : Full F (blockShape r t) := AdelicBlockParabolic.rational F (blockShape r t) ⟨c0, hc0⟩ * q
  have hq' : q'.val * k.val = AdelicGL.rational F (r + t + 2) c0 * x := by
    rw [hqk, ← mul_assoc]
    rfl
  rw [heightPower_eq s q' k.property hq', heightPower_eq s q k.property hqk.symm, map_mul,
    parabolicCharacter_rational, one_mul]

/-- **The series identity.** On the points of the scheme `GL_N`, the cuspidal-pair Eisenstein
sum at `s` is the group-scheme Eisenstein sum of the transported section at `λ = s λ₁`, for
every `s` (both sums are zero where their terms are not summable). -/
theorem eisensteinSeries_eq_schemeEisensteinSeries (hφ : IsSection T T' φ) (s : ℂ)
    (g : AdelicGroupPoints F (groupScheme (Fin (r + t + 2)) (CommRingCat.of F))) :
    eisensteinSeries F (r := r) (t := t) φ s (adelicHomeomorph F (r + t + 2) g) =
      (isIwasawaCompact_blockParabolic F (blockShape r t)).eisensteinSeries
        (φ ∘ adelicHomeomorph F (r + t + 2)) (s • lineParameter F r t) g := by
  set hK := isIwasawaCompact_blockParabolic F (blockShape r t)
  let f : RationalGL F (r + t + 2) → ℂ := fun y =>
    φ (AdelicGL.rational F (r + t + 2) y * adelicHomeomorph F (r + t + 2) g) *
      heightPower F r t s (AdelicGL.rational F (r + t + 2) y * adelicHomeomorph F (r + t + 2) g)
  have hf : ∀ c0 ∈ (blockShape r t).parabolic F, ∀ y, f (c0 * y) = f y := by
    intro c0 hc0 y
    simp only [f, map_mul, mul_assoc]
    rw [isSection_rational_mul hφ c0 hc0, heightPower_rational_mul s c0 hc0]
  have hterm : ∀ c, f (Quotient.out (parabolicCosetsEquiv F r t c)) =
      hK.eisensteinTerm (φ ∘ adelicHomeomorph F (r + t + 2)) (s • lineParameter F r t) g c := by
    intro c
    have hq : (Quotient.mk _ (Quotient.out (parabolicCosetsEquiv F r t c)) :
        Quotient (QuotientGroup.rightRel ((blockShape r t).parabolic F))) =
        Quotient.mk _ (rationalPointsEquiv F r t (Quotient.out c)) := by
      rw [Quotient.out_eq]
      conv_lhs => rw [← Quotient.out_eq c]
      rfl
    have hrel := QuotientGroup.rightRel_apply.mp (Quotient.exact hq)
    have hsplit : rationalPointsEquiv F r t (Quotient.out c) =
        (rationalPointsEquiv F r t (Quotient.out c) *
          (Quotient.out (parabolicCosetsEquiv F r t c))⁻¹) *
          Quotient.out (parabolicCosetsEquiv F r t c) := by group
    rw [← hf _ hrel, ← hsplit]
    simp only [f, rational_rationalPointsEquiv, ← map_mul]
    rw [heightPower_eq_schemeHeightPower]
    rfl
  change ∑' c, f (Quotient.out c) = ∑' c, hK.eisensteinTerm _ _ g c
  rw [← (parabolicCosetsEquiv F r t).tsum_eq]
  exact tsum_congr hterm

end Series

section Comparison

open Langlands.Automorphic.GroupSchemeFunctions

/-- **The group-scheme model of the cuspidal-pair Eisenstein series.** Let `F : Type u` be a
number field with compact adele quotient, `T`, `T'` actual cuspidal realizations of ranks `r + 1`
and `t + 1`, and `φ` a section in the sense of `IsSection T T'`. Transport `φ` to the points of
the group scheme `GL_N`, `N = r + t + 2`, along `adelicHomeomorph`. Then

* for all smooth-structure data `hsmooth`, `hcalc` of `GL_N`, the transported section is an
  automorphic function on `U_P(𝔸) M(F) \ GL_N(𝔸)` for the scheme block parabolic `P` of type
  `(r + 1, t + 1)`, its block-unipotent radical and block-diagonal Levi, the archimedean part of
  the standard maximal compact subgroup and the standard matrix embedding;
* for every `s ∈ ℂ` and every adelic point `g`, the actual sum `eisensteinSeries F φ s` at
  `adelicHomeomorph g` is the group-scheme Eisenstein sum of the transported section at the
  parameter `s • lineParameter F r t` for the Iwasawa height of the standard maximal compact
  subgroup. -/
def CuspidalPairSchemeComparisonStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r t : ℕ)
    (T : Automorphic.CuspidalOperatorRealization F r)
    (T' : Automorphic.CuspidalOperatorRealization F t) (φ : AdelicGL F (r + t + 2) → ℂ),
    IsSection T T' φ →
      (∀ {d : ℕ} (hsmooth : SmoothOfRelativeDimension d
          (groupScheme (Fin (r + t + 2)) (CommRingCat.of F)).X.hom)
        (hcalc : AdelicDifferentialCommutator F
          (groupScheme (Fin (r + t + 2)) (CommRingCat.of F)) hsmooth),
        IsAutomorphicFunctionOn F
          (groupScheme (Fin (r + t + 2)) (CommRingCat.of F)) hsmooth hcalc
          (parabolicQuotientSubgroup F
            (blockParabolicHom (Fin (r + t + 2)) (CommRingCat.of F)
              (blockShapeWeight (blockShape r t)))
            (blockUnipotentInclusion F (blockShape r t)) (blockLeviInclusion F (blockShape r t)))
          ((standardCompactPoints F (r + t + 2)).comap
            (ofInfinite F (groupScheme (Fin (r + t + 2)) (CommRingCat.of F))).toMonoidHom)
          (MatrixRepresentation.standard (Fin (r + t + 2)) (CommRingCat.of F))
          (φ ∘ adelicHomeomorph F (r + t + 2))) ∧
      ∀ (s : ℂ) (g : AdelicGroupPoints F (groupScheme (Fin (r + t + 2)) (CommRingCat.of F))),
        eisensteinSeries F (r := r) (t := t) φ s (adelicHomeomorph F (r + t + 2) g) =
          (isIwasawaCompact_blockParabolic F (blockShape r t)).eisensteinSeries
            (φ ∘ adelicHomeomorph F (r + t + 2)) (s • lineParameter F r t) g

theorem cuspidalPairSchemeComparison : CuspidalPairSchemeComparisonStatement.{u} :=
  fun _ _ _ _ _ _ _ _ _ hφ =>
    ⟨fun hsmooth hcalc => isAutomorphicFunctionOn_of_isSection hφ hsmooth hcalc,
      fun s g => eisensteinSeries_eq_schemeEisensteinSeries hφ s g⟩

end Comparison

end Langlands.Global.CuspidalPairEisenstein
