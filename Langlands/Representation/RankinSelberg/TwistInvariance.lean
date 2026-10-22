import Langlands.Representation.RankinSelberg.LocalFactor
import Langlands.Representation.Whittaker.Twist

/-!
# Determinant twists of JPSS zeta values

Twisting `π` by `χ ∘ det` and `π'` by `χ⁻¹ ∘ det` leaves every JPSS integrand
unchanged, because the large block matrix has the determinant of its corner.
Hence the zeta values and L-polynomials of the twisted pair are those of the pair.
-/

noncomputable section

namespace Langlands.RankinSelberg

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open MeasureTheory Polynomial

universe uF uV uV'

section Determinants

variable {F : Type uF} [Field F]

omit [Field F] in
/-- The standard rank inclusion `g ↦ diag(g, I_m)` preserves the determinant. -/
theorem det_rankInclusion {R : Type uF} [CommRing R] {n : ℕ} (m : ℕ)
    (g : Langlands.GeneralLinear n R) :
    Matrix.det (rankInclusion m g).val = Matrix.det g.val := by
  change Matrix.det (Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks g.val 0 0 (1 : Langlands.GeneralLinear m R).val)) = _
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Units.val_one, Matrix.det_one,
    mul_one]

/-- Appending an identity block preserves the determinant. -/
theorem det_appendIdentity (n : ℕ) :
    ∀ (d : ℕ) (g : Langlands.GeneralLinear (n + 1) F),
      Matrix.det (appendIdentity n d g).val = Matrix.det g.val
  | 0, _ => rfl
  | d + 1, g => by
    change Matrix.det (rankInclusion 1 (appendIdentity n d g)).val = _
    rw [det_rankInclusion, det_appendIdentity n d g]

/-- The rectangular unipotent factor `1 + X` has determinant one. -/
theorem det_rectangularUnipotent {n : ℕ} (j k : ℕ) (x : Matrix (Fin j) (Fin (n + 1)) F) :
    Matrix.det (rectangularUnipotent j k x).val = 1 := by
  change Matrix.det (1 + rectangularEntries j k x) = 1
  have hlow : (1 + rectangularEntries j k x).IsLowerTriangular := by
    intro a b hab
    change a < b at hab
    have ha : a ≠ b := ne_of_lt hab
    simp only [Matrix.add_apply, Matrix.one_apply_ne ha, zero_add, rectangularEntries]
    split_ifs with h1 h2
    · exfalso
      have : a.val < b.val := hab
      omega
    · rfl
    · rfl
  rw [Matrix.det_of_isLowerTriangular _ hlow]
  apply Finset.prod_eq_one
  intro a _
  simp only [Matrix.add_apply, Matrix.one_apply_eq, rectangularEntries]
  split_ifs with h1 h2
  · exfalso
    omega
  · simp
  · simp

/-- The unequal-rank block matrix has the determinant of its corner. -/
theorem determinant_unequalRankMatrix {n : ℕ} (j k : ℕ)
    (g : Langlands.GeneralLinear (n + 1) F) (x : Matrix (Fin j) (Fin (n + 1)) F) :
    determinant (unequalRankMatrix j k g x) = determinant g := by
  apply Units.ext
  change Matrix.det ((appendIdentity n (j + k + 1) g).val * (rectangularUnipotent j k x).val) =
    Matrix.det g.val
  rw [Matrix.det_mul, det_appendIdentity, det_rectangularUnipotent, mul_one]

end Determinants

section WhittakerSets

variable {F : Type uF} [Field F] [TopologicalSpace F]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (ψ : UnitaryAdditiveCharacter F) {n : ℕ} (χ : Fˣ →* ℂˣ)

/-- The Whittaker functions of `π ⊗ (χ ∘ det)` are those of `π` multiplied by
`χ(det g)`. -/
theorem mem_whittakerSet_twist_iff
    {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
    {W : WhittakerFunctions ψ n} :
    W ∈ whittakerSet ψ n (Langlands.twist (χ.comp determinant) π) ↔
      ∃ W₀ ∈ whittakerSet ψ n π, ∀ g, W.val g = (χ (determinant g) : ℂ) * W₀.val g := by
  constructor
  · rintro ⟨ℓ, v, rfl⟩
    let ℓ₀ : glFunctionals ψ n π :=
      untwistFunctional _ _ (χ.comp determinant) (determinantCharacter_unipotent χ) π ℓ
    refine ⟨coefficientMap π ℓ₀ v, ⟨ℓ₀, v, rfl⟩, fun g => ?_⟩
    exact (congrFun (twistFunction_coefficient _ _ (χ.comp determinant)
      (determinantCharacter_unipotent χ) π ℓ₀ v) g).symm
  · rintro ⟨W₀, ⟨ℓ₀, v, rfl⟩, hW⟩
    refine ⟨twistFunctional _ _ (χ.comp determinant) (determinantCharacter_unipotent χ) π ℓ₀,
      v, ?_⟩
    apply Subtype.ext
    funext g
    rw [hW g]
    exact (congrFun (twistFunction_coefficient _ _ (χ.comp determinant)
      (determinantCharacter_unipotent χ) π ℓ₀ v) g).symm

/-- The inverse-character version of `mem_whittakerSet_twist_iff`. -/
theorem mem_inverseWhittakerSet_twist_iff
    {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
    {W : InverseWhittakerFunctions ψ n} :
    W ∈ inverseWhittakerSet ψ n (Langlands.twist (χ.comp determinant) π) ↔
      ∃ W₀ ∈ inverseWhittakerSet ψ n π, ∀ g, W.val g = (χ (determinant g) : ℂ) * W₀.val g := by
  constructor
  · rintro ⟨ℓ, v, rfl⟩
    let ℓ₀ : glInverseFunctionals ψ n π :=
      untwistFunctional _ _ (χ.comp determinant) (determinantCharacter_unipotent χ) π ℓ
    refine ⟨coefficientMap π ℓ₀ v, ⟨ℓ₀, v, rfl⟩, fun g => ?_⟩
    exact (congrFun (twistFunction_coefficient _ _ (χ.comp determinant)
      (determinantCharacter_unipotent χ) π ℓ₀ v) g).symm
  · rintro ⟨W₀, ⟨ℓ₀, v, rfl⟩, hW⟩
    refine ⟨twistFunctional _ _ (χ.comp determinant) (determinantCharacter_unipotent χ) π ℓ₀,
      v, ?_⟩
    apply Subtype.ext
    funext g
    rw [hW g]
    exact (congrFun (twistFunction_coefficient _ _ (χ.comp determinant)
      (determinantCharacter_unipotent χ) π ℓ₀ v) g).symm

end WhittakerSets

section Integrands

variable {F : Type uF} [Field F] [TopologicalSpace F]
variable (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)

/-- Equal-rank integrands agree when the products of the two Whittaker functions agree. -/
theorem equalRankIntegrand_congr {n : ℕ} {W₁ W₂ : WhittakerFunctions ψ n}
    {W₁' W₂' : InverseWhittakerFunctions ψ n}
    (h : ∀ g, W₁.val g * W₁'.val g = W₂.val g * W₂'.val g)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) (s : ℂ) :
    equalRankIntegrand ψ abv W₁ W₁' Φ s = equalRankIntegrand ψ abv W₂ W₂' Φ s := by
  funext q
  induction q using Quotient.inductionOn with
  | h g => simp only [equalRankIntegrand_mk, h g]

/-- Unequal-rank integrands agree when the products of the two Whittaker
functions agree at every block matrix. -/
theorem unequalRankIntegrand_congr {n : ℕ} (j k : ℕ)
    {W₁ W₂ : WhittakerFunctions ψ (n + (j + k + 1))}
    {W₁' W₂' : InverseWhittakerFunctions ψ n}
    (h : ∀ g x, W₁.val (unequalRankMatrix j k g x) * W₁'.val g =
      W₂.val (unequalRankMatrix j k g x) * W₂'.val g) (s : ℂ) :
    unequalRankIntegrand ψ abv j k W₁ W₁' s = unequalRankIntegrand ψ abv j k W₂ W₂' s := by
  funext x q
  induction q using Quotient.inductionOn with
  | h g => simp only [unequalRankIntegrand_mk, h g x]

omit [TopologicalSpace F] in
/-- The twisting multipliers `χ(det g)` and `χ(det g)⁻¹` cancel. -/
theorem twist_product_cancel (χ : Fˣ →* ℂˣ) {m : ℕ} (g : Langlands.GeneralLinear m F)
    (a b : ℂ) :
    ((χ (determinant g) : ℂ) * a) * (((χ⁻¹) (determinant g) : ℂ) * b) = a * b := by
  rw [MonoidHom.inv_apply, mul_mul_mul_comm, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    one_mul]

end Integrands

section ZetaValues

variable {F : Type uF} [Field F] [TopologicalSpace F]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {V' : Type uV'} [AddCommGroup V'] [Module ℂ V']
variable (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ) (χ : Fˣ →* ℂˣ)

/-- Equal-rank zeta values of `(π ⊗ χ, π' ⊗ χ⁻¹)` are those of `(π, π')`. -/
theorem equalRankZetaValues_twist {n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
    (μ : Measure (LeftUnipotentQuotient n F))
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (π' : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V') :
    equalRankZetaValues q ψ abv μ (Langlands.twist (χ.comp determinant) π)
        (Langlands.twist ((χ⁻¹).comp determinant) π') =
      equalRankZetaValues q ψ abv μ π π' := by
  ext R
  constructor
  · rintro ⟨W, hW, W', hW', Φ, hconv, hR⟩
    obtain ⟨W₀, hW₀, hWeq⟩ := (mem_whittakerSet_twist_iff ψ χ).1 hW
    obtain ⟨W₀', hW₀', hW'eq⟩ := (mem_inverseWhittakerSet_twist_iff ψ χ⁻¹).1 hW'
    have hI : ∀ s, equalRankIntegrand ψ abv W W' Φ s = equalRankIntegrand ψ abv W₀ W₀' Φ s :=
      equalRankIntegrand_congr ψ abv (fun g => by rw [hWeq g, hW'eq g, twist_product_cancel])
        Φ
    refine ⟨W₀, hW₀, W₀', hW₀', Φ, ?_, ?_⟩
    · obtain ⟨a, ha⟩ := hconv
      exact ⟨a, fun s hs => by
        have := ha s hs
        rwa [EqualRankConverges, hI] at this⟩
    · have hfun : equalRankIntegral ψ abv μ W W' Φ = equalRankIntegral ψ abv μ W₀ W₀' Φ := by
        funext s
        simp only [equalRankIntegral, hI]
      rwa [hfun] at hR
  · rintro ⟨W₀, hW₀, W₀', hW₀', Φ, hconv, hR⟩
    let W : WhittakerFunctions ψ n :=
      twistFunctionEquiv _ _ (χ.comp determinant) (determinantCharacter_unipotent χ) W₀
    let W' : InverseWhittakerFunctions ψ n :=
      twistFunctionEquiv _ _ ((χ⁻¹).comp determinant) (determinantCharacter_unipotent χ⁻¹) W₀'
    have hW : W ∈ whittakerSet ψ n (Langlands.twist (χ.comp determinant) π) :=
      (mem_whittakerSet_twist_iff ψ χ).2 ⟨W₀, hW₀, fun _ => rfl⟩
    have hW' : W' ∈ inverseWhittakerSet ψ n (Langlands.twist ((χ⁻¹).comp determinant) π') :=
      (mem_inverseWhittakerSet_twist_iff ψ χ⁻¹).2 ⟨W₀', hW₀', fun _ => rfl⟩
    have hI : ∀ s, equalRankIntegrand ψ abv W W' Φ s = equalRankIntegrand ψ abv W₀ W₀' Φ s :=
      equalRankIntegrand_congr ψ abv (fun g => twist_product_cancel χ g _ _) Φ
    refine ⟨W, hW, W', hW', Φ, ?_, ?_⟩
    · obtain ⟨a, ha⟩ := hconv
      exact ⟨a, fun s hs => by
        have := ha s hs
        rwa [EqualRankConverges, ← hI] at this⟩
    · have hfun : equalRankIntegral ψ abv μ W W' Φ = equalRankIntegral ψ abv μ W₀ W₀' Φ := by
        funext s
        simp only [equalRankIntegral, hI]
      rwa [hfun]

/-- Unequal-rank zeta values of `(π ⊗ χ, π' ⊗ χ⁻¹)` are those of `(π, π')`. -/
theorem unequalRankZetaValues_twist {n : ℕ} (j k : ℕ)
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    (μ : Measure (LeftUnipotentQuotient n F)) (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    (π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) F) V)
    (π' : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V') :
    unequalRankZetaValues q ψ abv j k μ ν (Langlands.twist (χ.comp determinant) π)
        (Langlands.twist ((χ⁻¹).comp determinant) π') =
      unequalRankZetaValues q ψ abv j k μ ν π π' := by
  have hblock : ∀ (g : Langlands.GeneralLinear (n + 1) F) (x : Matrix (Fin j) (Fin (n + 1)) F)
      (a b : ℂ), ((χ (determinant (unequalRankMatrix j k g x)) : ℂ) * a) *
        (((χ⁻¹) (determinant g) : ℂ) * b) = a * b := by
    intro g x a b
    rw [determinant_unequalRankMatrix, twist_product_cancel]
  ext R
  constructor
  · rintro ⟨W, hW, W', hW', hconv, hR⟩
    obtain ⟨W₀, hW₀, hWeq⟩ := (mem_whittakerSet_twist_iff ψ χ).1 hW
    obtain ⟨W₀', hW₀', hW'eq⟩ := (mem_inverseWhittakerSet_twist_iff ψ χ⁻¹).1 hW'
    have hI : ∀ s, unequalRankIntegrand ψ abv j k W W' s =
        unequalRankIntegrand ψ abv j k W₀ W₀' s :=
      unequalRankIntegrand_congr ψ abv j k (fun g x => by rw [hWeq, hW'eq g, hblock])
    refine ⟨W₀, hW₀, W₀', hW₀', ?_, ?_⟩
    · obtain ⟨a, ha⟩ := hconv
      exact ⟨a, fun s hs => by
        have := ha s hs
        rwa [UnequalRankConverges, hI] at this⟩
    · have hfun : unequalRankIntegral ψ abv j k μ ν W W' =
          unequalRankIntegral ψ abv j k μ ν W₀ W₀' := by
        funext s
        simp only [unequalRankIntegral, hI]
      rwa [hfun] at hR
  · rintro ⟨W₀, hW₀, W₀', hW₀', hconv, hR⟩
    let W : WhittakerFunctions ψ (n + (j + k + 1)) :=
      twistFunctionEquiv _ _ (χ.comp determinant) (determinantCharacter_unipotent χ) W₀
    let W' : InverseWhittakerFunctions ψ n :=
      twistFunctionEquiv _ _ ((χ⁻¹).comp determinant) (determinantCharacter_unipotent χ⁻¹) W₀'
    have hW : W ∈ whittakerSet ψ (n + (j + k + 1)) (Langlands.twist (χ.comp determinant) π) :=
      (mem_whittakerSet_twist_iff ψ χ).2 ⟨W₀, hW₀, fun _ => rfl⟩
    have hW' : W' ∈ inverseWhittakerSet ψ n (Langlands.twist ((χ⁻¹).comp determinant) π') :=
      (mem_inverseWhittakerSet_twist_iff ψ χ⁻¹).2 ⟨W₀', hW₀', fun _ => rfl⟩
    have hI : ∀ s, unequalRankIntegrand ψ abv j k W W' s =
        unequalRankIntegrand ψ abv j k W₀ W₀' s :=
      unequalRankIntegrand_congr ψ abv j k (fun g x => hblock g x _ _)
    refine ⟨W, hW, W', hW', ?_, ?_⟩
    · obtain ⟨a, ha⟩ := hconv
      exact ⟨a, fun s hs => by
        have := ha s hs
        rwa [UnequalRankConverges, ← hI] at this⟩
    · have hfun : unequalRankIntegral ψ abv j k μ ν W W' =
          unequalRankIntegral ψ abv j k μ ν W₀ W₀' := by
        funext s
        simp only [unequalRankIntegral, hI]
      rwa [hfun]

/-- The equal-rank L-polynomial of `(π ⊗ χ, π' ⊗ χ⁻¹)` is that of `(π, π')`. -/
theorem isEqualRankLPolynomial_twist {n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
    (μ : Measure (LeftUnipotentQuotient n F))
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (π' : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V') (P : ℂ[X]) :
    IsEqualRankLPolynomial q ψ abv μ (Langlands.twist (χ.comp determinant) π)
        (Langlands.twist ((χ⁻¹).comp determinant) π') P ↔
      IsEqualRankLPolynomial q ψ abv μ π π' P := by
  rw [IsEqualRankLPolynomial, IsEqualRankLPolynomial, equalRankZetaValues_twist]

/-- The unequal-rank L-polynomial of `(π ⊗ χ, π' ⊗ χ⁻¹)` is that of `(π, π')`. -/
theorem isUnequalRankLPolynomial_twist {n : ℕ} (j k : ℕ)
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    (μ : Measure (LeftUnipotentQuotient n F)) (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    (π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) F) V)
    (π' : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V') (P : ℂ[X]) :
    IsUnequalRankLPolynomial q ψ abv j k μ ν (Langlands.twist (χ.comp determinant) π)
        (Langlands.twist ((χ⁻¹).comp determinant) π') P ↔
      IsUnequalRankLPolynomial q ψ abv j k μ ν π π' P := by
  rw [IsUnequalRankLPolynomial, IsUnequalRankLPolynomial, unequalRankZetaValues_twist]

omit [TopologicalSpace F] in
/-- Twisting the rank-one character `χη` by `η⁻¹` gives `χ`. -/
theorem twist_rankOneCharacter (η : Fˣ →* ℂˣ) :
    Langlands.twist ((η⁻¹).comp determinant) (rankOneCharacter (F := F) (χ * η)) =
      rankOneCharacter χ := by
  refine MonoidHom.ext fun g => LinearMap.ext fun v => ?_
  have h : ((η⁻¹).comp determinant g) * ((χ * η).comp determinant g) =
      χ.comp determinant g := by
    simp only [MonoidHom.comp_apply, MonoidHom.inv_apply, MonoidHom.mul_apply]
    rw [mul_comm, mul_assoc, mul_inv_cancel, mul_one]
  change (((η⁻¹).comp determinant g : ℂˣ) : ℂ) * ((((χ * η).comp determinant g : ℂˣ) : ℂ) * v) =
    ((χ.comp determinant g : ℂˣ) : ℂ) * v
  rw [← mul_assoc, ← Units.val_mul, h]

omit [TopologicalSpace F] in
/-- The identity relabelling `characterPairRank` preserves the determinant. -/
theorem determinant_characterPairRank (m : ℕ)
    (g : Langlands.GeneralLinear (0 + (0 + m + 1) + 1) F) :
    determinant (characterPairRank m g) = determinant g := by
  apply Units.ext
  change Matrix.det (Matrix.reindex (finCongr (by omega)) (finCongr (by omega)) g.val) =
    Matrix.det g.val
  exact Matrix.det_reindex_self _ _

omit [TopologicalSpace F] in
/-- Determinant twists commute with the relabelling `characterPairRank`. -/
theorem twist_comp_characterPairRank (η : Fˣ →* ℂˣ) (m : ℕ)
    (π : Representation ℂ (Langlands.GeneralLinear (m + 1 + 1) F) V) :
    (Langlands.twist (η.comp determinant) π).comp (characterPairRank m).toMonoidHom =
      Langlands.twist (η.comp determinant) (π.comp (characterPairRank m).toMonoidHom) := by
  ext g v
  change ((η (determinant (characterPairRank m g)) : ℂ) • π (characterPairRank m g)) v =
    ((η (determinant g) : ℂ) • π (characterPairRank m g)) v
  rw [determinant_characterPairRank]

/-- `L(s, (π ⊗ η) × χ) = L(s, π × χη)` at the level of zeta values. -/
theorem characterZetaValues_twist [MeasurableSpace (LeftUnipotentQuotient 0 F)]
    (μ : Measure (LeftUnipotentQuotient 0 F)) (η : Fˣ →* ℂˣ) :
    ∀ (m : ℕ) (π : Representation ℂ (Langlands.GeneralLinear (m + 1) F) V),
      characterZetaValues q ψ abv μ χ m (Langlands.twist (η.comp determinant) π) =
        characterZetaValues q ψ abv μ (χ * η) m π
  | 0, π => by
    change equalRankZetaValues q ψ abv μ (Langlands.twist (η.comp determinant) π)
        (rankOneCharacter χ) =
      equalRankZetaValues q ψ abv μ π (rankOneCharacter (χ * η))
    rw [← equalRankZetaValues_twist q ψ abv η μ π (rankOneCharacter (χ * η)),
      twist_rankOneCharacter]
  | m + 1, π => by
    let : MeasurableSpace (Matrix (Fin 0) (Fin (0 + 1)) F) := ⊤
    change unequalRankZetaValues q ψ abv 0 m μ (Measure.dirac 0)
        ((Langlands.twist (η.comp determinant) π).comp (characterPairRank m).toMonoidHom)
        (rankOneCharacter χ) =
      unequalRankZetaValues q ψ abv 0 m μ (Measure.dirac 0)
        (π.comp (characterPairRank m).toMonoidHom) (rankOneCharacter (χ * η))
    rw [twist_comp_characterPairRank, ← unequalRankZetaValues_twist q ψ abv η 0 m μ
      (Measure.dirac 0) _ (rankOneCharacter (χ * η)), twist_rankOneCharacter]

/-- The L-polynomial of `(π ⊗ η) × χ` is that of `π × χη`. -/
theorem isCharacterLPolynomial_twist [MeasurableSpace (LeftUnipotentQuotient 0 F)]
    (μ : Measure (LeftUnipotentQuotient 0 F)) (η : Fˣ →* ℂˣ) {m : ℕ}
    (π : Representation ℂ (Langlands.GeneralLinear (m + 1) F) V) (P : ℂ[X]) :
    IsCharacterLPolynomial q ψ abv μ χ (Langlands.twist (η.comp determinant) π) P ↔
      IsCharacterLPolynomial q ψ abv μ (χ * η) π P := by
  rw [IsCharacterLPolynomial, IsCharacterLPolynomial, characterZetaValues_twist]

/-- In particular the standard L-polynomial of `π ⊗ η` is that of `π × η`. -/
theorem isStandardLPolynomial_twist [MeasurableSpace (LeftUnipotentQuotient 0 F)]
    (μ : Measure (LeftUnipotentQuotient 0 F)) (η : Fˣ →* ℂˣ) {m : ℕ}
    (π : Representation ℂ (Langlands.GeneralLinear (m + 1) F) V) (P : ℂ[X]) :
    IsCharacterLPolynomial q ψ abv μ 1 (Langlands.twist (η.comp determinant) π) P ↔
      IsCharacterLPolynomial q ψ abv μ η π P := by
  rw [isCharacterLPolynomial_twist, show (1 : Fˣ →* ℂˣ) * η = η from MonoidHom.ext fun _ => one_mul _]

end ZetaValues

end Langlands.RankinSelberg
