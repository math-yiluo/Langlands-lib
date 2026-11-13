import Langlands.Representation.RankinSelberg.FieldTransport.Group
import Langlands.Representation.RankinSelberg.FunctionalEquationStatement
import Langlands.Representation.RankinSelberg.UnequalRankComplementaryConjugationProof
import Langlands.VirtualRepresentation.Supercuspidal.FieldTransport
import Langlands.HarmonicAnalysis.FieldTransport

/-!
# JPSS integrals along an isomorphism of topological fields

Let `σ : F ≃+* E` be a field isomorphism that is a homeomorphism, and let
`T = fieldEquiv n σ` act entrywise on general linear groups. This file proves
that `T` preserves the upper-unipotent subgroups, the standard characters (for
characters with `ψ' ∘ σ = ψ`), determinants, the long and block Weyl elements,
`-1`, inverse transposes, last rows and the unequal-rank block matrices.

The JPSS equal-rank and unequal-rank integrals, their absolute convergence, the
transformed (dual) Whittaker functions and the row Fourier integral are then
compared for functions related by composition with `T`, `σ` and the induced
homeomorphism of left unipotent quotients, with the quotient measure pushed
forward and the scalar Haar measure on `E` the pushforward of the one on `F`.
All comparisons are stated relationally: the hypotheses say that the `E`-side
function composed with the entrywise map is the `F`-side function.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure

universe uF uE

namespace Langlands.RankinSelberg.FieldTransport

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open Langlands.QuotientIntegration

variable {F : Type uF} {E : Type uE} [Field F] [Field E]
  [TopologicalSpace F] [TopologicalSpace E]
  (σ : F ≃+* E) (hσ : Continuous σ) (hσs : Continuous σ.symm)

section Matrices

variable {n : ℕ}

/-- The entrywise map preserves and reflects upper unipotence. -/
theorem fieldEquiv_mem_upperUnipotent_iff (g : Langlands.GeneralLinear n F) :
    fieldEquiv n σ hσ hσs g ∈ upperUnipotent n E ↔ g ∈ upperUnipotent n F := by
  change ((fieldEquiv n σ hσ hσs g).val.IsUpperTriangular ∧
      ∀ i, (fieldEquiv n σ hσ hσs g) i i = 1) ↔ (g.val.IsUpperTriangular ∧ ∀ i, g i i = 1)
  refine and_congr ⟨fun h i j hij => σ.injective ?_, fun h i j hij => ?_⟩
    (forall_congr' fun i => ?_)
  · rw [map_zero]
    exact h hij
  · change σ (g i j) = 0
    rw [h hij, map_zero]
  · rw [fieldEquiv_apply, ← map_one σ]
    exact σ.injective.eq_iff

/-- The entrywise isomorphism of upper-unipotent subgroups. -/
def unipotentEquiv (n : ℕ) : upperUnipotent n F ≃ₜ* upperUnipotent n E :=
  subgroupEquiv (fieldEquiv n σ hσ hσs) (fieldEquiv_mem_upperUnipotent_iff σ hσ hσs)

@[simp] theorem unipotentEquiv_apply_coe (u : upperUnipotent n F) :
    ((unipotentEquiv σ hσ hσs n u : upperUnipotent n E) : Langlands.GeneralLinear n E) =
      fieldEquiv n σ hσ hσs u := rfl

/-- The determinant of the entrywise image is the image of the determinant. -/
theorem det_fieldEquiv (g : Langlands.GeneralLinear n F) :
    Matrix.det (fieldEquiv n σ hσ hσs g).val = σ (Matrix.det g.val) :=
  (RingHom.map_det σ.toRingHom g.val).symm

theorem fieldEquiv_permutation (τ : Equiv.Perm (Fin n)) :
    fieldEquiv n σ hσ hσs (permutation n F τ) = permutation n E τ := by
  apply Units.ext
  ext i j
  change σ (permutation n F τ i j) = permutation n E τ i j
  rw [permutation_entry, permutation_entry]
  split_ifs <;> simp

theorem fieldEquiv_weylLong : fieldEquiv n σ hσ hσs (weylLong n F) = weylLong n E :=
  fieldEquiv_permutation σ hσ hσs _

theorem fieldEquiv_blockWeylAt {r : ℕ} (hnr : n < r) :
    fieldEquiv (r + 1) σ hσ hσs (blockWeylAt n r hnr) = blockWeylAt n r hnr := by
  rw [UnequalRankComplementaryConjugationProof.blockWeylAt_eq F n r hnr,
    UnequalRankComplementaryConjugationProof.blockWeylAt_eq E n r hnr]
  exact fieldEquiv_permutation σ hσ hσs _

theorem fieldEquiv_inverseTranspose (g : Langlands.GeneralLinear n F) :
    fieldEquiv n σ hσ hσs (inverseTranspose n F g) =
      inverseTranspose n E (fieldEquiv n σ hσ hσs g) := by
  apply Units.ext
  rfl

theorem fieldEquiv_neg_one : fieldEquiv n σ hσ hσs (-1) = -1 := by
  apply Units.ext
  ext i j
  change σ (((-1 : Langlands.GeneralLinear n F) : Matrix (Fin n) (Fin n) F) i j) =
    ((-1 : Langlands.GeneralLinear n E) : Matrix (Fin n) (Fin n) E) i j
  simp only [Units.val_neg, Units.val_one, Matrix.neg_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem lastRow_fieldEquiv (g : Langlands.GeneralLinear (n + 1) F) :
    lastRow (fieldEquiv (n + 1) σ hσ hσs g) = fun j => σ (lastRow g j) := rfl

theorem unequalRankMatrix_fieldEquiv (j k : ℕ) (g : Langlands.GeneralLinear (n + 1) F)
    (x : Matrix (Fin j) (Fin (n + 1)) F) :
    unequalRankMatrix j k (fieldEquiv (n + 1) σ hσ hσs g) (x.map σ) =
      fieldEquiv (n + (j + k + 1) + 1) σ hσ hσs (unequalRankMatrix j k g x) := by
  apply Units.ext
  ext a b
  rw [unequalRankMatrix_val]
  change _ = σ ((unequalRankMatrix j k g x).val a b)
  rw [unequalRankMatrix_val, Matrix.add_apply, Matrix.add_apply, map_add]
  congr 1
  · change appendIdentity n (j + k + 1) (fieldEquiv (n + 1) σ hσ hσs g) a b =
      σ (appendIdentity n (j + k + 1) g a b)
    rw [appendIdentity_entry, appendIdentity_entry]
    split_ifs <;> simp
  · simp only [rectangularEntries, Matrix.map_apply]
    split_ifs <;> simp

theorem determinantWeight_fieldEquiv {abv : AbsoluteValue F ℝ} {abv' : AbsoluteValue E ℝ}
    (habv : ∀ x, abv' (σ x) = abv x) (g : Langlands.GeneralLinear n F) (s : ℂ) :
    determinantWeight abv' (fieldEquiv n σ hσ hσs g) s = determinantWeight abv g s := by
  simp only [determinantWeight, det_fieldEquiv, habv]

end Matrices

section Characters

variable {ψ : UnitaryAdditiveCharacter F} {ψ' : UnitaryAdditiveCharacter E}
  (hψ : ∀ x, ψ' (σ x) = ψ x)

include hψ in
theorem standardCharacter_unipotentEquiv (n : ℕ) (u : upperUnipotent (n + 1) F) :
    standardCharacter ψ' n (unipotentEquiv σ hσ hσs (n + 1) u) = standardCharacter ψ n u := by
  apply Units.ext
  rw [standardCharacter_apply, standardCharacter_apply, UnitaryAdditiveCharacter.complex_apply,
    UnitaryAdditiveCharacter.complex_apply]
  have hs : ∑ i : Fin n, (unipotentEquiv σ hσ hσs (n + 1) u).val i.castSucc i.succ =
      σ (∑ i : Fin n, u.val i.castSucc i.succ) := by
    rw [_root_.map_sum]
    rfl
  rw [hs, hψ]

include hψ in
theorem inverseStandardCharacter_unipotentEquiv (n : ℕ) (u : upperUnipotent (n + 1) F) :
    inverseStandardCharacter ψ' n (unipotentEquiv σ hσ hσs (n + 1) u) =
      inverseStandardCharacter ψ n u := by
  change (standardCharacter ψ' n (unipotentEquiv σ hσ hσs (n + 1) u))⁻¹ =
    (standardCharacter ψ n u)⁻¹
  rw [standardCharacter_unipotentEquiv σ hσ hσs hψ]

include hψ in
theorem scale_neg_one_apply [IsTopologicalRing F] [IsTopologicalRing E] (x : F) :
    (ψ'.scale (-1)) (σ x) = (ψ.scale (-1)) x := by
  rw [UnitaryAdditiveCharacter.scale_apply, UnitaryAdditiveCharacter.scale_apply, ← hψ]
  congr 1
  simp

include hψ in
theorem complex_apply_map (x : F) : ψ'.complex (σ x) = ψ.complex x := by
  rw [UnitaryAdditiveCharacter.complex_apply, UnitaryAdditiveCharacter.complex_apply, hψ]

end Characters

section Quotient

variable (n : ℕ)

/-- The homeomorphism of left unipotent quotients induced by `T`. -/
def quotientHomeomorph : LeftUnipotentQuotient n F ≃ₜ LeftUnipotentQuotient n E :=
  cosetHomeomorph (fieldEquiv (n + 1) σ hσ hσs)
    (fieldEquiv_mem_upperUnipotent_iff σ hσ hσs)

variable {n}

@[simp] theorem quotientHomeomorph_mk (g : Langlands.GeneralLinear (n + 1) F) :
    quotientHomeomorph σ hσ hσs n (Quotient.mk _ g) =
      Quotient.mk _ (fieldEquiv (n + 1) σ hσ hσs g) := rfl

end Quotient

section Integrals

variable {ψ : UnitaryAdditiveCharacter F} {ψ' : UnitaryAdditiveCharacter E}
  {abv : AbsoluteValue F ℝ} {abv' : AbsoluteValue E ℝ} (habv : ∀ x, abv' (σ x) = abv x)
  {n : ℕ}

include habv in
theorem equalRankIntegrand_quotientHomeomorph
    {W : WhittakerFunctions ψ n} {W' : InverseWhittakerFunctions ψ n}
    {Φ : SchwartzBruhat (Fin (n + 1) → F)}
    {W₂ : WhittakerFunctions ψ' n} {W₂' : InverseWhittakerFunctions ψ' n}
    {Φ₂ : SchwartzBruhat (Fin (n + 1) → E)}
    (hW : ∀ g, W₂.val (fieldEquiv (n + 1) σ hσ hσs g) = W.val g)
    (hW' : ∀ g, W₂'.val (fieldEquiv (n + 1) σ hσ hσs g) = W'.val g)
    (hΦ : ∀ x : Fin (n + 1) → F, Φ₂ (fun i => σ (x i)) = Φ x) (s : ℂ)
    (q : LeftUnipotentQuotient n F) :
    equalRankIntegrand ψ' abv' W₂ W₂' Φ₂ s (quotientHomeomorph σ hσ hσs n q) =
      equalRankIntegrand ψ abv W W' Φ s q := by
  induction q using Quotient.inductionOn with
  | h g =>
    rw [quotientHomeomorph_mk, equalRankIntegrand_mk, equalRankIntegrand_mk, hW, hW',
      lastRow_fieldEquiv, hΦ (lastRow g), determinantWeight_fieldEquiv σ hσ hσs habv]

include habv in
theorem unequalRankIntegrand_quotientHomeomorph (j k : ℕ)
    {W : WhittakerFunctions ψ (n + (j + k + 1))} {W' : InverseWhittakerFunctions ψ n}
    {W₂ : WhittakerFunctions ψ' (n + (j + k + 1))} {W₂' : InverseWhittakerFunctions ψ' n}
    (hW : ∀ g, W₂.val (fieldEquiv (n + (j + k + 1) + 1) σ hσ hσs g) = W.val g)
    (hW' : ∀ g, W₂'.val (fieldEquiv (n + 1) σ hσ hσs g) = W'.val g) (s : ℂ)
    (x : Matrix (Fin j) (Fin (n + 1)) F) (q : LeftUnipotentQuotient n F) :
    unequalRankIntegrand ψ' abv' j k W₂ W₂' s (x.map σ) (quotientHomeomorph σ hσ hσs n q) =
      unequalRankIntegrand ψ abv j k W W' s x q := by
  induction q using Quotient.inductionOn with
  | h g =>
    rw [quotientHomeomorph_mk, unequalRankIntegrand_mk, unequalRankIntegrand_mk,
      unequalRankMatrix_fieldEquiv, hW, hW', determinantWeight_fieldEquiv σ hσ hσs habv]

variable [MeasurableSpace (LeftUnipotentQuotient n F)] [BorelSpace (LeftUnipotentQuotient n F)]
  [MeasurableSpace (LeftUnipotentQuotient n E)] [BorelSpace (LeftUnipotentQuotient n E)]

theorem map_quotientHomeomorph (μ : Measure (LeftUnipotentQuotient n F)) :
    μ.map (quotientHomeomorph σ hσ hσs n) =
      μ.map (quotientHomeomorph σ hσ hσs n).toMeasurableEquiv := rfl

include habv in
theorem equalRankIntegral_map (μ : Measure (LeftUnipotentQuotient n F))
    {W : WhittakerFunctions ψ n} {W' : InverseWhittakerFunctions ψ n}
    {Φ : SchwartzBruhat (Fin (n + 1) → F)}
    {W₂ : WhittakerFunctions ψ' n} {W₂' : InverseWhittakerFunctions ψ' n}
    {Φ₂ : SchwartzBruhat (Fin (n + 1) → E)}
    (hW : ∀ g, W₂.val (fieldEquiv (n + 1) σ hσ hσs g) = W.val g)
    (hW' : ∀ g, W₂'.val (fieldEquiv (n + 1) σ hσ hσs g) = W'.val g)
    (hΦ : ∀ x : Fin (n + 1) → F, Φ₂ (fun i => σ (x i)) = Φ x) (s : ℂ) :
    equalRankIntegral ψ' abv' (μ.map (quotientHomeomorph σ hσ hσs n)) W₂ W₂' Φ₂ s =
      equalRankIntegral ψ abv μ W W' Φ s := by
  unfold equalRankIntegral
  rw [map_quotientHomeomorph, integral_map_equiv]
  congr 1
  funext q
  exact equalRankIntegrand_quotientHomeomorph σ hσ hσs habv hW hW' hΦ s q

include habv in
theorem equalRankConverges_map_iff (μ : Measure (LeftUnipotentQuotient n F))
    {W : WhittakerFunctions ψ n} {W' : InverseWhittakerFunctions ψ n}
    {Φ : SchwartzBruhat (Fin (n + 1) → F)}
    {W₂ : WhittakerFunctions ψ' n} {W₂' : InverseWhittakerFunctions ψ' n}
    {Φ₂ : SchwartzBruhat (Fin (n + 1) → E)}
    (hW : ∀ g, W₂.val (fieldEquiv (n + 1) σ hσ hσs g) = W.val g)
    (hW' : ∀ g, W₂'.val (fieldEquiv (n + 1) σ hσ hσs g) = W'.val g)
    (hΦ : ∀ x : Fin (n + 1) → F, Φ₂ (fun i => σ (x i)) = Φ x) (s : ℂ) :
    EqualRankConverges ψ' abv' (μ.map (quotientHomeomorph σ hσ hσs n)) W₂ W₂' Φ₂ s ↔
      EqualRankConverges ψ abv μ W W' Φ s := by
  unfold EqualRankConverges
  rw [map_quotientHomeomorph, integrable_map_equiv]
  have he : equalRankIntegrand ψ' abv' W₂ W₂' Φ₂ s ∘
      (quotientHomeomorph σ hσ hσs n).toMeasurableEquiv =
      equalRankIntegrand ψ abv W W' Φ s :=
    funext (equalRankIntegrand_quotientHomeomorph σ hσ hσs habv hW hW' hΦ s)
  rw [he]

variable [MeasurableSpace F] [MeasurableSpace E] [BorelSpace F] [BorelSpace E]

/-- Entrywise transport of rectangular matrices as a measurable equivalence. -/
def matrixMeasurableEquiv (j t : ℕ) : Matrix (Fin j) (Fin t) F ≃ᵐ Matrix (Fin j) (Fin t) E :=
  MeasurableEquiv.piCongrRight fun _ => MeasurableEquiv.piCongrRight fun _ =>
    (HarmonicAnalysis.FieldTransport.homeomorph σ hσ hσs).toMeasurableEquiv

omit [MeasurableSpace (LeftUnipotentQuotient n F)] [BorelSpace (LeftUnipotentQuotient n F)]
  [MeasurableSpace (LeftUnipotentQuotient n E)] [BorelSpace (LeftUnipotentQuotient n E)] in
@[simp] theorem matrixMeasurableEquiv_apply (j t : ℕ) (x : Matrix (Fin j) (Fin t) F) :
    matrixMeasurableEquiv σ hσ hσs j t x = x.map σ := rfl

omit [MeasurableSpace (LeftUnipotentQuotient n F)] [BorelSpace (LeftUnipotentQuotient n F)]
  [MeasurableSpace (LeftUnipotentQuotient n E)] [BorelSpace (LeftUnipotentQuotient n E)] in
/-- Rectangular product measures correspond when the scalar measures do. -/
theorem measurePreserving_matrixMeasurableEquiv (ν : AdditiveHaarMeasure F)
    (ν' : AdditiveHaarMeasure E) [SigmaFinite ν'.measure]
    (hν : ν'.measure = ν.measure.map σ) (j t : ℕ) :
    MeasurePreserving (matrixMeasurableEquiv σ hσ hσs j t) (rectangularMeasure ν j t)
      (rectangularMeasure ν' j t) := by
  have h1 : MeasurePreserving σ ν.measure ν'.measure := ⟨hσ.measurable, hν.symm⟩
  exact measurePreserving_pi _ _ fun _ => measurePreserving_pi _ _ fun _ => h1

include habv in
theorem unequalRankIntegral_map (μ : Measure (LeftUnipotentQuotient n F))
    (ν : AdditiveHaarMeasure F) (ν' : AdditiveHaarMeasure E) [SigmaFinite ν'.measure]
    (hν : ν'.measure = ν.measure.map σ) (j k : ℕ)
    {W : WhittakerFunctions ψ (n + (j + k + 1))} {W' : InverseWhittakerFunctions ψ n}
    {W₂ : WhittakerFunctions ψ' (n + (j + k + 1))} {W₂' : InverseWhittakerFunctions ψ' n}
    (hW : ∀ g, W₂.val (fieldEquiv (n + (j + k + 1) + 1) σ hσ hσs g) = W.val g)
    (hW' : ∀ g, W₂'.val (fieldEquiv (n + 1) σ hσ hσs g) = W'.val g) (s : ℂ) :
    unequalRankIntegral ψ' abv' j k (μ.map (quotientHomeomorph σ hσ hσs n))
        (rectangularMeasure ν' j (n + 1)) W₂ W₂' s =
      unequalRankIntegral ψ abv j k μ (rectangularMeasure ν j (n + 1)) W W' s := by
  unfold unequalRankIntegral
  rw [map_quotientHomeomorph, integral_map_equiv]
  congr 1
  funext q
  rw [← (measurePreserving_matrixMeasurableEquiv σ hσ hσs ν ν' hν j (n + 1)).integral_comp']
  congr 1
  funext x
  exact unequalRankIntegrand_quotientHomeomorph σ hσ hσs habv j k hW hW' s x q

include habv in
theorem unequalRankConverges_map_iff (μ : Measure (LeftUnipotentQuotient n F))
    (ν : AdditiveHaarMeasure F) (ν' : AdditiveHaarMeasure E) [SigmaFinite ν.measure]
    [SigmaFinite ν'.measure] (hν : ν'.measure = ν.measure.map σ) (j k : ℕ)
    {W : WhittakerFunctions ψ (n + (j + k + 1))} {W' : InverseWhittakerFunctions ψ n}
    {W₂ : WhittakerFunctions ψ' (n + (j + k + 1))} {W₂' : InverseWhittakerFunctions ψ' n}
    (hW : ∀ g, W₂.val (fieldEquiv (n + (j + k + 1) + 1) σ hσ hσs g) = W.val g)
    (hW' : ∀ g, W₂'.val (fieldEquiv (n + 1) σ hσ hσs g) = W'.val g) (s : ℂ) :
    UnequalRankConverges ψ' abv' j k (μ.map (quotientHomeomorph σ hσ hσs n))
        (rectangularMeasure ν' j (n + 1)) W₂ W₂' s ↔
      UnequalRankConverges ψ abv j k μ (rectangularMeasure ν j (n + 1)) W W' s := by
  unfold UnequalRankConverges
  rw [← (measurePreserving_matrixMeasurableEquiv σ hσ hσs ν ν' hν j (n + 1)).map_eq,
    map_quotientHomeomorph, integrable_map_prod_map_iff]
  have he : (fun x : LeftUnipotentQuotient n F × Matrix (Fin j) (Fin (n + 1)) F =>
      unequalRankIntegrand ψ' abv' j k W₂ W₂' s
        (matrixMeasurableEquiv σ hσ hσs j (n + 1) x.2)
        ((quotientHomeomorph σ hσ hσs n).toMeasurableEquiv x.1)) =
      fun qx => unequalRankIntegrand ψ abv j k W W' s qx.2 qx.1 := by
    funext x
    exact unequalRankIntegrand_quotientHomeomorph σ hσ hσs habv j k hW hW' s x.2 x.1
  rw [← he]

include habv in
theorem unequalRankIntegralAt_map {r : ℕ} (μ : Measure (LeftUnipotentQuotient n F))
    (ν : AdditiveHaarMeasure F) (ν' : AdditiveHaarMeasure E) [SigmaFinite ν'.measure]
    (hν : ν'.measure = ν.measure.map σ) (j k : ℕ) (hr : r = n + (j + k + 1))
    {W : WhittakerFunctions ψ r} {W' : InverseWhittakerFunctions ψ n}
    {W₂ : WhittakerFunctions ψ' r} {W₂' : InverseWhittakerFunctions ψ' n}
    (hW : ∀ g, W₂.val (fieldEquiv (r + 1) σ hσ hσs g) = W.val g)
    (hW' : ∀ g, W₂'.val (fieldEquiv (n + 1) σ hσ hσs g) = W'.val g) :
    unequalRankIntegralAt j k hr ψ' abv' (μ.map (quotientHomeomorph σ hσ hσs n))
        (rectangularMeasure ν' j (n + 1)) W₂ W₂' =
      unequalRankIntegralAt j k hr ψ abv μ (rectangularMeasure ν j (n + 1)) W W' := by
  subst hr
  funext s
  exact unequalRankIntegral_map σ hσ hσs habv μ ν ν' hν j k hW hW' s

end Integrals

section DualFunctions

variable [IsTopologicalRing F] [IsTopologicalRing E]
  {ψ : UnitaryAdditiveCharacter F} {ψ' : UnitaryAdditiveCharacter E} {n : ℕ}

theorem firstDualFunction_fieldEquiv {f : WhittakerFunctions ψ n}
    {f₂ : WhittakerFunctions ψ' n}
    (hf : ∀ g, f₂.val (fieldEquiv (n + 1) σ hσ hσs g) = f.val g)
    (g : Langlands.GeneralLinear (n + 1) F) :
    (firstDualFunction ψ' n f₂).val (fieldEquiv (n + 1) σ hσ hσs g) =
      (firstDualFunction ψ n f).val g := by
  rw [firstDualFunction_apply, firstDualFunction_apply, ← fieldEquiv_inverseTranspose,
    ← fieldEquiv_weylLong σ hσ hσs, ← map_mul, hf]

theorem secondDualFunction_fieldEquiv {f : InverseWhittakerFunctions ψ n}
    {f₂ : InverseWhittakerFunctions ψ' n}
    (hf : ∀ g, f₂.val (fieldEquiv (n + 1) σ hσ hσs g) = f.val g)
    (g : Langlands.GeneralLinear (n + 1) F) :
    (secondDualFunction ψ' n f₂).val (fieldEquiv (n + 1) σ hσ hσs g) =
      (secondDualFunction ψ n f).val g := by
  rw [secondDualFunction_apply, secondDualFunction_apply, ← fieldEquiv_inverseTranspose,
    ← fieldEquiv_weylLong σ hσ hσs, ← map_mul, hf]

omit [IsTopologicalRing F] [IsTopologicalRing E] in
theorem translateWhittaker_fieldEquiv {f : WhittakerFunctions ψ n}
    {f₂ : WhittakerFunctions ψ' n}
    (hf : ∀ g, f₂.val (fieldEquiv (n + 1) σ hσ hσs g) = f.val g)
    (a g : Langlands.GeneralLinear (n + 1) F) :
    (translateWhittaker ψ' n f₂ (fieldEquiv (n + 1) σ hσ hσs a)).val
        (fieldEquiv (n + 1) σ hσ hσs g) =
      (translateWhittaker ψ n f a).val g := by
  rw [translateWhittaker_apply, translateWhittaker_apply, ← map_mul, hf]

end DualFunctions

section RowFourier

variable [MeasurableSpace F] [MeasurableSpace E] [BorelSpace F] [BorelSpace E] {d : ℕ}

/-- Entrywise transport of row vectors as a measurable equivalence. -/
def rowMeasurableEquiv (d : ℕ) : (Fin d → F) ≃ᵐ (Fin d → E) :=
  MeasurableEquiv.piCongrRight fun _ =>
    (HarmonicAnalysis.FieldTransport.homeomorph σ hσ hσs).toMeasurableEquiv

@[simp] theorem rowMeasurableEquiv_apply (x : Fin d → F) :
    rowMeasurableEquiv σ hσ hσs d x = fun i => σ (x i) := rfl

/-- Row product measures correspond when the scalar measures do. -/
theorem measurePreserving_rowMeasurableEquiv (ν : AdditiveHaarMeasure F)
    (ν' : AdditiveHaarMeasure E) [SigmaFinite ν'.measure]
    (hν : ν'.measure = ν.measure.map σ) (d : ℕ) :
    MeasurePreserving (rowMeasurableEquiv σ hσ hσs d) (rowMeasure ν d) (rowMeasure ν' d) := by
  have h1 : MeasurePreserving σ ν.measure ν'.measure := ⟨hσ.measurable, hν.symm⟩
  exact measurePreserving_pi _ _ fun _ => h1

omit [TopologicalSpace F] [TopologicalSpace E] [MeasurableSpace F] [MeasurableSpace E]
  [BorelSpace F] [BorelSpace E] in
theorem rowPairing_map (x y : Fin d → F) :
    rowPairing (fun i => σ (x i)) (fun i => σ (y i)) = σ (rowPairing x y) := by
  simp only [rowPairing, _root_.map_sum, map_mul]

variable [IsTopologicalRing F] [IsTopologicalRing E]
  {ψ : UnitaryAdditiveCharacter F} {ψ' : UnitaryAdditiveCharacter E}

omit [IsTopologicalRing F] [IsTopologicalRing E] in
include hσ hσs in
theorem rowFourierIntegral_map (hψ : ∀ x, ψ' (σ x) = ψ x) (ν : AdditiveHaarMeasure F)
    (ν' : AdditiveHaarMeasure E) [SigmaFinite ν'.measure]
    (hν : ν'.measure = ν.measure.map σ) {Φ : (Fin d → F) → ℂ} {Φ₂ : (Fin d → E) → ℂ}
    (hΦ : ∀ x, Φ₂ (fun i => σ (x i)) = Φ x) (y : Fin d → F) :
    rowFourierIntegral ψ' ν' d Φ₂ (fun i => σ (y i)) = rowFourierIntegral ψ ν d Φ y := by
  unfold rowFourierIntegral
  rw [← (measurePreserving_rowMeasurableEquiv σ hσ hσs ν ν' hν d).integral_comp']
  congr 1
  funext x
  rw [rowMeasurableEquiv_apply, hΦ, rowPairing_map, complex_apply_map σ hψ]

omit [IsTopologicalRing F] [IsTopologicalRing E] in
include hσ hσs in
theorem isRowFourierPair_map_iff (hψ : ∀ x, ψ' (σ x) = ψ x) (ν : AdditiveHaarMeasure F)
    (ν' : AdditiveHaarMeasure E) [SigmaFinite ν'.measure]
    (hν : ν'.measure = ν.measure.map σ) {Φ Φhat : SchwartzBruhat (Fin d → F)}
    {Φ₂ Φhat₂ : SchwartzBruhat (Fin d → E)}
    (hΦ : ∀ x, Φ₂ (fun i => σ (x i)) = Φ x) (hΦhat : ∀ x, Φhat₂ (fun i => σ (x i)) = Φhat x) :
    IsRowFourierPair ψ' ν' Φ₂ Φhat₂ ↔ IsRowFourierPair ψ ν Φ Φhat := by
  unfold IsRowFourierPair
  constructor
  · intro h y
    rw [← hΦhat y, h, rowFourierIntegral_map σ hσ hσs hψ ν ν' hν hΦ]
  · intro h y'
    have hy : y' = fun i => σ ((fun i => σ.symm (y' i)) i) := by
      funext i
      simp
    rw [hy, hΦhat, h, rowFourierIntegral_map σ hσ hσs hψ ν ν' hν hΦ]

end RowFourier

/-- Entrywise transport of row test functions, `Φ ↦ Φ ∘ σ⁻¹`. -/
def rowTestEquiv (d : ℕ) : SchwartzBruhat (Fin d → F) ≃ₗ[ℂ] SchwartzBruhat (Fin d → E) :=
  Hecke.TestFunction.pullback
    (Homeomorph.piCongrRight fun _ : Fin d =>
      HarmonicAnalysis.FieldTransport.homeomorph σ hσ hσs).symm

theorem rowTestEquiv_apply_map {d : ℕ} (Φ : SchwartzBruhat (Fin d → F)) (x : Fin d → F) :
    rowTestEquiv σ hσ hσs d Φ (fun i => σ (x i)) = Φ x := by
  change Φ (fun i => σ.symm (σ (x i))) = Φ x
  simp

theorem rowTestEquiv_symm_apply {d : ℕ} (Φ₂ : SchwartzBruhat (Fin d → E)) (x : Fin d → F) :
    (rowTestEquiv σ hσ hσs d).symm Φ₂ x = Φ₂ (fun i => σ (x i)) := rfl

end Langlands.RankinSelberg.FieldTransport
