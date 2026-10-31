import Langlands.Representation.Induction.SplitKernelCovariance

/-! The natural equivariant split-kernel integral with its actual Haar character. -/

noncomputable section

namespace Langlands.Induction

open MeasureTheory MeasureTheory.Measure
open QuotientIntegration HarmonicAnalysis
open scoped NNReal ENNReal

universe uG uL uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {L : Type uL} [Group L]
variable (r : G →* L) (s : L →* G) (H : Subgroup G) (hsH : ∀ l, s l ∈ H)

local notation "I" => H.comap r.ker.subtype
local notation "α" => splitKernelConjugation r s
local notation "hα" => splitKernelConjugation_mem r s H hsH

/-- The actual restriction of section inverse conjugation to the intersection. -/
def splitKernelIntersectionConjugation (l : L) : I ≃ₜ* I :=
  subgroupAutomorphism I (α l) (hα l)

@[simp] theorem splitKernelConjugation_one :
    α 1 = ContinuousMulEquiv.refl r.ker := by
  ext n
  simp [splitKernelConjugation_apply]

/-- Inverse conjugation reverses the order of the section factors. -/
theorem splitKernelConjugation_mul (l k : L) :
    α (l * k) = (α l).trans (α k) := by
  ext n
  simp [splitKernelConjugation_apply, mul_assoc]

@[simp] theorem splitKernelIntersectionConjugation_one :
    splitKernelIntersectionConjugation r s H hsH 1 = ContinuousMulEquiv.refl I := by
  apply ContinuousMulEquiv.ext
  intro i
  apply Subtype.ext
  change α 1 (i : r.ker) = (i : r.ker)
  rw [splitKernelConjugation_one]
  rfl

theorem splitKernelIntersectionConjugation_mul (l k : L) :
    splitKernelIntersectionConjugation r s H hsH (l * k) =
      (splitKernelIntersectionConjugation r s H hsH l).trans
        (splitKernelIntersectionConjugation r s H hsH k) := by
  apply ContinuousMulEquiv.ext
  intro i
  apply Subtype.ext
  change α (l * k) (i : r.ker) = α k (α l (i : r.ker))
  rw [splitKernelConjugation_mul]
  rfl

section Character

variable [LocallyCompactSpace r.ker]
variable [MeasurableSpace r.ker] [BorelSpace r.ker]
variable [MeasurableSpace (H.comap r.ker.subtype)] [BorelSpace (H.comap r.ker.subtype)]
variable (hH : IsClosed (H : Set G))

/-- The positive character given by the actual forward-precomposition
subgroup-to-kernel Haar ratio. Local compactness of the intersection is derived. -/
def splitKernelHaarRatio : L →* ℝ≥0ˣ := by
  let : LocallyCompactSpace I := (isClosed_splitKernelIntersection r H hH).locallyCompactSpace
  exact
    { toFun l := Units.mk0
        (mulEquivHaarChar (splitKernelIntersectionConjugation r s H hsH l) /
          mulEquivHaarChar (α l))
        (div_ne_zero (mulEquivHaarChar_pos _).ne' (mulEquivHaarChar_pos _).ne')
      map_one' := by
        apply Units.ext
        simp only [Units.val_mk0, splitKernelIntersectionConjugation_one,
          splitKernelConjugation_one, mulEquivHaarChar_refl, div_self one_ne_zero, Units.val_one]
      map_mul' l k := by
        apply Units.ext
        simp only [Units.val_mk0, Units.val_mul, splitKernelIntersectionConjugation_mul,
          splitKernelConjugation_mul, mulEquivHaarChar_trans]
        exact (div_mul_div_comm
          (mulEquivHaarChar (splitKernelIntersectionConjugation r s H hsH l))
          (mulEquivHaarChar (α l))
          (mulEquivHaarChar (splitKernelIntersectionConjugation r s H hsH k))
          (mulEquivHaarChar (α k))).symm }

@[simp] theorem splitKernelHaarRatio_apply (l : L) :
    letI : LocallyCompactSpace I := (isClosed_splitKernelIntersection r H hH).locallyCompactSpace
    (splitKernelHaarRatio r s H hsH hH l : ℝ≥0) =
      mulEquivHaarChar (subgroupAutomorphism I (α l) (hα l)) /
        mulEquivHaarChar (α l) := rfl

end Character

section Equivalence

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable [TopologicalSpace L] [LocallyCompactSpace G] [T2Space G]
variable (hrs : ∀ l, r (s l) = l) (hr : Continuous r) (hs : Continuous s)
variable (hH : IsClosed (H : Set G)) (σ : Representation ℂ H V) (hσ : IsSmooth σ)
variable [LocallyCompactSpace r.ker]
variable [MeasurableSpace r.ker] [BorelSpace r.ker]
variable [MeasurableSpace (H.comap r.ker.subtype)] [BorelSpace (H.comap r.ker.subtype)]
variable [MeasurableSpace (LeftQuotient (H.comap r.ker.subtype))]
variable [BorelSpace (LeftQuotient (H.comap r.ker.subtype))]
variable (ν : Measure (LeftQuotient (H.comap r.ker.subtype))) [IsFiniteMeasureOnCompacts ν]
variable (hBasis : ∀ O : Set r.ker, IsOpen O → (1 : r.ker) ∈ O →
  ∃ K : OpenSubgroup r.ker, IsCompact (K : Set r.ker) ∧ (K : Set r.ker) ⊆ O)
variable (μN : Measure r.ker) (μI : Measure (H.comap r.ker.subtype))
variable [IsHaarMeasure μN] [μN.Regular] [IsMulRightInvariant μN]
variable [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
variable (hCompatible : IsCompatible (H.comap r.ker.subtype) μN μI ν)

local notation "σI" => σ.comp (r.ker.subtype.subgroupComap H)
local notation "χ" => Jacquet.complexCharacter (splitKernelHaarRatio r s H hsH hH)

/-- The actual relative quotient integral as an equivariant equivalence, with
the exact positive Haar character twisting the coefficient quotient action. -/
def splitKernelCompactEquivariantEquiv :
    Representation.Equiv (((compactInduced H σ).toCoinvariants r.ker).comp s)
      (twist χ (splitKernelCoefficientAction r s H hsH σ)) where
  toLinearEquiv := splitKernelCompactCoinvariantEquiv r s hrs hr hs H hH hsH σ hσ
    ν hBasis μN μI hCompatible
  isIntertwining' l := by
    apply LinearMap.ext
    intro z
    let : LocallyCompactSpace I := (isClosed_splitKernelIntersection r H hH).locallyCompactSpace
    change splitKernelCompactCoinvariantDesc r s hrs hr hs H hH hsH σ hσ ν
        hCompatible.right_invariant ((compactInduced H σ).toCoinvariants r.ker (s l) z) =
      (χ l : ℂ) • splitKernelCoefficientAction r s H hsH σ l
        (splitKernelCompactCoinvariantDesc r s hrs hr hs H hH hsH σ hσ ν
          hCompatible.right_invariant z)
    rw [Jacquet.complexCharacter_apply, splitKernelHaarRatio_apply]
    exact splitKernelCompactCoinvariantDesc_section r s H hsH σ hrs hr hs hH hσ ν
      hCompatible l z

/-- The underlying linear equivalence is exactly the split-kernel integral equivalence. -/
theorem splitKernelCompactEquivariantEquiv_toLinearEquiv :
    (splitKernelCompactEquivariantEquiv r s H hsH hrs hr hs hH σ hσ ν hBasis μN μI
        hCompatible).toLinearEquiv =
      splitKernelCompactCoinvariantEquiv r s hrs hr hs H hH hsH σ hσ ν hBasis μN μI
        hCompatible := rfl

@[simp] theorem splitKernelCompactEquivariantEquiv_mk (f : CompactFunctions H σ) :
    splitKernelCompactEquivariantEquiv r s H hsH hrs hr hs hH σ hσ ν hBasis μN μI hCompatible
        (Representation.Coinvariants.mk ((compactInduced H σ).comp r.ker.subtype) f) =
      AlgebraicIntegral.integral ν (quotientCoinvariantSimple I σI
        (splitKernelCompactEquiv r s hrs hr hs H hH hsH σ hσ f)) := rfl

/-- The equivariant integral is natural for every smooth coefficient
intertwiner between modules in independent universes. -/
theorem splitKernelCompactEquivariantEquiv_natural
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {τ : Representation ℂ H W} (hτ : IsSmooth τ) (T : σ.IntertwiningMap τ)
    (z : Representation.Coinvariants ((compactInduced H σ).comp r.ker.subtype)) :
    splitKernelCompactEquivariantEquiv r s H hsH hrs hr hs hH τ hτ ν hBasis μN μI hCompatible
        (Representation.Coinvariants.map _ _
          (Jacquet.restrictMap (compactInducedMap H T) r.ker) z) =
      Representation.Coinvariants.map σI (τ.comp (r.ker.subtype.subgroupComap H))
        (splitKernelInducingMap r H T)
        (splitKernelCompactEquivariantEquiv r s H hsH hrs hr hs hH σ hσ ν
          hBasis μN μI hCompatible z) :=
  splitKernelCompactCoinvariantEquiv_natural r s hrs hr hs H hH hsH σ hσ ν
    hBasis μN μI hCompatible hτ T z

end Equivalence

end Langlands.Induction
