import Langlands.Representation.Induction.CoefficientSplitKernelIntegral
import Langlands.Representation.Induction.SplitKernelEquivariant

/-! The native equivariant split-kernel integral with its exact Haar character. -/

noncomputable section

namespace Langlands.Induction.Coefficient

open MeasureTheory MeasureTheory.Measure
open QuotientIntegration HarmonicAnalysis
open scoped NNReal ENNReal

universe uR uG uL uV uW

variable {R : Type uR} [CommRing R]

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {L : Type uL} [Group L]
variable {V : Type uV} [AddCommGroup V] [Module R V]

variable (r : G →* L) (s : L →* G) (H : Subgroup G) (hsH : ∀ l, s l ∈ H)

variable (σ : Representation R H V)

local notation "I" => H.comap r.ker.subtype
local notation "σI" => σ.comp (r.ker.subtype.subgroupComap H)
local notation "α" => splitKernelConjugation r s
local notation "hα" => splitKernelConjugation_mem r s H hsH
local notation "a" => splitKernelSection s H hsH

/-- The section's coefficient operator intertwines the inverse-conjugated
intersection action with the original action. -/
def splitKernelCoefficientMap (l : L) :
    (automorphismInducing I (α l) (hα l) σI).IntertwiningMap σI where
  toLinearMap := σ (a l)
  isIntertwining' i := by
    apply LinearMap.ext
    intro v
    change σ (a l)
        (σ (r.ker.subtype.subgroupComap H (subgroupAutomorphism I (α l) (hα l) i)) v) =
      σ (r.ker.subtype.subgroupComap H i) (σ (a l) v)
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 1
    congr 1
    apply Subtype.ext
    change s l * (splitKernelConjugation r s l (i : r.ker) : G) =
      ((i : r.ker) : G) * s l
    rw [splitKernelConjugation_apply]
    simp only [mul_assoc, mul_inv_cancel_left]

/-- The actual linear operator on inducing coinvariants, using the canonical
identity-on-vectors transport and the section's coefficient intertwiner. -/
def splitKernelCoefficientLinearMap (l : L) :
    Representation.Coinvariants σI →ₗ[R] Representation.Coinvariants σI :=
  (Representation.Coinvariants.map _ _ (splitKernelCoefficientMap r s H hsH σ l)).comp
    (automorphismCoinvariantsEquiv I (α l) (hα l) σI).symm.toLinearMap

@[simp] theorem splitKernelCoefficientLinearMap_mk (l : L) (v : V) :
    splitKernelCoefficientLinearMap r s H hsH σ l (Representation.Coinvariants.mk σI v) =
      Representation.Coinvariants.mk σI (σ (a l) v) := rfl

/-- The actual section action on the actual inducing coinvariants. -/
def splitKernelCoefficientAction : Representation R L (Representation.Coinvariants σI) where
  toFun := splitKernelCoefficientLinearMap r s H hsH σ
  map_one' := by
    apply LinearMap.ext
    intro z
    obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective σI z
    change splitKernelCoefficientLinearMap r s H hsH σ 1
      (Representation.Coinvariants.mk σI v) = Representation.Coinvariants.mk σI v
    simp only [splitKernelCoefficientLinearMap_mk, map_one, Module.End.one_apply]
  map_mul' l k := by
    apply LinearMap.ext
    intro z
    obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective σI z
    change splitKernelCoefficientLinearMap r s H hsH σ (l * k)
      (Representation.Coinvariants.mk σI v) =
        splitKernelCoefficientLinearMap r s H hsH σ l
          (splitKernelCoefficientLinearMap r s H hsH σ k (Representation.Coinvariants.mk σI v))
    simp only [splitKernelCoefficientLinearMap_mk, map_mul, Module.End.mul_apply]

@[simp] theorem splitKernelCoefficientAction_mk (l : L) (v : V) :
    splitKernelCoefficientAction r s H hsH σ l (Representation.Coinvariants.mk σI v) =
      Representation.Coinvariants.mk σI (σ (a l) v) := rfl

/-- Every coefficient intertwiner commutes with the actual descended action. -/
theorem splitKernelCoefficientAction_natural
    {W : Type uW} [AddCommGroup W] [Module R W]
    {τ : Representation R H W} (T : σ.IntertwiningMap τ)
    (l : L) (z : Representation.Coinvariants σI) :
    Representation.Coinvariants.map σI (τ.comp (r.ker.subtype.subgroupComap H))
        (splitKernelInducingMap r H T) (splitKernelCoefficientAction r s H hsH σ l z) =
      splitKernelCoefficientAction r s H hsH τ l
        (Representation.Coinvariants.map σI (τ.comp (r.ker.subtype.subgroupComap H))
          (splitKernelInducingMap r H T) z) := by
  obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective σI z
  change Representation.Coinvariants.mk (τ.comp (r.ker.subtype.subgroupComap H))
    (T (σ (a l) v)) =
      Representation.Coinvariants.mk (τ.comp (r.ker.subtype.subgroupComap H)) (τ (a l) (T v))
  exact congrArg (Representation.Coinvariants.mk _) (Representation.IntertwiningMap.isIntertwining
    σ τ T (a l) v)

section Functions

variable [TopologicalSpace L] [LocallyCompactSpace G]
variable (hrs : ∀ l, r (s l) = l) (hr : Continuous r) (hs : Continuous s)
variable (hH : IsClosed (H : Set G)) (hσ : IsSmooth σ)

local notation "E" => splitKernelCompactEquiv r s hrs hr hs H hH hsH σ hσ

/-- Restricting the section translate is inverse-conjugation precomposition
followed by the actual section coefficient map. -/
theorem splitKernelCompactEquiv_section (l : L) (f : CompactFunctions H σ) :
    E (compactInduced H σ (s l) f) =
      compactInducedMap I (splitKernelCoefficientMap r s H hsH σ l)
        (precomposeCompactInducedEquiv I (α l) (hα l) σI (E f)) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext n
  change f.1.1.1 ((n : G) * s l) =
    σ (a l) (f.1.1.1 (splitKernelConjugation r s l n : G))
  rw [← f.1.1.property]
  change f.1.1.1 ((n : G) * s l) =
    f.1.1.1 (s l * (splitKernelConjugation r s l n : G))
  rw [splitKernelConjugation_apply]
  simp only [mul_assoc, mul_inv_cancel_left]

/-- The pointwise form: the restricted section translate at `n` is the section
coefficient applied to the restriction of `f` at the inverse conjugate of `n`. -/
theorem splitKernelCompactEquiv_section_eval (l : L) (f : CompactFunctions H σ)
    (n : r.ker) :
    eval I σI (E (compactInduced H σ (s l) f)).1 n =
      σ (a l) (eval I σI (E f).1 (α l n)) := by
  rw [splitKernelCompactEquiv_section r s H hsH σ hrs hr hs hH hσ l f]
  rfl

section Integral

variable [Algebra ℂ R] [Module ℂ V] [IsScalarTower ℂ R V]

variable [T2Space G] [LocallyCompactSpace r.ker]
variable [MeasurableSpace r.ker] [BorelSpace r.ker]
variable [MeasurableSpace (H.comap r.ker.subtype)] [BorelSpace (H.comap r.ker.subtype)]

variable {μN : Measure r.ker} {μI : Measure (H.comap r.ker.subtype)}
variable [IsHaarMeasure μN] [μN.Regular]
variable [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
variable [MeasurableSpace (LeftQuotient (H.comap r.ker.subtype))]
variable [BorelSpace (LeftQuotient (H.comap r.ker.subtype))]
variable (ν : Measure (LeftQuotient (H.comap r.ker.subtype))) [IsFiniteMeasureOnCompacts ν]
variable (hCompatible : IsCompatible (H.comap r.ker.subtype) μN μI ν)

local notation "c" l:max => (algebraMap ℂ R ((((mulEquivHaarChar (subgroupAutomorphism I (α l) (hα l)) /
  mulEquivHaarChar (α l) : ℝ≥0) : ℝ) : ℂ)))

include hCompatible in
/-- Section translation on the actual relative integral has precisely the
subgroup-to-kernel Haar ratio for forward inverse-conjugation precomposition. -/
theorem splitKernelCompactIntegral_section (l : L) (f : CompactFunctions H σ) :
    letI : LocallyCompactSpace I := (isClosed_splitKernelIntersection r H hH).locallyCompactSpace
    splitKernelCompactIntegral r s hrs hr hs H hH hsH σ hσ ν
        (compactInduced H σ (s l) f) =
      c l • splitKernelCoefficientAction r s H hsH σ l
        (splitKernelCompactIntegral r s hrs hr hs H hH hsH σ hσ ν f) := by
  let : LocallyCompactSpace I := (isClosed_splitKernelIntersection r H hH).locallyCompactSpace
  change compactCoinvariantIntegral I σI ν (E (compactInduced H σ (s l) f)) = _
  rw [splitKernelCompactEquiv_section r s H hsH σ hrs hr hs hH hσ l f]
  rw [compactCoinvariantIntegral_natural]
  let A := automorphismCoinvariantsEquiv I (α l) (hα l) σI
  let T := splitKernelCoefficientMap r s H hsH σ l
  let z := compactCoinvariantIntegral I (automorphismInducing I (α l) (hα l) σI) ν
    (precomposeCompactInducedEquiv I (α l) (hα l) σI (E f))
  have hc : A z = c l • compactCoinvariantIntegral I σI ν (E f) := by
    simpa only [algebraMap_smul] using
      (compactCoinvariantIntegral_automorphism I (isClosed_splitKernelIntersection r H hH)
        ν hCompatible (α l) (hα l) σI (E f))
  change Representation.Coinvariants.map _ _ T z = _
  calc
    Representation.Coinvariants.map _ _ T z =
        splitKernelCoefficientLinearMap r s H hsH σ l (A z) := by
      change Representation.Coinvariants.map _ _ T z =
        Representation.Coinvariants.map _ _ T (A.symm (A z))
      rw [A.symm_apply_apply]
    _ = _ := by
      rw [hc, map_smul]
      rfl

include hCompatible in
/-- The same formula holds on the actual kernel coinvariants, with the
actual full-group quotient action evaluated at the section value. -/
theorem splitKernelCompactCoinvariantDesc_section (l : L)
    (z : Representation.Coinvariants ((compactInduced H σ).comp r.ker.subtype)) :
    letI : LocallyCompactSpace I := (isClosed_splitKernelIntersection r H hH).locallyCompactSpace
    splitKernelCompactCoinvariantDesc r s hrs hr hs H hH hsH σ hσ ν
        hCompatible.right_invariant ((compactInduced H σ).toCoinvariants r.ker (s l) z) =
      c l • splitKernelCoefficientAction r s H hsH σ l
        (splitKernelCompactCoinvariantDesc r s hrs hr hs H hH hsH σ hσ ν
          hCompatible.right_invariant z) := by
  let : LocallyCompactSpace I := (isClosed_splitKernelIntersection r H hH).locallyCompactSpace
  obtain ⟨f, rfl⟩ := Representation.Coinvariants.mk_surjective _ z
  exact splitKernelCompactIntegral_section r s H hsH σ hrs hr hs hH hσ ν hCompatible l f

end Integral

end Functions

section Equivalence

variable [Algebra ℂ R] [Module ℂ V] [IsScalarTower ℂ R V]
variable [TopologicalSpace L] [LocallyCompactSpace G] [T2Space G]
variable (hrs : ∀ l, r (s l) = l) (hr : Continuous r) (hs : Continuous s)
variable (hH : IsClosed (H : Set G)) (hσ : IsSmooth σ)
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

local notation "χR" =>
  MonoidHom.comp (Units.map (RingHom.toMonoidHom (algebraMap ℂ R)))
    (Jacquet.complexCharacter (splitKernelHaarRatio r s H hsH hH))

/-- The actual relative integral is a native coefficient equivariant
equivalence with the exact Haar character embedded in the coefficient algebra. -/
def splitKernelCompactEquivariantEquiv :
    Representation.Equiv (((compactInduced H σ).toCoinvariants r.ker).comp s)
      (twist χR (splitKernelCoefficientAction r s H hsH σ)) where
  toLinearEquiv := splitKernelCompactCoinvariantEquiv r s hrs hr hs H hH hsH σ hσ
    ν hBasis μN μI hCompatible
  isIntertwining' l := by
    apply LinearMap.ext
    intro z
    let : LocallyCompactSpace I := (isClosed_splitKernelIntersection r H hH).locallyCompactSpace
    change splitKernelCompactCoinvariantDesc r s hrs hr hs H hH hsH σ hσ ν
        hCompatible.right_invariant ((compactInduced H σ).toCoinvariants r.ker (s l) z) =
      algebraMap ℂ R
        (Jacquet.complexCharacter (splitKernelHaarRatio r s H hsH hH) l : ℂ) •
          splitKernelCoefficientAction r s H hsH σ l
            (splitKernelCompactCoinvariantDesc r s hrs hr hs H hH hsH σ hσ ν
              hCompatible.right_invariant z)
    rw [Jacquet.complexCharacter_apply, splitKernelHaarRatio_apply]
    exact splitKernelCompactCoinvariantDesc_section r s H hsH σ hrs hr hs hH hσ ν
      hCompatible l z

/-- The underlying equivalence is the actual native relative quotient integral. -/
theorem splitKernelCompactEquivariantEquiv_toLinearEquiv :
    (splitKernelCompactEquivariantEquiv r s H hsH σ hrs hr hs hH hσ ν hBasis μN μI
        hCompatible).toLinearEquiv =
      splitKernelCompactCoinvariantEquiv r s hrs hr hs H hH hsH σ hσ ν hBasis μN μI
        hCompatible := rfl

@[simp] theorem splitKernelCompactEquivariantEquiv_mk (f : CompactFunctions H σ) :
    splitKernelCompactEquivariantEquiv r s H hsH σ hrs hr hs hH hσ ν hBasis μN μI
        hCompatible
        (Representation.Coinvariants.mk ((compactInduced H σ).comp r.ker.subtype) f) =
      fullCoinvariantsComplexEquiv σI
        (AlgebraicIntegral.integral ν (quotientCoinvariantSimple I
          (Jacquet.CoefficientRestriction.complexRepresentation σI)
          (compactFunctionsComplexEquiv I σI
            (splitKernelCompactEquiv r s hrs hr hs H hH hsH σ hσ f)))) := rfl

/-- The equivariant native integral commutes with every coefficient
intertwiner, retaining independent coefficient carrier universes. -/
theorem splitKernelCompactEquivariantEquiv_natural
    {W : Type uW} [AddCommGroup W] [Module R W] [Module ℂ W] [IsScalarTower ℂ R W]
    {τ : Representation R H W} (hτ : IsSmooth τ) (T : σ.IntertwiningMap τ)
    (z : Representation.Coinvariants ((compactInduced H σ).comp r.ker.subtype)) :
    splitKernelCompactEquivariantEquiv r s H hsH τ hrs hr hs hH hτ ν hBasis μN μI
        hCompatible
        (Representation.Coinvariants.map _ _
          (Jacquet.restrictMap (compactInducedMap H T) r.ker) z) =
      Representation.Coinvariants.map σI (τ.comp (r.ker.subtype.subgroupComap H))
        (splitKernelInducingMap r H T)
        (splitKernelCompactEquivariantEquiv r s H hsH σ hrs hr hs hH hσ ν
          hBasis μN μI hCompatible z) :=
  splitKernelCompactCoinvariantEquiv_natural r s hrs hr hs H hH hsH σ hσ ν
    hBasis μN μI hCompatible hτ T z

end Equivalence

end Langlands.Induction.Coefficient
