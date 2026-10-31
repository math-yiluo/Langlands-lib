import Langlands.Geometry.Analytic.StrictTestDomain.BinaryLaurentDiagramComparisonStatement
import Langlands.Geometry.Analytic.StrictTestDomain.RationalPullbackProof

/-! # Elementary compatibility for the binary Laurent comparison -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTestDomain

open RationalData

variable (K : Type u) [NormedField K] [IsUltrametricDist K]

/-- Equal denominator and numerator data give the identity equivalence after
equality elimination, on the actual relative rational quotients. -/
def relativeRationalEquivOfEq (A : PresentedAffinoidAlgebra K) (m : ℕ)
    {g h : A} {n k : Fin m → A} (hg : g = h) (hn : n = k) :
    BoundedAlgEquiv K
      (PresentedAffinoidAlgebra.RelativeRationalPresentation.Algebra K A
        (PositivePolyradius.unit (Fin m)) g n)
      (PresentedAffinoidAlgebra.RelativeRationalPresentation.Algebra K A
        (PositivePolyradius.unit (Fin m)) h k) := by
  subst h k
  exact BoundedAlgEquiv.refl K _

/-- Equality transport preserves the actual coefficient classes. -/
@[simp] theorem relativeRationalEquivOfEq_baseMap
    (A : PresentedAffinoidAlgebra K) (m : ℕ)
    {g h : A} {n k : Fin m → A} (hg : g = h) (hn : n = k) (a : A) :
    relativeRationalEquivOfEq K A m hg hn
      (PresentedAffinoidAlgebra.RelativeRationalPresentation.baseMap K A
        (PositivePolyradius.unit (Fin m)) g n a) =
      PresentedAffinoidAlgebra.RelativeRationalPresentation.baseMap K A
        (PositivePolyradius.unit (Fin m)) h k a := by
  subst h k
  rfl

/-- Equality transport preserves the actual fraction coordinates. -/
@[simp] theorem relativeRationalEquivOfEq_fraction
    (A : PresentedAffinoidAlgebra K) (m : ℕ)
    {g h : A} {n k : Fin m → A} (hg : g = h) (hn : n = k) (j : Fin m) :
    relativeRationalEquivOfEq K A m hg hn
      (PresentedAffinoidAlgebra.RelativeRationalPresentation.fraction K A
        (PositivePolyradius.unit (Fin m)) g n j) =
      PresentedAffinoidAlgebra.RelativeRationalPresentation.fraction K A
        (PositivePolyradius.unit (Fin m)) h k j := by
  subst h k
  rfl

variable [CompleteSpace K] (P : PresentedStrictAffinoidAlgebra K) (f : P)

/-- The actual strict intersection has four fraction variables. -/
@[simp] theorem laurent_inter_arity :
    ((laurentUpper f).inter (laurentLower f)).arity = 4 := rfl

/-- Its product denominator is `f`. -/
@[simp] theorem laurent_inter_denominator :
    ((laurentUpper f).inter (laurentLower f)).denominator = f := by
  change 1 * f = f
  exact one_mul f

/-- The numerator order is the actual `finProdFinEquiv` order. -/
theorem laurent_inter_numerator :
    ((laurentUpper f).inter (laurentLower f)).numerator = ![f, 1, f ^ 2, f] := by
  funext j
  fin_cases j <;>
    simp [inter, laurentUpper, laurentLower, RationalIntersection.numerators,
      finProdFinEquiv, Fin.divNat, Fin.modNat, pow_two]

/-- Transporting the actual strict intersection numerators through the inverse
base comparison gives the displayed relative product tuple. -/
theorem laurent_inter_numerator_strictEquiv :
    (fun j => (PresentedAffinoidAlgebra.strictEquiv K P).symm
      (((laurentUpper f).inter (laurentLower f)).numerator j)) =
      ![(PresentedAffinoidAlgebra.strictEquiv K P).symm f, 1,
        ((PresentedAffinoidAlgebra.strictEquiv K P).symm f) ^ 2,
        (PresentedAffinoidAlgebra.strictEquiv K P).symm f] := by
  rw [laurent_inter_numerator]
  change (fun j => (PresentedAffinoidAlgebra.strictEquiv K P).symm.toAlgEquiv
    (![f, 1, f ^ 2, f] j)) = _
  funext j
  fin_cases j <;> simp

/-- Any two bounded upper/overlap comparison maps compatible with coefficients
also commute with the actual left restriction. -/
theorem binaryLaurent_left_square
    (a : BoundedAlgHom K (laurentUpper f).algebra
      (PresentedAffinoidAlgebra.BinaryLaurent.Upper K
        (PresentedAffinoidAlgebra.ofStrict K P)
        ((PresentedAffinoidAlgebra.strictEquiv K P).symm f)))
    (b : BoundedAlgHom K ((laurentUpper f).inter (laurentLower f)).algebra
      (PresentedAffinoidAlgebra.BinaryLaurent.Overlap K
        (PresentedAffinoidAlgebra.ofStrict K P)
        ((PresentedAffinoidAlgebra.strictEquiv K P).symm f)))
    (ha : ∀ p : P, a ((laurentUpper f).baseMap p) =
      PresentedAffinoidAlgebra.BinaryLaurent.upperBase K
        (PresentedAffinoidAlgebra.ofStrict K P)
        ((PresentedAffinoidAlgebra.strictEquiv K P).symm f)
        ((PresentedAffinoidAlgebra.strictEquiv K P).symm p))
    (hb : ∀ p : P, b (((laurentUpper f).inter (laurentLower f)).baseMap p) =
      PresentedAffinoidAlgebra.BinaryLaurent.overlapBase K
        (PresentedAffinoidAlgebra.ofStrict K P)
        ((PresentedAffinoidAlgebra.strictEquiv K P).symm f)
        ((PresentedAffinoidAlgebra.strictEquiv K P).symm p)) :
    b.comp (interLeft (laurentUpper f) (laurentLower f)).restriction =
      (PresentedAffinoidAlgebra.BinaryLaurent.left K
        (PresentedAffinoidAlgebra.ofStrict K P)
        ((PresentedAffinoidAlgebra.strictEquiv K P).symm f)).comp a := by
  apply (laurentUpper f).hom_ext
  apply BoundedAlgHom.ext
  intro p
  have hr := congrArg (fun φ : BoundedAlgHom K P
      ((laurentUpper f).inter (laurentLower f)).algebra => φ p)
    (interLeft (laurentUpper f) (laurentLower f)).restriction_comp_baseMap
  change b ((interLeft (laurentUpper f) (laurentLower f)).restriction
      ((laurentUpper f).baseMap p)) =
    PresentedAffinoidAlgebra.BinaryLaurent.left K
      (PresentedAffinoidAlgebra.ofStrict K P)
      ((PresentedAffinoidAlgebra.strictEquiv K P).symm f)
      (a ((laurentUpper f).baseMap p))
  rw [show (interLeft (laurentUpper f) (laurentLower f)).restriction
      ((laurentUpper f).baseMap p) =
      ((laurentUpper f).inter (laurentLower f)).baseMap p from hr,
    hb, ha, PresentedAffinoidAlgebra.BinaryLaurent.left_upperBase]

/-- Any two bounded lower/overlap comparison maps compatible with coefficients
also commute with the actual right restriction. -/
theorem binaryLaurent_right_square
    (a : BoundedAlgHom K (laurentLower f).algebra
      (PresentedAffinoidAlgebra.BinaryLaurent.Lower K
        (PresentedAffinoidAlgebra.ofStrict K P)
        ((PresentedAffinoidAlgebra.strictEquiv K P).symm f)))
    (b : BoundedAlgHom K ((laurentUpper f).inter (laurentLower f)).algebra
      (PresentedAffinoidAlgebra.BinaryLaurent.Overlap K
        (PresentedAffinoidAlgebra.ofStrict K P)
        ((PresentedAffinoidAlgebra.strictEquiv K P).symm f)))
    (ha : ∀ p : P, a ((laurentLower f).baseMap p) =
      PresentedAffinoidAlgebra.BinaryLaurent.lowerBase K
        (PresentedAffinoidAlgebra.ofStrict K P)
        ((PresentedAffinoidAlgebra.strictEquiv K P).symm f)
        ((PresentedAffinoidAlgebra.strictEquiv K P).symm p))
    (hb : ∀ p : P, b (((laurentUpper f).inter (laurentLower f)).baseMap p) =
      PresentedAffinoidAlgebra.BinaryLaurent.overlapBase K
        (PresentedAffinoidAlgebra.ofStrict K P)
        ((PresentedAffinoidAlgebra.strictEquiv K P).symm f)
        ((PresentedAffinoidAlgebra.strictEquiv K P).symm p)) :
    b.comp (interRight (laurentUpper f) (laurentLower f)).restriction =
      (PresentedAffinoidAlgebra.BinaryLaurent.right K
        (PresentedAffinoidAlgebra.ofStrict K P)
        ((PresentedAffinoidAlgebra.strictEquiv K P).symm f)).comp a := by
  apply (laurentLower f).hom_ext
  apply BoundedAlgHom.ext
  intro p
  have hr := congrArg (fun φ : BoundedAlgHom K P
      ((laurentUpper f).inter (laurentLower f)).algebra => φ p)
    (interRight (laurentUpper f) (laurentLower f)).restriction_comp_baseMap
  change b ((interRight (laurentUpper f) (laurentLower f)).restriction
      ((laurentLower f).baseMap p)) =
    PresentedAffinoidAlgebra.BinaryLaurent.right K
      (PresentedAffinoidAlgebra.ofStrict K P)
      ((PresentedAffinoidAlgebra.strictEquiv K P).symm f)
      (a ((laurentLower f).baseMap p))
  rw [show (interRight (laurentUpper f) (laurentLower f)).restriction
      ((laurentLower f).baseMap p) =
      ((laurentUpper f).inter (laurentLower f)).baseMap p from hr,
    hb, ha, PresentedAffinoidAlgebra.BinaryLaurent.right_lowerBase]

end Langlands.Analytic.StrictTestDomain
