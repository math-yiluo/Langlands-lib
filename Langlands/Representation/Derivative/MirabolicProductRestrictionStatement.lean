import Langlands.Representation.Derivative.Homogeneity
import Langlands.Representation.Induction.BinaryProduct
import Langlands.Representation.Mirabolic.MixedProducts

/-!
# Restriction of a binary product to the mirabolic subgroup

The natural short exact sequence of BZ77 Proposition 4.13(a), for all positive
ranks `a = m + 1` and `b = n + 1`:
`0 → (A|P_a) × B → (A × B)|P_(a+b) → A × (B|P_b) → 0`.
The three terms are composites of the actual binary and mixed products,
restrictions and rank transports. This module states the sequence; it does not
prove it.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Derivative

open GeneralLinear HarmonicAnalysis

universe uF uV

namespace MirabolicProductRestriction

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- `(A × B)|P_(a+b)` for `A` on `GL_(m+1)` and `B` on `GL_(n+1)`: the binary
normalized product, the actual rank cast `(m+1)+(n+1) = (m+n+1)+1`, and
restriction to `P_(m+n+2)`. -/
def restrictedProduct (T : F.TopologicalData) (m n : ℕ) :
    letI := T.topology
    (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + 1) F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier)) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (m + n + 1) F.Carrier) :=
  letI := T.topology
  T.binaryNormalizedProductFunctor (m + 1) (n + 1) ⋙
    generalLinearRankCast T (show (m + 1) + (n + 1) = (m + n + 1) + 1 by omega) ⋙
      generalLinearRestriction T (m + n + 1)

/-- `(A|P_a) × B`, the first term: restriction of the first input to
`P_(m+1)`, the right mixed product of case (III) with ranks `n+1, m`, and the
actual rank cast `(n+1)+m = m+n+1`. -/
def restrictionSubobject (T : F.TopologicalData) (m n : ℕ) :
    letI := T.topology
    (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + 1) F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier)) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (m + n + 1) F.Carrier) :=
  letI := T.topology
  (generalLinearRestriction T m).prod
      (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier))) ⋙
    T.rightMixedProductFunctor (n + 1) m ⋙
      mirabolicRankCast T (show (n + 1) + m = m + n + 1 by omega)

/-- `A × (B|P_b)`, the last term: restriction of the second input to
`P_(n+1)`, the left mixed product of case (II) with ranks `m+1, n`, and the
actual rank cast `(m+1)+n = m+n+1`. -/
def restrictionQuotient (T : F.TopologicalData) (m n : ℕ) :
    letI := T.topology
    (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + 1) F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier)) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (m + n + 1) F.Carrier) :=
  letI := T.topology
  (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + 1) F.Carrier))).prod
      (generalLinearRestriction T n) ⋙
    T.leftMixedProductFunctor (m + 1) n ⋙
      mirabolicRankCast T (show (m + 1) + n = m + n + 1 by omega)

end MirabolicProductRestriction

open MirabolicProductRestriction in
/-- BZ77 Proposition 4.13(a) for all positive ranks `a = m+1`, `b = n+1`:
natural transformations `i` and `q` whose actual component intertwiners form a
short exact sequence `0 → (A|P_a) × B → (A × B)|P_(a+b) → A × (B|P_b) → 0` at
every pair `(A, B)`. This is a proposition definition, with no theorem-valued
premise and no assertion of its proof. -/
def MirabolicProductRestrictionStatement {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ m n : ℕ,
    ∃ (i : restrictionSubobject.{uF, uV} T m n ⟶ restrictedProduct T m n)
      (q : restrictedProduct.{uF, uV} T m n ⟶ restrictionQuotient T m n),
      ∀ X,
        Function.Injective (SmoothRep.hom (i.app X)) ∧
        LinearMap.range (SmoothRep.hom (i.app X)).toLinearMap =
          LinearMap.ker (SmoothRep.hom (q.app X)).toLinearMap ∧
        Function.Surjective (SmoothRep.hom (q.app X))

end Langlands.Derivative
