import Langlands.Representation.Derivative.Homogeneity
import Langlands.Representation.Induction.BinaryProduct
import Langlands.Representation.Mirabolic.MixedProducts

/-!
# Mixed products and the normalized mirabolic minus functors

Natural versions of the minus clauses of BZ77 Proposition 4.13(b,c), including
the two source-rank-one boundaries. The functors are the actual normalized
products and localized quotient functors. This module states the comparisons;
it does not prove them.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Derivative

open GeneralLinear HarmonicAnalysis

universe uF uV

namespace MirabolicProductMinus

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- `Φ⁻(ρ × τ)` for `ρ` on `GL_(k+1)` and `τ` on `P_(r+1)`.
The actual rank cast is `(k+1)+r = (k+r)+1`; the output is `P_(k+r+1)`. -/
def leftPhiProduct (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (k r : ℕ) :
    letI := T.topology
    (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier)) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (k + r) F.Carrier) :=
  letI := T.topology
  T.leftMixedProductFunctor (k + 1) r ⋙
    mirabolicRankCast T (Nat.succ_add k r) ⋙ Mirabolic.phiMinus T ψ (k + r)

/-- `Φ⁻(τ × ρ)` with the same ranks and actual source transport as above. -/
def rightPhiProduct (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (k r : ℕ) :
    letI := T.topology
    (SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier)) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (k + r) F.Carrier) :=
  letI := T.topology
  T.rightMixedProductFunctor (k + 1) r ⋙
    mirabolicRankCast T (Nat.succ_add k r) ⋙ Mirabolic.phiMinus T ψ (k + r)

/-- `ρ × Φ⁻τ` for `τ` on `P_(r+2)`, transported to `P_(k+r+2)`. -/
def leftPhiExpected (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (k r : ℕ) :
    letI := T.topology
    (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier)) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (k + r + 1) F.Carrier) :=
  letI := T.topology
  (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier))).prod
      (Mirabolic.phiMinus T ψ r) ⋙
    T.leftMixedProductFunctor (k + 1) r ⋙ mirabolicRankCast T (Nat.succ_add k r)

/-- `(Φ⁻τ) × ρ` for `τ` on `P_(r+2)`, the first term in BZ77 4.13(c).
The last rank cast identifies `(k+1)+r` with `k+r+1`. -/
def rightPhiSubobject (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (k r : ℕ) :
    letI := T.topology
    (SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier)) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (k + r + 1) F.Carrier) :=
  letI := T.topology
  (Mirabolic.phiMinus T ψ r).prod
      (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier))) ⋙
    T.rightMixedProductFunctor (k + 1) r ⋙ mirabolicRankCast T (Nat.succ_add k r)

/-- `(Ψ⁻τ) × (ρ restricted to P_(k+1))` for `τ` on `P_(r+1)`.
The left mixed product retains all of the `GL_r` input, including `r=0`;
the actual target transport is `r+k = k+r`. -/
def rightPhiQuotient (T : F.TopologicalData) (k r : ℕ) :
    letI := T.topology
    (SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier)) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (k + r) F.Carrier) :=
  letI := T.topology
  (Mirabolic.psiMinus T r).prod (generalLinearRestriction T k) ⋙
    T.leftMixedProductFunctor r k ⋙ mirabolicRankCast T (Nat.add_comm r k)

/-- The `Ψ⁻` clause of BZ77 4.13(b), naturally in both inputs, for all
positive GL ranks and all existing mirabolic ranks. -/
def LeftPsiCompatibility (F : PadicField.{uF} p) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ k r : ℕ, Nonempty
    (T.leftMixedProductFunctor.{uF, uV} (k + 1) r ⋙
        Mirabolic.psiMinus T ((k + 1) + r) ≅
      (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier))).prod
          (Mirabolic.psiMinus T r) ⋙ T.binaryNormalizedProductFunctor (k + 1) r)

/-- The `Φ⁻` clause of BZ77 4.13(b) when the source mirabolic rank is at
least two. Both sides are functors on the full product category. -/
def LeftPhiCompatibility (F : PadicField.{uF} p) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (k r : ℕ), Nonempty
    (leftPhiProduct.{uF, uV} T ψ k (r + 1) ≅ leftPhiExpected T ψ k r)

/-- The source `P_1` boundary of BZ77 4.13(b): the actual `Φ⁻` of
`ρ × τ` has zero carrier. No `Φ⁻` on `P_1` or group `P_0` is used. -/
def LeftPhiBoundary (F : PadicField.{uF} p) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (k : ℕ)
    (X : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (mirabolic 0 F.Carrier)),
    Subsingleton ((leftPhiProduct T ψ k 0).obj X)

/-- The `Ψ⁻` clause of BZ77 4.13(c), with the full binary product and actual
rank transport `r+(k+1) = (k+1)+r`, also when `r=0`. -/
def RightPsiCompatibility (F : PadicField.{uF} p) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ k r : ℕ, Nonempty
    (T.rightMixedProductFunctor.{uF, uV} (k + 1) r ⋙
        Mirabolic.psiMinus T ((k + 1) + r) ≅
      (Mirabolic.psiMinus T r).prod
          (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier))) ⋙
        T.binaryNormalizedProductFunctor r (k + 1) ⋙
          generalLinearRankCast T (Nat.add_comm r (k + 1)))

/-- The `Φ⁻` sequence of BZ77 4.13(c) for source `P_(r+2)`. The injection and
quotient are natural transformations, and their actual linear maps are short
exact at every pair of representations. -/
def RightPhiShortExact (F : PadicField.{uF} p) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (k r : ℕ),
    ∃ (i : rightPhiSubobject.{uF, uV} T ψ k r ⟶ rightPhiProduct T ψ k (r + 1))
      (q : rightPhiProduct.{uF, uV} T ψ k (r + 1) ⟶ rightPhiQuotient T k (r + 1)),
      ∀ X,
        Function.Injective (SmoothRep.hom (i.app X)) ∧
        LinearMap.range (SmoothRep.hom (i.app X)).toLinearMap =
          LinearMap.ker (SmoothRep.hom (q.app X)).toLinearMap ∧
        Function.Surjective (SmoothRep.hom (q.app X))

/-- The source `P_1` boundary of BZ77 4.13(c): the middle and last terms
are naturally isomorphic, with the entire `GL_0` carrier in the last term. -/
def RightPhiBoundary (F : PadicField.{uF} p) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (k : ℕ), Nonempty
    (rightPhiProduct.{uF, uV} T ψ k 0 ≅ rightPhiQuotient T k 0)

end MirabolicProductMinus

/-- BZ77 Proposition 4.13(b,c), restricted to the actual determinant-normalized
minus functors, including both `P_1` boundary clauses. This is a proposition
definition, with no theorem-valued premise and no assertion of its proof. -/
def MirabolicProductMinusCompatibilityStatement {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) : Prop :=
  MirabolicProductMinus.LeftPsiCompatibility.{uF, uV} F T ∧
  MirabolicProductMinus.LeftPhiCompatibility.{uF, uV} F T ∧
  MirabolicProductMinus.LeftPhiBoundary.{uF, uV} F T ∧
  MirabolicProductMinus.RightPsiCompatibility.{uF, uV} F T ∧
  MirabolicProductMinus.RightPhiShortExact.{uF, uV} F T ∧
  MirabolicProductMinus.RightPhiBoundary.{uF, uV} F T

end Langlands.Derivative
