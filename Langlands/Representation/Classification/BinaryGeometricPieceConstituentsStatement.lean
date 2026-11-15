import Langlands.Representation.Geometric.GeometricLemmaStatement
import Langlands.Representation.Classification.TwoSupercuspidalProductStructureStatement
import Langlands.Representation.Classification.SegmentHeadJacquetStatement
import Langlands.Representation.Classification.SingletonSegmentSocle
import Langlands.Representation.Induction.BinaryProduct
import Langlands.Representation.Exponents.WeylBranchPiecesStatement

/-!
# First-block constituents of the geometric pieces of a binary product

For the two-block source shape `(m₁, m₂)` and the two-block target shape `(a, b)`, every
irreducible representation of `GL_a` occurring in the first block of a geometric piece of
`r_(a,b)(Y₁ × Y₂)` comes from first-block Jacquet constituents of `Y₁` and `Y₂`, combined by a
normalized product. Only the identity piece can produce a constituent of `Y₁` alone.
Proposition only; nothing is proved here.
-/

noncomputable section

namespace Langlands.Classification.BinaryGeometricPieces

open CategoryTheory GeneralLinear Geometric

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- `ρ`, a representation of `GL_a`, is a first-block Jacquet constituent of `Y`, a
representation of `GL_m`: either `a = m` and `ρ` is a subquotient of `Y` (after the literal
rank transport), or `a + k = m` with `a, k > 0` and `ρ` is a subquotient of the restriction to
the first block `GL_a` of the normalized Jacquet module of `Y` along `(a, k)`. -/
def IsFirstBlockConstituent {m a : ℕ}
    (Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier))
    (ρ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)) :
    Prop :=
  letI := T.topology
  (∃ h : m = a, WeylBranchPieces.IsSubquotient (T.castRank h Y).representation
      ρ.representation) ∨
  (∃ (k : ℕ) (ha : 0 < a) (hk : 0 < k) (h : a + k = m),
      WeylBranchPieces.IsSubquotient
        ((T.normalizedJacquet (BlockShape.ofPair a k ha hk h) Y.representation).comp
          (MonoidHom.mulSingle
            (fun i => GeneralLinear ((BlockShape.ofPair a k ha hk h).size i) F.Carrier)
            (0 : Fin 2)))
        ρ.representation)

/-- The mixed alternative: `a = a₁ + a₂` with `a₁, a₂ > 0`, and `ρ` is a subquotient of the
normalized product `ρ₁ × ρ₂` of irreducible first-block Jacquet constituents `ρ₁` of `Y₁` and
`ρ₂` of `Y₂`. -/
def IsMixedConstituent {m₁ m₂ a : ℕ}
    (Y₁ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m₁ F.Carrier))
    (Y₂ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m₂ F.Carrier))
    (ρ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)) :
    Prop :=
  letI := T.topology
  ∃ (a₁ a₂ : ℕ) (_ : 0 < a₁) (_ : 0 < a₂) (h : a₁ + a₂ = a)
    (ρ₁ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a₁ F.Carrier))
    (ρ₂ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a₂ F.Carrier)),
    ρ₁.IsIrreducible ∧ ρ₂.IsIrreducible ∧
    IsFirstBlockConstituent F T Y₁ ρ₁ ∧ IsFirstBlockConstituent F T Y₂ ρ₂ ∧
    SmoothRep.IsSubquotient ρ (T.castRank h ((T.binaryNormalizedProductFunctor a₁ a₂).obj (ρ₁, ρ₂)))

/-- **Statement.** Let `0 < m₁, m₂, a, b` with `a + b = m₁ + m₂`, let `B = (m₁, m₂)` and
`C = (a, b)`, and let `w` be a minimal representative with the intersection refinements `S`
of `B` and `R` of `C`. Let `Y₁`, `Y₂` be finite-length representations of `GL_{m₁}` and
`GL_{m₂}`, and let `ρ` be an irreducible representation of `GL_a` which is a subquotient of the
restriction to the first block `GL_a` of the geometric piece of index `w`, applied to
`Y₁ ⊗ Y₂`. Then either `w` is the identity and `ρ` is a first-block Jacquet constituent of
`Y₁`, or `ρ` is a first-block Jacquet constituent of `Y₂`, or `ρ` is a mixed constituent. -/
def BinaryGeometricPieceConstituents : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (m₁ m₂ : ℕ) (h₁ : 0 < m₁) (h₂ : 0 < m₂) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
      (h : a + b = m₁ + m₂)
      (w : MinimalRepresentatives (BlockShape.ofPair m₁ m₂ h₁ h₂ rfl)
        (BlockShape.ofPair a b ha hb h))
      (S : BlockRefinement (BlockShape.ofPair m₁ m₂ h₁ h₂ rfl))
      (R : BlockRefinement (BlockShape.ofPair a b ha hb h))
      (hS : IsIntersectionRefinement (F := F.Carrier) (BlockShape.ofPair m₁ m₂ h₁ h₂ rfl)
        (BlockShape.ofPair a b ha hb h) w.val S)
      (hR : IsIntersectionRefinement (F := F.Carrier) (BlockShape.ofPair a b ha hb h)
        (BlockShape.ofPair m₁ m₂ h₁ h₂ rfl) w.val⁻¹ R)
      (Y₁ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m₁ F.Carrier))
      (Y₂ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m₂ F.Carrier))
      (ρ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)),
      Y₁.HasFiniteLength → Y₂.HasFiniteLength → ρ.IsIrreducible →
      WeylBranchPieces.IsSubquotient
        (((geometricPieceFunctor.{uF, max uF uV} T (BlockShape.ofPair m₁ m₂ h₁ h₂ rfl)
            (BlockShape.ofPair a b ha hb h) w.val S R hS.2.1 hR.2.1).obj
            (FiniteTensor.externalSmoothObject (twoBlockFactors h₁ h₂ Y₁ Y₂))).ρ.comp
          (MonoidHom.mulSingle
            (fun i => GeneralLinear ((BlockShape.ofPair a b ha hb h).size i) F.Carrier)
            (0 : Fin 2)))
        ρ.representation →
      (w.val = 1 ∧ IsFirstBlockConstituent F T Y₁ ρ) ∨ IsFirstBlockConstituent F T Y₂ ρ ∨
        IsMixedConstituent F T Y₁ Y₂ ρ

end Langlands.Classification.BinaryGeometricPieces
