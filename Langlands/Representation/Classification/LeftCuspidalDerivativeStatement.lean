import Langlands.Representation.Classification.SingletonSegmentSocle
import Langlands.Representation.Induction.BinaryProduct

/-!
# The highest left cuspidal derivative lemma for `GL_n`: proposition target

Iterated products with an actual supercuspidal representation, left reducedness, and one
unproved proposition collecting closure under products, a comparison derived from the highest
derivative lemma, its uniqueness consequence, and reducedness of segment heads and socles.
-/

noncomputable section

namespace Langlands.Classification.LeftCuspidalDerivative

open CategoryTheory PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The rank `d * K + m` of `A^K × Y`, computed by peeling off one factor of rank `d` at a
time (`powerRank_eq`). -/
def powerRank (d : ℕ) : ℕ → ℕ → ℕ
  | 0, m => m
  | K + 1, m => d + powerRank d K m

theorem powerRank_eq (d K m : ℕ) : powerRank d K m = d * K + m := by
  induction K with
  | zero => simp [powerRank]
  | succ K ih => rw [powerRank, ih, Nat.mul_succ]; omega

/-- `A^K × Y = A × (A × ⋯ × (A × Y))`, with `K` factors equal to the actual supercuspidal
representation `A` of `GL_d(F)`, each step the published binary normalized product; a
representation of `GL_(powerRank d K m)(F)` for `Y` on `GL_m(F)`. -/
def powerProduct {d : ℕ}
    (A : letI := T.topology; GeneralLinear.SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := d)) :
    (K : ℕ) → {m : ℕ} →
      (letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)) →
      (letI := T.topology;
        SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (powerRank d K m) F.Carrier))
  | 0, _, Y => Y
  | K + 1, m, Y =>
    letI := T.topology
    (T.binaryNormalizedProductFunctor d (powerRank d K m)).obj (A.obj, powerProduct A K Y)

/-- `Y` is left `A`-reduced: no irreducible subquotient of `Y` embeds into a normalized
product `A × σ` (after the literal rank transport `d + k = m`). -/
def LeftReduced {d : ℕ}
    (A : letI := T.topology; GeneralLinear.SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := d))
    {m : ℕ} (Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)) :
    Prop :=
  letI := T.topology
  ∀ (Z : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)), Z.IsIrreducible →
    SmoothRep.IsSubquotient Z Y →
      ∀ (k : ℕ) (h : d + k = m) (σ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear k F.Carrier)),
        ¬ SmoothRep.IsSubrepresentation Z
          (T.castRank h ((T.binaryNormalizedProductFunctor d k).obj (A.obj, σ)))

/-- **Target.** For every actual supercuspidal `A`:

* (subquotients) subquotients of finite-length left `A`-reduced representations are left
  `A`-reduced;
* (product) normalized products of finite-length left `A`-reduced representations are left
  `A`-reduced;
* (comparison) if an irreducible `π` embeds into `A^K × Y`, where `Y` is finite-length, left
  `A`-reduced and every irreducible subrepresentation of `Y` is isomorphic to an irreducible
  `S`, then `π` embeds into `A^K × S`;
* (uniqueness) if `S` is irreducible and left `A`-reduced, any two irreducible
  subrepresentations of `A^K × S` are isomorphic;
* (segments) for a cuspidal datum `κ` represented by `A`, a segment head of `Δ` is left
  `A`-reduced unless `Δ.last = κ`, and a segment socle of `Δ` is left `A`-reduced unless
  `Δ.base = κ`.

Unproved. -/
def LeftCuspidalDerivativeLemma : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (d : ℕ)
      (A : GeneralLinear.SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := d)),
      (∀ (m : ℕ) (Y Y' : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)),
          Y.HasFiniteLength → SmoothRep.IsSubquotient Y' Y → LeftReduced F T A Y →
            LeftReduced F T A Y') ∧
      (∀ (m₁ m₂ : ℕ)
          (Y₁ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m₁ F.Carrier))
          (Y₂ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m₂ F.Carrier)),
          Y₁.HasFiniteLength → Y₂.HasFiniteLength →
          LeftReduced F T A Y₁ → LeftReduced F T A Y₂ →
            LeftReduced F T A ((T.binaryNormalizedProductFunctor m₁ m₂).obj (Y₁, Y₂))) ∧
      (∀ (K m : ℕ)
          (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (powerRank d K m) F.Carrier))
          (Y S : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)),
          Y.HasFiniteLength → π.IsIrreducible → S.IsIrreducible →
          LeftReduced F T A Y →
          (∀ Z : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier),
            Z.IsIrreducible → SmoothRep.IsSubrepresentation Z Y → Nonempty (Z ≅ S)) →
          SmoothRep.IsSubrepresentation π (powerProduct F T A K Y) →
            SmoothRep.IsSubrepresentation π (powerProduct F T A K S)) ∧
      (∀ (K m : ℕ) (S : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier))
          (π π' : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (powerRank d K m) F.Carrier)),
          S.IsIrreducible → LeftReduced F T A S → π.IsIrreducible → π'.IsIrreducible →
          SmoothRep.IsSubrepresentation π (powerProduct F T A K S) →
          SmoothRep.IsSubrepresentation π' (powerProduct F T A K S) → Nonempty (π ≅ π')) ∧
      (∀ (κ : T.CuspidalDatum.{max uF uV, uF}) (hκ : κ.rank = d),
          κ.IsRepresentedBy (hκ ▸ A) →
          ∀ (Δ : T.Segment.{max uF uV, uF})
            (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)),
            (T.IsSegmentHead Δ π → Δ.last ≠ κ → LeftReduced F T A π) ∧
            (T.IsSegmentSocle Δ π → Δ.base ≠ κ → LeftReduced F T A π))

end Langlands.Classification.LeftCuspidalDerivative
