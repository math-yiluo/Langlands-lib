import Langlands.Group.GL.AdjacentMergeShape
import Langlands.Group.GL.MirabolicOppositeIntersection
import Langlands.Representation.Induction.BlockFactors
import Langlands.Representation.Filtration.ObjectDefinitions

/-!
# Composition-factor commutativity of two-factor normalized products

Zelevinsky (1980), Theorem 1.9, for two smooth factors of finite length.
This is a proposition definition, not a proof.
-/

namespace Langlands.Parabolic

open GeneralLinear

/-- For finite-length smooth complex representations `π₁` of `GL_a` and `π₂` of
`GL_b`, the actual normalized products `π₁ × π₂` and `π₂ × π₁` on `GL_(a+b)` have
the same composition factors with multiplicities. The first product is induced
on the shape `(a, b)` with blocks `π₁, π₂`; the second on the same shape with
its two blocks swapped by `BlockShape.permute`, so of shape `(b, a)` with blocks
`π₂, π₁`. -/
def TwoBlockProductReversalFactors.{uF, uV} : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
      (π₁ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
      (π₂ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)),
      π₁.HasFiniteLength → π₂.HasFiniteLength →
        letI := T.generalLinearTopologicalGroup (a + b)
        let B := BlockShape.binary a b ha hb
        let A : ∀ i : Fin B.length,
            SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier) :=
          fun i => Fin.cases π₁ (fun _ => π₂) i
        let σ := B.adjacentSwap 0 Nat.one_lt_two
        HaveSameJordanHolderFactors
          (Rep.of (T.normalizedProductInduced B fun i => (A i).representation))
          (Rep.of (T.normalizedProductInduced (B.permute σ)
            fun i => (A (σ i)).representation))

end Langlands.Parabolic
