import Langlands.Representation.Induction.ConjugateParabolic
import Langlands.Representation.Classification.RelativeRegularComparisonStatement
import Langlands.Group.GL.SingletonBlocks
import Langlands.Group.GL.Maps

/-!
# Semistandard recovery of Langlands data

A derived GL_n form of Silberger 1978, Corollary 6.2, with actual
Weyl representatives, parabolic pairs and conjugate-parabolic induction.
-/

noncomputable section

namespace Langlands

open GeneralLinear Exponents
open RelativeRegularComparison

universe uF uV uW uJ uK

/-- Equivalent irreducible quotients of regular-positive semistandard and
standard inductions recover the actual parabolic pair, untwisted tempered
representation and real character under a representative of the ambient Weyl group. -/
def GLSemistandardLanglandsConjugacyStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n →
      let A₀ := (ConjugateBlockPair.standard
        (R := F.Carrier) (BlockShape.singletons n)).splitComponent
      ∀ (P : ConjugateBlockPair n F.Carrier) (B : BlockShape n),
        P.splitComponent ≤ A₀ →
        ∀ (σ : Rep.{uV} ℂ (P.shape.Levi F.Carrier))
          (τ : Rep.{uW} ℂ (B.Levi F.Carrier)),
          Representation.IsIrreducible σ.ρ → IsLeviTempered T P.shape σ →
          Representation.IsIrreducible τ.ρ → IsLeviTempered T B τ →
          ∀ (t : Fin P.shape.length → ℝ) (u : Fin B.length → ℝ),
            StrictAnti t → StrictAnti u →
            ∀ (J : Rep.{uJ} ℂ (GeneralLinear n F.Carrier))
              (K : Rep.{uK} ℂ (GeneralLinear n F.Carrier)),
              Representation.IsIrreducible J.ρ →
              Representation.IsIrreducible K.ρ →
              (∃ q : (T.normalizedConjugateParabolicInduced P
                  (T.leviRealPowerTwist P.shape t σ.ρ)).IntertwiningMap J.ρ,
                Function.Surjective q) →
              (∃ q : (T.normalizedParabolicInduced B
                  (T.leviRealPowerTwist B u τ.ρ)).IntertwiningMap K.ρ,
                Function.Surjective q) →
              Nonempty (J.ρ.Equiv K.ρ) →
              ∃ (w : Equiv.Perm (Fin n))
                (e : P.shape.Levi F.Carrier ≃ₜ* B.Levi F.Carrier),
                let y := GeneralLinear.permutation n F.Carrier w
                y ∈ Subgroup.normalizer (A₀ : Set (GeneralLinear n F.Carrier)) ∧
                P.parabolic.map (MulAut.conj y).toMonoidHom = B.parabolic F.Carrier ∧
                P.splitComponent.map (MulAut.conj y).toMonoidHom =
                  (ConjugateBlockPair.standard (R := F.Carrier) B).splitComponent ∧
                P.leviSubgroup.map (MulAut.conj y).toMonoidHom = B.leviSubgroup F.Carrier ∧
                (∀ m : P.shape.Levi F.Carrier,
                  B.leviEmbedding F.Carrier (e m) = y * P.leviEmbedding m * y⁻¹) ∧
                (T.leviRealPowerCharacter P.shape t).comp
                  e.toMulEquiv.symm.toMonoidHom = T.leviRealPowerCharacter B u ∧
                Nonempty (Representation.Equiv
                  (σ.ρ.comp e.toMulEquiv.symm.toMonoidHom) τ.ρ)

end Langlands
