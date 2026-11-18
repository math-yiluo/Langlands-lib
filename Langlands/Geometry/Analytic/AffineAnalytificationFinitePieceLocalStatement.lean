import Langlands.Geometry.Analytic.AffineAnalytificationLocalizedMap
import Langlands.Geometry.Analytic.FullRecognitionEtaleMorphisms
import Langlands.Geometry.Analytic.AnalytificationCenter

/-! # Statement: local structure of the finite pieces of an affine analytification map -/

universe u v w

namespace Langlands.Analytic.AffineAnalytification

open scoped TensorProduct

/-- Derived statement. The conditions on `α` and `β` follow Berkovich 1990, §3.4 (Theorem 3.4.1
and the last paragraph of its proof). The local comparison `χ` is a Library analogue of the
identity `A_W = A_V ⊗_B C` in the proof of Berkovich 1993, Proposition 2.6.10, not that
proposition itself. Let `g := saturatedHom K P Q f` be finite over open sets
`V` and `U`, let `W ⊆ U` be a recognized affinoid subset of the analytification of `A` with
algebra `R`, and let `V'` be a recognized affinoid subset with locus `V ∩ g⁻¹(W)` and algebra
`S`, such that the bounded map `φ : R → S` of the piece is finite Banach. Then there are
`K`-algebra maps `α : A → R` and `β : B → S` such that `α` is flat, every point `t` of `M(R)`
restricts along `α` to the seminorm of the point `W.chart t`, every point `s` of `M(S)`
restricts along `β` to the seminorm of the point `V'.chart s`, and the ring map
`χ : R ⊗_A B → S` given by `φ` and `β` becomes bijective after localizing at the prime of every
point `s` of `M(S)`. -/
def AffineAnalytificationFinitePieceLocalStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (A : Type v) [CommRing A] [Algebra K A] (B : Type w) [CommRing B] [Algebra K B]
    (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
    (f : A →ₐ[K] B) (V : Set (presentation K Q).space) (U : Set (presentation K P).space),
    let g := saturatedHom K P Q f
    IsOpen V → IsOpen U →
    AffinoidAtlasPresentation.StrongHom.IsFiniteOver (A := presentation K Q)
      (B := presentation K P) g V U →
    ∀ (W : (presentation K P).atlas.saturatedAtlas.RecognizedSubset), W.locus ⊆ U →
    ∀ (V' : (presentation K Q).atlas.saturatedAtlas.RecognizedSubset)
      (h : g.baseMap '' Set.range V'.chart ⊆ Set.range W.chart),
      V'.locus = V ∩ g.baseMap ⁻¹' W.locus →
      (g.fullRecognitionPairs.pullback V' W h).IsFiniteBanach →
      ∃ (α : A →ₐ[K] W.algebra) (β : B →ₐ[K] V'.algebra),
        α.toRingHom.Flat ∧
        (∀ (t : BanachSpectrum W.algebra) (a : A), t (α a) = pointSeminorm K P (W.chart t) a) ∧
        (∀ (s : BanachSpectrum V'.algebra) (b : B), s (β b) = pointSeminorm K Q (V'.chart s) b) ∧
        (letI : Algebra A W.algebra := α.toRingHom.toAlgebra
         letI : Algebra A B := f.toRingHom.toAlgebra
         ∃ χ : W.algebra ⊗[A] B →+* V'.algebra,
          (∀ r : W.algebra, χ (r ⊗ₜ[A] 1) = g.fullRecognitionPairs.pullback V' W h r) ∧
          (∀ b : B, χ (1 ⊗ₜ[A] b) = β b) ∧
          ∀ s : BanachSpectrum V'.algebra,
            Function.Bijective (Localization.localRingHom (s.kernel.comap χ) s.kernel χ rfl))

end Langlands.Analytic.AffineAnalytification
