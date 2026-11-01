import Langlands.Representation.Derivative.Homogeneity
import Langlands.Representation.Classification.SupercuspidalSupport

/-!
# Support shift for mirabolic submodules of cuspidal products

Bernstein–Zelevinsky 1977, Lemma 4.7(b), for an actual mirabolic
representation embedded in the restriction of a product of supercuspidal
representations. No proof is supplied.
-/

noncomputable section

namespace Langlands.Classification

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Let `π = ρ_1 × ⋯ × ρ_r` be a product of actual supercuspidal representatives
`A_i` of cuspidal data `ρ_i` on `GL_(N+1)`, and let `W` be a representation of
`P_(N+1)` with an injective intertwiner into the restriction `π|P`. If the
highest nonzero derivative of `W` has order `k > 0`, then for every irreducible
subrepresentation `σ` of `W^(k)` and every supercuspidal support `s` of `σ`,
the multiset `ν · s` is contained in `ρ_1 + ⋯ + ρ_r`. -/
def CuspidalProductMirabolicSupportShift : Prop :=
  letI := T.topology
  ∀ (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N r : ℕ) (ρ : Fin r → T.CuspidalDatum.{uV, uF}) (h : ∑ i, (ρ i).rank = N + 1)
    (A : ∀ i, GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank)),
    (∀ i, (ρ i).IsRepresentedBy (A i)) →
    ∀ (W : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear.mirabolic N F.Carrier))
      (f : W ⟶ (Derivative.generalLinearRestriction T N).obj (T.cuspidalProductInduced ρ h A)),
      Function.Injective (SmoothRep.hom f) →
    ∀ (k : ℕ) (hk : 0 < k ∧ k ≤ N + 1), Derivative.level T ψ W = k →
    ∀ σ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (N + 1 - k) F.Carrier),
      IsIrreducibleSubrepresentation
        ((Derivative.mirabolicDerivativeOfOrder T ψ N k hk).obj W).representation
        σ.representation →
      ∀ s : Multiset (T.CuspidalDatum.{uV, uF}), T.IsSupercuspidalSupport σ s →
        s.map (PadicField.TopologicalData.CuspidalDatum.twist 1) ≤
          (List.ofFn ρ : Multiset (T.CuspidalDatum.{uV, uF}))

end Langlands.Classification
