import Langlands.Representation.CompactCoefficient.Classes
import Langlands.Representation.Hecke.ActionProjection

/-! # The idempotents `e_{K,τ}` of an irreducible compact representation (Renard IV.1.5)

For an irreducible representation `τ` of a unimodular t.d. group with compactly supported
coefficients and a compact open subgroup `K`, there is a unique element `e_{K,τ}` of the Hecke
algebra acting on `τ` as `e_K` and by zero on every irreducible representation not isomorphic
to `τ`; these elements are compatible under shrinking `K` and under conjugation.
-/

noncomputable section

universe u v

open CategoryTheory MeasureTheory

namespace Langlands.Renard.CompactRepresentation

/-- Renard IV.1.5, Theorem: let `G` be a Hausdorff, locally compact, totally disconnected
group, countable at infinity, with a regular Haar measure `μ` that is also right invariant,
and `τ` an irreducible smooth representation with compactly supported smooth coefficients.
Say that `e ∈ H(G)` is a `(K, τ)`-projector if `τ(e) = τ(e_K)` for the normalized indicator
`e_K` of `K`, and `ρ(e) = 0` for every irreducible smooth `ρ` not isomorphic to `τ`. Then

* (i) for every compact open `K` there is exactly one `(K, τ)`-projector `e_{K,τ}`;
* (ii) if `K' ≤ K`, then `e_{K',τ} * e_{K,τ} = e_K * e_{K',τ} = e_{K',τ} * e_K = e_{K,τ}`; in
  particular `e_{K,τ}` is idempotent;
* (iii) for `g ∈ G`, the conjugate `x ↦ e_{K,τ}(g⁻¹ x g)` (that is `δ_g * e_{K,τ} * δ_{g⁻¹}`)
  is the `(gKg⁻¹, τ)`-projector. -/
def CompactProjectionDistributionStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [SigmaCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    [μ.IsMulRightInvariant] (τ : SmoothRep.{0, u, v} ℂ G),
    τ.IsIrreducible → HasCompactSmoothDualCoefficients τ.representation →
    let IsProjector : (K : OpenSubgroup G) → IsCompact (K : Set G) → Hecke.HeckeAlgebra μ → Prop :=
      fun K hK e =>
        Hecke.heckeAction μ τ.representation τ.isSmooth e =
            Hecke.heckeAction μ τ.representation τ.isSmooth
              (Hecke.HeckeAlgebra.normalizedIndicator μ K hK) ∧
          ∀ ρ : SmoothRep.{0, u, v} ℂ G, ρ.IsIrreducible → IsEmpty (ρ ≅ τ) →
            Hecke.heckeAction μ ρ.representation ρ.isSmooth e = 0
    (∀ (K : OpenSubgroup G) (hK : IsCompact (K : Set G)), ∃! e, IsProjector K hK e) ∧
    (∀ (K K' : OpenSubgroup G) (hK : IsCompact (K : Set G)) (hK' : IsCompact (K' : Set G))
        (e e' : Hecke.HeckeAlgebra μ), K' ≤ K → IsProjector K hK e → IsProjector K' hK' e' →
        e' * e = e ∧ Hecke.HeckeAlgebra.normalizedIndicator μ K hK * e' = e ∧
          e' * Hecke.HeckeAlgebra.normalizedIndicator μ K hK = e) ∧
    ∀ (g : G) (K K' : OpenSubgroup G) (hK : IsCompact (K : Set G))
      (hK' : IsCompact (K' : Set G)) (e : Hecke.HeckeAlgebra μ),
      (∀ x : G, x ∈ K' ↔ g⁻¹ * x * g ∈ K) → IsProjector K hK e →
        IsProjector K' hK'
          ((Hecke.HeckeAlgebra.toTestFunction μ).symm
            (Hecke.TestFunction.rightTranslate g
              (Hecke.TestFunction.leftTranslate g (Hecke.HeckeAlgebra.toTestFunction μ e))))

end Langlands.Renard.CompactRepresentation
