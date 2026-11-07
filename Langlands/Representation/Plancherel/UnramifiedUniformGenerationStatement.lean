import Langlands.Representation.Plancherel.CompactIntertwiningFamilies
import Langlands.Representation.Jacquet.IwahoriStablePairingData

/-! # Uniform fixed-vector generation of actual unramified induction -/

noncomputable section

open scoped NNReal

namespace Langlands.Plancherel

open Aubert.General

universe uG uI uV

/-- Under the displayed compact-picture and opposite-Iwahori hypotheses, one
arbitrarily small compact open subgroup generates every actual unramified
induced fiber by its fixed vectors. Every smaller open subgroup also does so. -/
def UnramifiedUniformGenerationStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G]
    [LocallyCompactSpace G] [NonarchimedeanGroup G] [T2Space G]
    (P M U Ubar : Subgroup G)
    (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
    (_hδ : IsUnimodularModulus U hU)
    (K : OpenSubgroup G) (_hP : IsClosed (P : Set G))
    (_hK : IsCompact (K : Set G))
    (_hPK : ∀ x : G, ∃ p : P, ∃ k : K, x = (p : G) * (k : G))
    (I : Type uI) (ν : I → (M →* ℝ≥0ˣ)) (_hν : ∀ i, Continuous (ν i))
    (_hr : Continuous h.projection)
    (A : SmoothRep.{0, uG, uV} ℂ M) (_hfin : A.HasFiniteLength)
    (_hMUbar : M ≤ Subgroup.normalizer (Ubar : Set G))
    (_hPUbar : ∀ x : G, x ∈ P → x ∈ Ubar → x = 1)
    (g : G) (_hbasis : Jacquet.HasOppositeIwahoriContractionBasis U M Ubar g)
    (O : Set G) (_hO : IsOpen O) (_h1 : (1 : G) ∈ O),
    ∃ L₀ : OpenSubgroup G, IsCompact (L₀ : Set G) ∧ (L₀ : Set G) ⊆ O ∧
      L₀ ≤ K ∧
      ∀ H : OpenSubgroup G, H ≤ L₀ →
        ∀ χ : unramifiedCharacters ν,
          ∀ S : Subrepresentation (UnramifiedLeviInduction h hU ν χ A).representation,
            fixedVectors (UnramifiedLeviInduction h hU ν χ A).representation
              H.toSubgroup ≤ S.toSubmodule → S = ⊤

end Langlands.Plancherel
