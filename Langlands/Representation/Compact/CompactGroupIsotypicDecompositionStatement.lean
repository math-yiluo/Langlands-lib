import Langlands.Representation.CompactCoefficient.Isotypic

/-! # Isotypic decomposition for compact t.d. groups (Renard IV.1.1, Corollary)

Every smooth representation of a compact totally disconnected group is the internal direct
sum of its isotypic components, indexed by the isomorphism classes of irreducible smooth
representations.
-/

universe u v

open CategoryTheory

namespace Langlands.Renard.CompactRepresentation

/-- Renard IV.1.1, Corollary: let `K` be a compact, Hausdorff, totally disconnected topological
group and `π` a smooth complex representation of `K`. The isotypic components `V(σ)` of `π`,
`σ` running over the isomorphism classes of irreducible smooth representations of `K` (all of
which have compactly supported coefficients, `K` being compact), are independent and span
`π`: `V = ⊕_σ V(σ)`. Here `V(σ)` is the published `isotypicSubrepresentation`, the sum of the
images of all intertwiners from representatives of `σ`, i.e. the image of
`Hom_K(V_σ, V) ⊗ V_σ → V`. -/
def CompactGroupIsotypicDecompositionStatement : Prop :=
  ∀ (K : Type u) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    [T2Space K] [TotallyDisconnectedSpace K] (π : SmoothRep.{0, u, v} ℂ K),
    iSupIndep (fun c : CompactCoefficientClass.{u, v} K =>
        CompactCoefficientClass.isotypicSubrepresentation c π) ∧
      (⨆ c : CompactCoefficientClass.{u, v} K,
        CompactCoefficientClass.isotypicSubrepresentation c π) = ⊤

end Langlands.Renard.CompactRepresentation
