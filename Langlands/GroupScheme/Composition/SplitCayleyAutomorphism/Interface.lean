import Langlands.GroupScheme.Composition.SplitCayleyAutomorphism.RootGroups

/-! # Algebraic inputs for the split Cayley automorphism pinning (proposed interface)

Four pure matrix-algebra statements about Zorn's algebra used by the scheme-theoretic proof of
`SplitCayleyAutomorphismPinningStatement`. They mention only the root-group matrices
`rootMatrix`/`rootGL`, the torus matrices `torusGL` and the predicate `IsAutomorphism` of
`RootGroups.lean`. -/

noncomputable section

universe u

namespace Langlands.GroupScheme

namespace SplitCayley

/-- Generation (used for connectedness): over an algebraically closed field every automorphism
matrix of Zorn's algebra is a finite product of root-group and torus elements. -/
def GenerationStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (g : GL (Fin 8) k),
    IsAutomorphism ((g : Matrix (Fin 8) (Fin 8) k).mulVec) →
      g ∈ Subgroup.closure (Set.range (fun p : Root × k => rootGL p.1 p.2) ∪
        Set.range (fun p : kˣ × kˣ => torusGL p.1 p.2))

/-- Stable subspaces (used for the unipotent radical): over an algebraically closed field, a
subspace of `k⁸` that is stable under all root-group and torus elements and contains a vector off
the line of the unit contains the six coordinate vectors `u₁, u₂, u₃, v₁, v₂, v₃`. -/
def StableSubspaceStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (W : Submodule k (Fin 8 → k)),
    (∀ (α : Root) (r : k), ∀ w ∈ W, (rootMatrix α r).mulVec w ∈ W) →
    (∀ s t : kˣ, ∀ w ∈ W, ((torusGL s t : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k).mulVec w ∈ W) →
    (∃ w ∈ W, w ∉ Submodule.span k {unit k}) →
      ∀ i : Fin 8, i ≠ 0 → i ≠ 7 → (Pi.single i 1 : Fin 8 → k) ∈ W

/-- Rigidity modulo the unit (used for the unipotent radical): over any commutative ring, an
automorphism matrix moving each of `u₁, …, v₃` only by a multiple of the unit is the identity. -/
def UnitRigidityStatement : Prop :=
  ∀ (A : Type u) [CommRing A] (g : Matrix (Fin 8) (Fin 8) A), IsAutomorphism g.mulVec →
    (∀ i : Fin 8, i ≠ 0 → i ≠ 7 →
      ∃ c : A, g.mulVec (Pi.single i 1) = Pi.single i 1 + c • unit A) →
      g = 1

/-- Rigidity of central elements (used for the trivial centre): over any commutative ring, an
automorphism matrix commuting with every root-group element `x_α(1)` is the identity. -/
def CenterRigidityStatement : Prop :=
  ∀ (A : Type u) [CommRing A] (g : Matrix (Fin 8) (Fin 8) A), IsAutomorphism g.mulVec →
    (∀ α : Root, Commute g (rootMatrix α 1)) → g = 1

end SplitCayley

end Langlands.GroupScheme
