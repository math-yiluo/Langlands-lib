import Langlands.Representation.Twist.Definitions
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Semisimple
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Operations and invariants of finite-dimensional complex representations

All operations are the existing Mathlib operations or the accepted scalar twist.
The usual complex topology is specified intrinsically by `moduleTopology`.
These are proposition targets, not proofs or additional representation records.
-/

noncomputable section

open scoped TensorProduct

namespace Langlands.Weil

universe uG uV uU uT

/-- Linear representation isomorphism preserves the conditions and invariants
used for complex Weil representations. -/
def RepresentationIsomorphismInvariance : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] (I : Subgroup G)
    (V : Type uV) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (U : Type uU) [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G U), Nonempty (ρ.Equiv σ) →
    letI : TopologicalSpace (Module.End ℂ V) := moduleTopology ℂ (Module.End ℂ V)
    letI : TopologicalSpace (Module.End ℂ U) := moduleTopology ℂ (Module.End ℂ U)
    ρ.ker = σ.ker ∧
    (ρ.comp I.subtype).ker = (σ.comp I.subtype).ker ∧
    (Continuous ρ ↔ Continuous σ) ∧
    (IsOpen ((ρ.comp I.subtype).ker : Set I) ↔
      IsOpen ((σ.comp I.subtype).ker : Set I)) ∧
    ((Set.range ρ).Finite ↔ (Set.range σ).Finite) ∧
    ((Set.range (ρ.comp I.subtype)).Finite ↔
      (Set.range (σ.comp I.subtype)).Finite) ∧
    ((∀ i : I, ρ (i : G) = 1) ↔ ∀ i : I, σ (i : G) = 1) ∧
    (Representation.IsIrreducible ρ ↔ Representation.IsIrreducible σ) ∧
    (Representation.IsSemisimpleRepresentation ρ ↔
      Representation.IsSemisimpleRepresentation σ) ∧
    Module.finrank ℂ V = Module.finrank ℂ U ∧
    ∀ g : G, LinearMap.det (ρ g) = LinearMap.det (σ g)

/-- The rank and determinant formulas use actual product, tensor and dual
carriers. Twisting keeps its original carrier. -/
def RepresentationRankDeterminant : Prop :=
  ∀ (G : Type uG) [Group G]
    (V : Type uV) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (U : Type uU) [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G U),
    Module.finrank ℂ (V × U) = Module.finrank ℂ V + Module.finrank ℂ U ∧
    Module.finrank ℂ (V ⊗[ℂ] U) = Module.finrank ℂ V * Module.finrank ℂ U ∧
    Module.finrank ℂ (Module.Dual ℂ V) = Module.finrank ℂ V ∧
    (∀ g : G,
      LinearMap.det ((ρ.prod σ) g) = LinearMap.det (ρ g) * LinearMap.det (σ g) ∧
      LinearMap.det ((ρ.tprod σ) g) =
        LinearMap.det (ρ g) ^ Module.finrank ℂ U *
          LinearMap.det (σ g) ^ Module.finrank ℂ V ∧
      LinearMap.det (ρ.dual g) = (LinearMap.det (ρ g))⁻¹) ∧
    ∀ (χ : G →* ℂˣ) (g : G),
      LinearMap.det (Langlands.twist χ ρ g) =
        (χ g : ℂ) ^ Module.finrank ℂ V * LinearMap.det (ρ g)

/-- Rank additivity and determinant multiplicativity on an actual short exact
sequence of representations, without assuming a splitting. -/
def RepresentationExactSequenceInvariants : Prop :=
  ∀ (G : Type uG) [Group G]
    (V : Type uV) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (U : Type uU) [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]
    (T : Type uT) [AddCommGroup T] [Module ℂ T] [FiniteDimensional ℂ T]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G U)
    (τ : Representation ℂ G T)
    (f : ρ.IntertwiningMap σ) (g : σ.IntertwiningMap τ),
    Function.Injective f → Function.Surjective g →
    LinearMap.range f.toLinearMap = LinearMap.ker g.toLinearMap →
    Module.finrank ℂ U = Module.finrank ℂ V + Module.finrank ℂ T ∧
    ∀ w : G, LinearMap.det (σ w) = LinearMap.det (ρ w) * LinearMap.det (τ w)

/-- Continuity, open inertia kernels and finite images are preserved by the
standard operations. No finiteness of the whole group is assumed. -/
def RepresentationOperationClosure : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (I : Subgroup G)
    (V : Type uV) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (U : Type uU) [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G U),
    letI : TopologicalSpace (Module.End ℂ V) := moduleTopology ℂ (Module.End ℂ V)
    letI : TopologicalSpace (Module.End ℂ U) := moduleTopology ℂ (Module.End ℂ U)
    letI : TopologicalSpace (Module.End ℂ (V × U)) :=
      moduleTopology ℂ (Module.End ℂ (V × U))
    letI : TopologicalSpace (Module.End ℂ (V ⊗[ℂ] U)) :=
      moduleTopology ℂ (Module.End ℂ (V ⊗[ℂ] U))
    letI : TopologicalSpace (Module.End ℂ (Module.Dual ℂ V)) :=
      moduleTopology ℂ (Module.End ℂ (Module.Dual ℂ V))
    (Continuous ρ → Continuous σ →
      Continuous (ρ.prod σ) ∧ Continuous (ρ.tprod σ)) ∧
    (Continuous ρ.dual ↔ Continuous ρ) ∧
    (IsOpen ((ρ.comp I.subtype).ker : Set I) →
      IsOpen ((σ.comp I.subtype).ker : Set I) →
      IsOpen (((ρ.prod σ).comp I.subtype).ker : Set I) ∧
      IsOpen (((ρ.tprod σ).comp I.subtype).ker : Set I)) ∧
    (IsOpen ((ρ.dual.comp I.subtype).ker : Set I) ↔
      IsOpen ((ρ.comp I.subtype).ker : Set I)) ∧
    ((Set.range ρ).Finite → (Set.range σ).Finite →
      (Set.range (ρ.prod σ)).Finite ∧ (Set.range (ρ.tprod σ)).Finite) ∧
    ((Set.range ρ.dual).Finite ↔ (Set.range ρ).Finite) ∧
    ((Set.range (ρ.comp I.subtype)).Finite →
      (Set.range (σ.comp I.subtype)).Finite →
      (Set.range ((ρ.prod σ).comp I.subtype)).Finite ∧
      (Set.range ((ρ.tprod σ).comp I.subtype)).Finite) ∧
    ((Set.range (ρ.dual.comp I.subtype)).Finite ↔
      (Set.range (ρ.comp I.subtype)).Finite) ∧
    ((∀ i : I, ρ (i : G) = 1) → (∀ i : I, σ (i : G) = 1) →
      (∀ i : I, (ρ.prod σ) (i : G) = 1) ∧
      (∀ i : I, (ρ.tprod σ) (i : G) = 1)) ∧
    ((∀ i : I, ρ.dual (i : G) = 1) ↔ ∀ i : I, ρ (i : G) = 1) ∧
    (Representation.IsIrreducible ρ.dual ↔ Representation.IsIrreducible ρ) ∧
    (Representation.IsSemisimpleRepresentation ρ.dual ↔
      Representation.IsSemisimpleRepresentation ρ) ∧
    ∀ χ : G →* ℂˣ,
      (Continuous χ → Continuous ρ → Continuous (Langlands.twist χ ρ)) ∧
      (IsOpen ((χ.comp I.subtype).ker : Set I) →
        IsOpen ((ρ.comp I.subtype).ker : Set I) →
        IsOpen (((Langlands.twist χ ρ).comp I.subtype).ker : Set I)) ∧
      ((Set.range χ).Finite → (Set.range ρ).Finite →
        (Set.range (Langlands.twist χ ρ)).Finite) ∧
      ((Set.range (χ.comp I.subtype)).Finite →
        (Set.range (ρ.comp I.subtype)).Finite →
        (Set.range ((Langlands.twist χ ρ).comp I.subtype)).Finite) ∧
      ((∀ i : I, χ (i : G) = 1) →
        ((∀ i : I, Langlands.twist χ ρ (i : G) = 1) ↔
          ∀ i : I, ρ (i : G) = 1)) ∧
      (Representation.IsIrreducible (Langlands.twist χ ρ) ↔
        Representation.IsIrreducible ρ) ∧
      (Representation.IsSemisimpleRepresentation (Langlands.twist χ ρ) ↔
        Representation.IsSemisimpleRepresentation ρ)

/-- The determinant is a continuous unit-valued character, and every rank-one
representation is isomorphic to exactly one scalar-character representation.
The witnesses are conclusions, not input data. -/
def RepresentationCharacterNormalization : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G]
    (V : Type uV) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V),
    letI : TopologicalSpace (Module.End ℂ V) := moduleTopology ℂ (Module.End ℂ V)
    Continuous ρ →
    (∃! δ : G →* ℂˣ,
      Continuous δ ∧ ∀ g : G, (δ g : ℂ) = LinearMap.det (ρ g)) ∧
    (Module.finrank ℂ V = 1 →
      ∃! χ : G →* ℂˣ,
        Continuous χ ∧ Nonempty (ρ.Equiv (Langlands.characterRepresentation χ)))

/-- The complete operation, invariance and normalization target. -/
def RepresentationOperations : Prop :=
  RepresentationIsomorphismInvariance.{uG, uV, uU} ∧
  RepresentationRankDeterminant.{uG, uV, uU} ∧
  RepresentationExactSequenceInvariants.{uG, uV, uU, uT} ∧
  RepresentationOperationClosure.{uG, uV, uU} ∧
  RepresentationCharacterNormalization.{uG, uV}

end Langlands.Weil
