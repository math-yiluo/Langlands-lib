import Langlands.Representation.Twist.Definitions
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.RepresentationTheory.FiniteIndex
import Mathlib.RepresentationTheory.Semisimple
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Restriction and finite-index induction of complex Weil representations

The induced representation is Mathlib's actual coinvariant vector space `IndV`.
No finite-dimensionality, continuity or semisimplicity of the induced action is
assumed: these properties occur as conclusions. Local-field embeddings remain
the responsibility of the arithmetic construction.
-/

noncomputable section

namespace Langlands.Weil

universe uG uH uV uU

/-- Restriction along a continuous homomorphism, including the correct supplied
inertia inclusion. There is no irreducibility claim for arbitrary restriction. -/
def RepresentationRestriction : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G]
    (H : Type uH) [Group H] [TopologicalSpace H] (φ : H →* G)
    (I : Subgroup G) (J : Subgroup H),
    Continuous φ → J ≤ I.comap φ →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (U : Type uU) [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]
      (ρ : Representation ℂ G V) (σ : Representation ℂ G U),
      letI : TopologicalSpace (Module.End ℂ V) := moduleTopology ℂ (Module.End ℂ V)
      (Continuous ρ → Continuous (ρ.comp φ)) ∧
      (IsOpen ((ρ.comp I.subtype).ker : Set I) →
        IsOpen (((ρ.comp φ).comp J.subtype).ker : Set J)) ∧
      ((Set.range (ρ.comp I.subtype)).Finite →
        (Set.range ((ρ.comp φ).comp J.subtype)).Finite) ∧
      ((Set.range ρ).Finite → (Set.range (ρ.comp φ)).Finite) ∧
      ((∀ i : I, ρ (i : G) = 1) → ∀ j : J, (ρ.comp φ) (j : H) = 1) ∧
      (ρ.prod σ).comp φ = Representation.prod (ρ.comp φ) (σ.comp φ) ∧
      (ρ.tprod σ).comp φ = Representation.tprod (ρ.comp φ) (σ.comp φ) ∧
      ρ.dual.comp φ = Representation.dual (ρ.comp φ) ∧
      (∀ h : H, LinearMap.det ((ρ.comp φ) h) = LinearMap.det (ρ (φ h))) ∧
      (Nonempty (ρ.Equiv σ) →
        Nonempty (Representation.Equiv (ρ.comp φ) (σ.comp φ)))

/-- The actual induced carrier is finite-dimensional of the expected dimension;
finite image and semisimplicity are reflected as well as preserved. -/
def RepresentationInductionFiniteness : Prop :=
  ∀ (G : Type uG) [Group G] (H : Subgroup G) [H.FiniteIndex]
    (V : Type uV) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ H V),
    FiniteDimensional ℂ (Representation.IndV H.subtype ρ) ∧
    Module.finrank ℂ (Representation.IndV H.subtype ρ) =
      H.index * Module.finrank ℂ V ∧
    ((Set.range (ρ.ind H.subtype)).Finite ↔ (Set.range ρ).Finite) ∧
    (Representation.IsSemisimpleRepresentation (ρ.ind H.subtype) ↔
      Representation.IsSemisimpleRepresentation ρ) ∧
    ∀ σ : Representation ℂ G V,
      Representation.IsSemisimpleRepresentation (σ.comp H.subtype) ↔
        Representation.IsSemisimpleRepresentation σ

/-- For an open finite-index subgroup, induction preserves and reflects ordinary
complex continuity. Normal inertia is needed for the induction inertia comparisons. -/
def RepresentationInductionTopology : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H : OpenSubgroup G) [H.toSubgroup.FiniteIndex]
    (I : Subgroup G) [I.Normal]
    (V : Type uV) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ H V),
    letI : TopologicalSpace (Module.End ℂ V) := moduleTopology ℂ (Module.End ℂ V)
    letI : TopologicalSpace (Module.End ℂ (Representation.IndV H.toSubgroup.subtype ρ)) :=
      moduleTopology ℂ (Module.End ℂ (Representation.IndV H.toSubgroup.subtype ρ))
    (Continuous (ρ.ind H.toSubgroup.subtype) ↔ Continuous ρ) ∧
    (IsOpen (((ρ.ind H.toSubgroup.subtype).comp I.subtype).ker : Set I) ↔
      IsOpen ((ρ.comp (I.comap H.toSubgroup.subtype).subtype).ker :
        Set (I.comap H.toSubgroup.subtype))) ∧
    ((Set.range ((ρ.ind H.toSubgroup.subtype).comp I.subtype)).Finite ↔
      (Set.range (ρ.comp (I.comap H.toSubgroup.subtype).subtype)).Finite) ∧
    (I ≤ H.toSubgroup →
      ((∀ i : I, ρ.ind H.toSubgroup.subtype (i : G) = 1) ↔
        ∀ i : I.comap H.toSubgroup.subtype, ρ (i : H) = 1))

/-- Frobenius reciprocity expressed by the actual generator map into `IndV`.
It applies even without a finite-index or finite-dimensional hypothesis. -/
def RepresentationInductionReciprocity : Prop :=
  ∀ (G : Type uG) [Group G] (H : Subgroup G)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (U : Type uU) [AddCommGroup U] [Module ℂ U]
    (ρ : Representation ℂ H V) (σ : Representation ℂ G U)
    (f : ρ.IntertwiningMap (σ.comp H.subtype)),
    ∃! F : (ρ.ind H.subtype).IntertwiningMap σ,
      ∀ v : V, F (Representation.IndV.mk H.subtype ρ 1 v) = f v

/-- Finite-index induction commutes with sum and dual, has the tensor projection
formula, respects twists and isomorphisms, and is transitive. -/
def RepresentationInductionCompatibility : Prop :=
  ∀ (G : Type uG) [Group G] (H : Subgroup G) [H.FiniteIndex]
    (V : Type uV) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (U : Type uU) [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]
    (ρ : Representation ℂ H V) (τ : Representation ℂ H U)
    (σ : Representation ℂ G U),
    Nonempty (((ρ.prod τ).ind H.subtype).Equiv
      ((ρ.ind H.subtype).prod (τ.ind H.subtype))) ∧
    Nonempty (((ρ.tprod (σ.comp H.subtype)).ind H.subtype).Equiv
      ((ρ.ind H.subtype).tprod σ)) ∧
    Nonempty ((ρ.dual.ind H.subtype).Equiv (ρ.ind H.subtype).dual) ∧
    (Nonempty (ρ.Equiv τ) → Nonempty ((ρ.ind H.subtype).Equiv (τ.ind H.subtype))) ∧
    (∀ χ : G →* ℂˣ,
      Nonempty (((Langlands.twist (χ.comp H.subtype) ρ).ind H.subtype).Equiv
        (Langlands.twist χ (ρ.ind H.subtype)))) ∧
    ∀ (K : Subgroup H) [K.FiniteIndex] (π : Representation ℂ K V),
      Nonempty (((π.ind K.subtype).ind H.subtype).Equiv
        (π.ind (H.subtype.comp K.subtype)))

/-- The complete generic restriction/induction target for the Weil framework. -/
def RepresentationRestrictionInduction : Prop :=
  RepresentationRestriction.{uG, uH, uV, uU} ∧
  RepresentationInductionFiniteness.{uG, uV} ∧
  RepresentationInductionTopology.{uG, uV} ∧
  RepresentationInductionReciprocity.{uG, uV, uU} ∧
  RepresentationInductionCompatibility.{uG, uV, uU}

end Langlands.Weil
