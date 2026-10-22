import Langlands.ClassFieldTheory.Local.Completion
import Langlands.ClassFieldTheory.Local.FiniteArtin
import Langlands.LocalField.Normalization.Definitions
import Mathlib.GroupTheory.Transfer

/-!
# Profinite local reciprocity and its characterization

These are proposition definitions, not assertions of proved local class field
theory. The completion is built from open finite quotients of the original
topology. The Galois target is the actual closed-commutator quotient.
-/

namespace Langlands.LocalClassField

universe u v

/-- A geometric normalization of the actual finite norm-residue system.
The inverse of the finite automorphism attached to a uniformizer acts on
residue classes by the residue-cardinality power map. -/
def GeometricProfiniteReciprocityRelation
    {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    (T : F.TopologicalData) :
    letI := T.topology
    (F.Carrierˣ →ₜ* Field.absoluteGaloisGroupAbelianization F.Carrier) → Prop :=
  letI := T.topology
  fun r =>
    ProfiniteNormResidueRelation r ∧
      ∀ (L : LocalFiniteAbelianExtension F)
        (S : (L.asPadicField (p := p)).TopologicalData)
        (a : F.Carrierˣ), T.ord (a : F.Carrier) = 1 →
        ∀ x : L.field, S.discreteValuation x ≤ 1 →
          S.discreteValuation
            ((finiteFamilyOfHom r L a).symm x -
              x ^ T.residueCardinality) < 1

/-- In characteristic zero the original topology makes every finite-index
subgroup open; no continuity is inferred merely from an abstract quotient. -/
def LocalFiniteIndexSubgroupsOpen : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (T : F.TopologicalData),
    letI := T.topology
    ∀ H : Subgroup F.Carrierˣ, H.FiniteIndex → IsOpen (H : Set F.Carrierˣ)

/-- Existence and uniqueness of the normalized continuous reciprocity
homomorphism, including all finite norm kernels and restrictions. -/
def ProfiniteReciprocityExistenceUniqueness : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (T : F.TopologicalData),
    letI := T.topology
    ∃! r : F.Carrierˣ →ₜ* Field.absoluteGaloisGroupAbelianization F.Carrier,
      GeometricProfiniteReciprocityRelation F T r

/-- The same reciprocity map is injective and extends uniquely to a
topological group isomorphism from the actual multiplicative completion. -/
def ProfiniteReciprocityCompletion : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (T : F.TopologicalData),
    letI := T.topology
    ∀ r : F.Carrierˣ →ₜ* Field.absoluteGaloisGroupAbelianization F.Carrier,
      GeometricProfiniteReciprocityRelation F T r →
        Function.Injective r ∧
          ∃! e : LocalMultiplicative.profiniteCompletion T ≃ₜ*
              Field.absoluteGaloisGroupAbelianization F.Carrier,
            ∀ a : F.Carrierˣ, e (LocalMultiplicative.completionMap T a) = r a

/-- Exactly the continuous finite-image complex characters of the original
multiplicative group descend uniquely from the profinite Galois quotient. -/
def ProfiniteReciprocityCharacterTransport : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (T : F.TopologicalData),
    letI := T.topology
    ∀ r : F.Carrierˣ →ₜ* Field.absoluteGaloisGroupAbelianization F.Carrier,
      GeometricProfiniteReciprocityRelation F T r →
        ∀ χ : F.Carrierˣ →ₜ* ℂˣ,
          (Set.range χ).Finite ↔
            ∃! ψ : Field.absoluteGaloisGroupAbelianization F.Carrier →ₜ* ℂˣ,
              ψ.comp r = χ

/-- For any finite extension, including non-Galois extensions, the actual
field norm corresponds to the map of absolute-Galois abelianizations.
Compatible embeddings of the algebraic closures are quantified explicitly. -/
def ProfiniteReciprocityNormFunctoriality : Prop :=
  ∀ (p : ℕ) [Fact p.Prime]
    (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier]
    [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [Algebra (AlgebraicClosure F.Carrier) (AlgebraicClosure E.Carrier)]
    [IsScalarTower F.Carrier
      (AlgebraicClosure F.Carrier) (AlgebraicClosure E.Carrier)]
    (T : F.TopologicalData) (S : E.TopologicalData),
    letI := T.topology
    letI := S.topology
    ∀ (rF : F.Carrierˣ →ₜ* Field.absoluteGaloisGroupAbelianization F.Carrier)
      (rE : E.Carrierˣ →ₜ* Field.absoluteGaloisGroupAbelianization E.Carrier),
      GeometricProfiniteReciprocityRelation F T rF →
      GeometricProfiniteReciprocityRelation E S rE →
        rF.comp (localNorm T S) =
          (absoluteAbelianizationMap (K := F.Carrier) (E := E.Carrier)).comp rE

/-- Field inclusion corresponds to the genuine finite-index transfer.
Its value on absolute Galois elements is pinned to Mathlib's coset-product
transfer, rather than an arbitrary map making the desired square commute.
The subgroup realization and the continuous descent are conclusions. -/
def ProfiniteReciprocityTransferFunctoriality : Prop :=
  ∀ (p : ℕ) [Fact p.Prime]
    (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier]
    [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [Algebra (AlgebraicClosure F.Carrier) (AlgebraicClosure E.Carrier)]
    [IsScalarTower F.Carrier
      (AlgebraicClosure F.Carrier) (AlgebraicClosure E.Carrier)]
    (T : F.TopologicalData) (S : E.TopologicalData),
    letI := T.topology
    letI := S.topology
    let i := Field.absoluteGaloisGroup.mapOfAlgebra F.Carrier E.Carrier
    let H := i.toMonoidHom.range
    ∃ h : H.FiniteIndex,
      letI := h
      ∃ j : Field.absoluteGaloisGroup E.Carrier ≃ₜ* H,
        (∀ g : Field.absoluteGaloisGroup E.Carrier, (j g).val = i g) ∧
        ∃ tr : Field.absoluteGaloisGroupAbelianization F.Carrier →ₜ*
            Field.absoluteGaloisGroupAbelianization E.Carrier,
          (∀ g : Field.absoluteGaloisGroup F.Carrier,
            tr (absoluteAbelianizationProjection F.Carrier g) =
              MonoidHom.transfer
                ((absoluteAbelianizationProjection E.Carrier).toMonoidHom.comp
                  (j.symm : H →ₜ* Field.absoluteGaloisGroup E.Carrier).toMonoidHom) g) ∧
          ∀ (rF : F.Carrierˣ →ₜ* Field.absoluteGaloisGroupAbelianization F.Carrier)
            (rE : E.Carrierˣ →ₜ* Field.absoluteGaloisGroupAbelianization E.Carrier),
            GeometricProfiniteReciprocityRelation F T rF →
            GeometricProfiniteReciprocityRelation E S rE →
              tr.comp rF = rE.comp (localInclusion T S)

/-- The local profinite reciprocity family, with unconditional existence
and uniqueness, completion, finite characters, norm and transfer diagrams. -/
def ProfiniteReciprocityTheorems : Prop :=
  LocalFiniteIndexSubgroupsOpen.{u} ∧
    ProfiniteReciprocityExistenceUniqueness.{u} ∧
      ProfiniteReciprocityCompletion.{u} ∧
        ProfiniteReciprocityCharacterTransport.{u} ∧
          ProfiniteReciprocityNormFunctoriality.{u, v} ∧
            ProfiniteReciprocityTransferFunctoriality.{u, v}

end Langlands.LocalClassField
