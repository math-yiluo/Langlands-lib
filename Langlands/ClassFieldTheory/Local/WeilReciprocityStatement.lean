import Langlands.ClassFieldTheory.Local.ReciprocityRelations
import Langlands.ClassFieldTheory.Local.ProfiniteReciprocityStatement
import Langlands.Weil.Local.Assembly
import Langlands.HarmonicAnalysis.Conductor

/-!
# Geometric local Weil reciprocity and quasicharacter transport

The degree is the constructed geometric residue degree of the actual field.
The isomorphism and its completion comparison are conclusions. Its inverse
lands only in the topological abelianization.
-/

noncomputable section

namespace Langlands.LocalClassField

universe u

/-- A candidate for the actual local Weil group has geometric order and
induces the explicitly normalized finite norm-residue system. -/
def GeometricWeilReciprocityRelation
    {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData)
    (e : WeilReciprocityCandidate T (Weil.Local.localResidueDegree F)) : Prop :=
  GeometricOrderRelation T (Weil.Local.localResidueDegree F) e ∧
    GeometricProfiniteReciprocityRelation F T
      (candidateGaloisHom T (Weil.Local.localResidueDegree F) e)

/-- For every finite p-adic field there is a unique geometrically normalized
topological isomorphism from its actual Weil abelianization to its units. -/
def WeilReciprocityExistenceUniqueness : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData),
    ∃! e : WeilReciprocityCandidate T (Weil.Local.localResidueDegree F),
      GeometricWeilReciprocityRelation F T e

/-- The Weil reciprocity isomorphism induces the unique comparison between
the actual multiplicative completion and the absolute-Galois abelianization. -/
def WeilReciprocityCompletion : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData)
    (e : WeilReciprocityCandidate T (Weil.Local.localResidueDegree F)),
    GeometricWeilReciprocityRelation F T e →
      ∃! c : LocalMultiplicative.profiniteCompletion T ≃ₜ* localAbelianGaloisGroup F,
        CompletionComparisonRelation T (Weil.Local.localResidueDegree F) e c

/-- The image of actual Weil inertia in the abelianization corresponds to
the actual valuation-unit subgroup. -/
def WeilReciprocityInertiaImage : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData)
    (e : WeilReciprocityCandidate T (Weil.Local.localResidueDegree F)),
    GeometricWeilReciprocityRelation F T e →
      (WeilQuotients.inertia (Weil.Local.localResidueDegree F)).map e.toMonoidHom =
        T.unitSubgroup

/-- Transport preserves unramifiedness and sends every complex unramified
Weil character to the corresponding integer-order character of field units. -/
def WeilReciprocityUnramifiedCharacters : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ e : WeilReciprocityCandidate T (Weil.Local.localResidueDegree F),
      GeometricWeilReciprocityRelation F T e →
        (∀ χ : Weil.Local.localWeilGroup F →ₜ* ℂˣ,
          (∀ w ∈ Weil.Local.localInertia F, χ w = 1) ↔
            T.IsUnramifiedQuasicharacter
              (weilCandidateCharacterEquiv T (Weil.Local.localResidueDegree F) e χ)) ∧
        ∀ (z : ℂˣ) (a : F.Carrierˣ),
          weilCandidateCharacterEquiv T (Weil.Local.localResidueDegree F) e
            (Weil.Local.localUnramifiedCharacter F z) a = z ^ T.ord (a : F.Carrier)

/-- Arbitrary unramified twists, including nonunitary and infinite-order
ones, transport through reciprocity with their specified degree-one value. -/
def WeilReciprocityUnramifiedTwists : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ e : WeilReciprocityCandidate T (Weil.Local.localResidueDegree F),
      GeometricWeilReciprocityRelation F T e →
        ∀ (χ : Weil.Local.localWeilGroup F →ₜ* ℂˣ) (z : ℂˣ) (a : F.Carrierˣ),
          weilCandidateCharacterEquiv T (Weil.Local.localResidueDegree F) e
            (χ * Weil.Local.localUnramifiedCharacter F z) a =
              weilCandidateCharacterEquiv T (Weil.Local.localResidueDegree F) e χ a *
                z ^ T.ord (a : F.Carrier)

/-- The actual Weil norm character transports to the actual normalized
absolute value, with geometric degree one giving the inverse residue size. -/
def WeilReciprocityNormCharacter : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ e : WeilReciprocityCandidate T (Weil.Local.localResidueDegree F),
      GeometricWeilReciprocityRelation F T e →
        ∀ a : F.Carrierˣ,
          (weilCandidateCharacterEquiv T (Weil.Local.localResidueDegree F) e
            (Weil.Local.localNormCharacter F) a : ℂ) =
              (T.normalizedAbs (a : F.Carrier) : ℂ)

/-- Actual local Weil reciprocity, its completion comparison, and the
unramified and norm-character transport needed by rank-one LLC. -/
def WeilReciprocityTheorems : Prop :=
  WeilReciprocityExistenceUniqueness.{u} ∧
    WeilReciprocityCompletion.{u} ∧
      WeilReciprocityInertiaImage.{u} ∧
        WeilReciprocityUnramifiedCharacters.{u} ∧
          WeilReciprocityUnramifiedTwists.{u} ∧
            WeilReciprocityNormCharacter.{u}

end Langlands.LocalClassField
