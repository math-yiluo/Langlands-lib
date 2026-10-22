import Langlands.ClassFieldTheory.Local.Units
import Langlands.ClassFieldTheory.Local.Completion
import Langlands.ClassFieldTheory.Local.FiniteArtin
import Langlands.ClassFieldTheory.Local.WeilAbelianization
import Langlands.ClassFieldTheory.Local.Transfer

/-!
# Relations on local reciprocity candidates

All groups, norm images, quotients and comparison maps in these predicates
are the actual preceding constructions. No candidate or existence proof is
provided, and no canonical reciprocity map is chosen.
-/

noncomputable section

namespace Langlands.LocalClassField

universe u

section Local

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p}
  (T : F.TopologicalData)
  (φ : Field.absoluteGaloisGroup F.Carrier →ₜ* Weil.ProfiniteIntegers)

/-- The type of candidate continuous reciprocity isomorphisms, in the
direction from the topological Weil abelianization to field units.
This type is not asserted to be inhabited. -/
abbrev WeilReciprocityCandidate :=
  letI := T.topology
  WeilQuotients.Abelianization φ ≃ₜ* F.Carrierˣ

/-- A specified Weil candidate induces a continuous homomorphism into the
actual absolute-Galois abelianization. Its inverse is used only on the
Weil abelianization, never on the nonabelian Weil group. -/
def candidateGaloisHom (e : WeilReciprocityCandidate T φ) :
    letI := T.topology
    F.Carrierˣ →ₜ* Field.absoluteGaloisGroupAbelianization F.Carrier := by
  letI := T.topology
  exact (WeilQuotients.toGroupAbelianization φ).comp
    (e.symm : F.Carrierˣ →ₜ* WeilQuotients.Abelianization φ)

/-- The plus-sign order normalization for geometric Frobenius of degree
`+1`: order after the candidate equals descended degree. -/
def GeometricOrderRelation (e : WeilReciprocityCandidate T φ) : Prop :=
  T.orderHom.comp e.toMonoidHom = (WeilQuotients.degree φ).toMonoidHom

/-- Local conditions on a candidate: geometric order normalization, density
in the actual Galois abelianization, and all finite norm-residue relations.
These local conditions do not assert cross-field uniqueness. -/
def LocalReciprocityCandidateRelation (e : WeilReciprocityCandidate T φ) : Prop :=
  letI := T.topology
  GeometricOrderRelation T φ e ∧
    ProfiniteNormResidueRelation (candidateGaloisHom T φ e)

/-- The comparison diagram between the actual continuous profinite
completion of field units and the actual Galois abelianization. This
is a predicate on a specified comparison isomorphism, not its constructor. -/
def CompletionComparisonRelation (e : WeilReciprocityCandidate T φ)
    (c : LocalMultiplicative.profiniteCompletion T ≃ₜ* localAbelianGaloisGroup F) :
    Prop :=
  letI := T.topology
  (c : LocalMultiplicative.profiniteCompletion T →ₜ* localAbelianGaloisGroup F).comp
    (LocalMultiplicative.completionMap T) = candidateGaloisHom T φ e

/-- The precise local existence property on these objects. It is a proposition
definition, not a theorem or a source of a chosen reciprocity map. Its intended
application requires the actual geometric residue-degree map `φ`. -/
def LocalReciprocityExistence : Prop :=
  ∃ e : WeilReciprocityCandidate T φ,
    LocalReciprocityCandidateRelation T φ e ∧
      ∃ c : LocalMultiplicative.profiniteCompletion T ≃ₜ* localAbelianGaloisGroup F,
        CompletionComparisonRelation T φ e c

/-- Conditional transport of complex quasicharacters along a given Weil
candidate. The first step is genuine abelianization descent, and the second
uses the given abelianized equivalence. -/
def weilCandidateCharacterEquiv (e : WeilReciprocityCandidate T φ) :
    letI := T.topology
    (Weil.Pullback φ →ₜ* ℂˣ) ≃ (F.Carrierˣ →ₜ* ℂˣ) := by
  letI := T.topology
  exact (WeilQuotients.characterDescent φ).trans (characterTransport e)

end Local

section Relative

variable (K : Type u) [Field K] [PerfectField K]
  (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E]

/-- The norm square on candidate maps into actual Galois abelianizations
in the common closure. The field norm and subgroup inclusion are constructed. -/
def AbsoluteNormRelation
    (aK : Kˣ →* Field.absoluteGaloisGroupAbelianization K)
    (aE : Eˣ →* TopologicalAbelianization E.fixingSubgroup) : Prop :=
  aK.comp (normUnits K E) =
    (absoluteFixingAbelianInclusion K E).toMonoidHom.comp aE

/-- The field-inclusion/transfer square on the same actual groups.
The transfer is the constructed continuous finite-index transfer. -/
def AbsoluteTransferRelation
    (aK : Kˣ →* Field.absoluteGaloisGroupAbelianization K)
    (aE : Eˣ →* TopologicalAbelianization E.fixingSubgroup) : Prop :=
  aE.comp (Units.map (algebraMap K E).toMonoidHom) =
    (absoluteTransferToFixing K E).toMonoidHom.comp aK

variable (φ : Field.absoluteGaloisGroup K →ₜ* Weil.ProfiniteIntegers)

/-- The norm square in the forward Weil-to-units direction, using the
actual subgroup fixing `E` inside the existing pullback. -/
def WeilNormRelation
    (tK : TopologicalAbelianization (Weil.Pullback φ) →* Kˣ)
    (tE : TopologicalAbelianization (pullbackFixingSubgroup K E φ) →* Eˣ) : Prop :=
  tK.comp (pullbackFixingAbelianInclusion K E φ).toMonoidHom =
    (normUnits K E).comp tE

/-- The opposite transfer square in the forward Weil-to-units direction. -/
def WeilTransferRelation
    (tK : TopologicalAbelianization (Weil.Pullback φ) →* Kˣ)
    (tE : TopologicalAbelianization (pullbackFixingSubgroup K E φ) →* Eˣ) : Prop :=
  tE.comp (pullbackTransferToFixing K E φ).toMonoidHom =
    (Units.map (algebraMap K E).toMonoidHom).comp tK

/-- Both cross-field squares, as a relation on specified candidate maps.
It asserts no existence, uniqueness or independence of closure presentation. -/
def RelativeWeilReciprocityRelation
    (tK : TopologicalAbelianization (Weil.Pullback φ) →* Kˣ)
    (tE : TopologicalAbelianization (pullbackFixingSubgroup K E φ) →* Eˣ) : Prop :=
  WeilNormRelation K E φ tK tE ∧ WeilTransferRelation K E φ tK tE

end Relative

end Langlands.LocalClassField
