import Langlands.Correspondence.Domains
import Langlands.Weil.Representation.Determinant
import Langlands.Weil.Representation.DualClasses
import Langlands.Weil.Representation.TwistClasses
import Langlands.ClassFieldTheory.Local.WeilReciprocityStatement
import Langlands.LocalFactor.RankOne

/-!
# Character, determinant, twist and dual compatibility conditions

Every condition is taken along a specified candidate for local Weil
reciprocity. The geometric normalization is the published relation
`IsGeometricReciprocity`. The final LLC predicate must quantify both.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

/-- Topological isomorphisms from the actual Weil abelianization to field units. -/
abbrev ReciprocityCandidate := LocalFactor.RankOne.ReciprocityCandidate F

/-- The published geometric normalization for the canonical topology. -/
abbrev IsGeometricReciprocity (e : ReciprocityCandidate F) : Prop :=
  LocalClassField.GeometricWeilReciprocityRelation F F.canonicalTopologicalData e

/-- The actual abelianization projection followed by the candidate. -/
def reciprocityHom (e : ReciprocityCandidate F) :
    Weil.Local.localWeilGroup F →* F.Carrierˣ :=
  (LocalFactor.RankOne.reciprocityUnits F e).toMonoidHom

/-- A field quasi-character pulled back to the actual local Weil group. -/
def weilCharacter (e : ReciprocityCandidate F) (χ : QuasiCharacter F) :
    Weil.Local.localWeilGroup F →* ℂˣ :=
  (LocalFactor.RankOne.weilCharacter F e χ).toMonoidHom

/-- The pullback is the inverse of the published character transport. -/
theorem weilCharacter_eq_symm (e : ReciprocityCandidate F) (χ : QuasiCharacter F) :
    weilCharacter F e χ =
      ((LocalClassField.weilCandidateCharacterEquiv F.canonicalTopologicalData
        (Weil.Local.localResidueDegree F) e).symm χ).toMonoidHom :=
  rfl

/-- The pullback is precomposition with the reciprocity homomorphism. -/
theorem weilCharacter_eq_comp (e : ReciprocityCandidate F) (χ : QuasiCharacter F) :
    weilCharacter F e χ = χ.toMonoidHom.comp (reciprocityHom F e) :=
  rfl

/-- The determinant Weil character descends through actual pair isomorphisms. -/
def parameterDeterminant {n : ℕ+} (D : WeilDeligneClass.{uF, uP} F n) :
    Weil.Local.localWeilGroup F →* ℂˣ :=
  Quotient.lift
    (s := WeilDeligneRepresentation.frobeniusSemisimpleParameterSetoid
      (Weil.Local.localInertia F) (Weil.Local.localDegree F).toMonoidHom)
    (fun A : {A : Weil.Local.LocalWeilDeligneRepresentation.{uF, uP} F //
        Weil.Local.IsLocalFrobeniusSemisimpleParameter F A} =>
      FiniteRepresentation.determinantCharacter A.val.toFiniteRepresentation)
    (fun _ _ ⟨e⟩ => FiniteRepresentation.determinantCharacter_eq e.representationEquiv)
    D.val

/-- Determinant of a continuous irreducible Weil class, using genuine quotient descent. -/
def irreducibleWeilDeterminant {n : ℕ+} (σ : IrreducibleWeilClass.{uF, uP} F n) :
    Weil.Local.localWeilGroup F →* ℂˣ :=
  FiniteRepresentation.determinantCharacterClass (weilClassForget F σ)

/-- A rank-one full parameter class is the actual scalar character with zero monodromy.
The pair equivalence permits the independent parameter-carrier universe. -/
def IsRankOneParameterCharacter (χ : Weil.Local.localWeilGroup F →* ℂˣ)
    (D : WeilDeligneClass.{uF, uP} F 1) : Prop :=
  ∃ A : Weil.Local.LocalWeilDeligneRepresentation.{uF, uP} F,
    WeilDeligneRepresentation.classOf A = parameterForget F D ∧
    Nonempty (WeilDeligneRepresentation.Equiv
      (WeilDeligneRepresentation.zeroMonodromy
        (Weil.Local.localNormCharacter F).toMonoidHom
        (FiniteRepresentation.of (Langlands.characterRepresentation χ))) A)

/-- A rank-one irreducible Weil class is the actual scalar character. -/
def IsRankOneWeilCharacter (χ : Weil.Local.localWeilGroup F →* ℂˣ)
    (σ : IrreducibleWeilClass.{uF, uP} F 1) : Prop :=
  ∃ A : Weil.Local.LocalWeilRepresentation.{uF, uP} F,
    FiniteRepresentation.classOf A = weilClassForget F σ ∧
    Nonempty ((Langlands.characterRepresentation χ).Equiv A.representation)

/-- Rank-one compatibility along a reciprocity candidate.
Existence of each rank-one parameter class is required, not assumed. -/
def RankOneCompatibility (e : ReciprocityCandidate F)
    (c : FullMap.{uF, uP, uA} F) : Prop :=
  ∀ χ : QuasiCharacter F, ∃ D : WeilDeligneClass.{uF, uP} F 1,
    IsRankOneParameterCharacter F (weilCharacter F e χ) D ∧
      IsRankOneCharacter F χ (c 1 D)

/-- The scalar matrix at the reciprocity image of `w` acts by the determinant at `w`. -/
def DeterminantCompatibility (e : ReciprocityCandidate F)
    (c : FullMap.{uF, uP, uA} F) : Prop :=
  ∀ n D (w : Weil.Local.localWeilGroup F),
    CentralActsBy F (c n D) (reciprocityHom F e w) (parameterDeterminant F D w)

/-- Twisting by the pulled-back character matches twisting by `χ ∘ det`.
The twisted parameter class is required to exist. -/
def TwistCompatibility (e : ReciprocityCandidate F)
    (c : FullMap.{uF, uP, uA} F) : Prop :=
  ∀ n (D : WeilDeligneClass.{uF, uP} F n) (χ : QuasiCharacter F),
    ∃ E : WeilDeligneClass.{uF, uP} F n,
      WeilDeligneRepresentation.ParameterRelations.IsTwistOf (weilCharacter F e χ) D E ∧
        IsCharacterTwist F χ (c n D) (c n E)

/-- The dual parameter class matches the smooth contragredient.
The dual parameter class is required to exist. -/
def DualCompatibility (c : FullMap.{uF, uP, uA} F) : Prop :=
  ∀ n (D : WeilDeligneClass.{uF, uP} F n), ∃ E : WeilDeligneClass.{uF, uP} F n,
    WeilDeligneRepresentation.ParameterRelations.IsDualOf D E ∧
      IsSmoothDual F (c n D) (c n E)

/-- The separate irreducible-Weil/supercuspidal rank-one condition. -/
def SupercuspidalRankOneCompatibility (e : ReciprocityCandidate F)
    (c : SupercuspidalMap.{uF, uP, uA} F) : Prop :=
  ∀ χ : QuasiCharacter F, ∃ σ : IrreducibleWeilClass.{uF, uP} F 1,
    IsRankOneWeilCharacter F (weilCharacter F e χ) σ ∧
      IsSupercuspidalRankOneCharacter F χ (c 1 σ)

/-- Determinant and central action on the supercuspidal family. -/
def SupercuspidalDeterminantCompatibility (e : ReciprocityCandidate F)
    (c : SupercuspidalMap.{uF, uP, uA} F) : Prop :=
  ∀ n σ (w : Weil.Local.localWeilGroup F),
    SupercuspidalCentralActsBy F (c n σ) (reciprocityHom F e w)
      (irreducibleWeilDeterminant F σ w)

/-- Twist compatibility on the supercuspidal family. The Weil-side output is the
published certified twist of the continuous irreducible class. -/
def SupercuspidalTwistCompatibility (e : ReciprocityCandidate F)
    (c : SupercuspidalMap.{uF, uP, uA} F) : Prop :=
  ∀ n (σ : IrreducibleWeilClass.{uF, uP} F n) (χ : QuasiCharacter F),
    IsSupercuspidalCharacterTwist F χ (c n σ)
      (c n (FiniteRepresentation.continuousIrreducibleTwistEquiv
        (LocalFactor.RankOne.weilCharacter F e χ) (n : ℕ) σ))

/-- Dual compatibility on the supercuspidal family. The Weil-side output is the
published certified dual of the continuous irreducible class. -/
def SupercuspidalDualCompatibility (c : SupercuspidalMap.{uF, uP, uA} F) : Prop :=
  ∀ n (σ : IrreducibleWeilClass.{uF, uP} F n),
    IsSupercuspidalSmoothDual F (c n σ)
      (c n (FiniteRepresentation.continuousIrreducibleDualEquiv (n : ℕ) σ))

end Langlands.Correspondence
