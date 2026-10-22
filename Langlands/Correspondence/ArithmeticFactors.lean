import Langlands.Correspondence.OperationCompatibility
import Langlands.Correspondence.LocalConventions
import Langlands.LocalFactor.CommonClosureGamma
import Langlands.WeilDeligne.Restriction
import Langlands.Representation.RankinSelberg.FunctionalEquationStatement

/-!
# Arithmetic pair factors on the correspondence domains

Pair L-factors are evaluated on the actual local Weil group. Pair epsilon values
come from a supplied common-closure local-constant system at the bottom
intermediate field. No system, additive character or measure is chosen.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uV

open Weil.Local LocalFactor LocalFactor.CommonClosure LocalFactor.CommonClosureWeilDeligne

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

/-- All genuine pair classes of the actual local Weil group, of every rank. -/
abbrev LocalPairClass :=
  WeilDeligneRepresentation.IsomorphismClasses.{0, uF, uP} ℂ (localWeilGroup F)
    (localNormCharacter F).toMonoidHom

/-- The zero-monodromy pair class of a continuous irreducible Weil class.
Representation equivalences give pair equivalences through the actual functor. -/
def weilPairClass {n : ℕ+} (σ : IrreducibleWeilClass.{uF, uP} F n) :
    LocalPairClass.{uF, uP} F :=
  Quotient.map (sa := FiniteRepresentation.isomorphismSetoid)
    (sb := WeilDeligneRepresentation.isomorphismSetoid)
    (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter F).toMonoidHom)
    (fun (A B : LocalWeilRepresentation.{uF, uP} F) (h : FiniteRepresentation.IsIsomorphic A B) =>
      (h.map fun e : FiniteRepresentation.Equiv A B =>
        WeilDeligneRepresentation.Equiv.ofIso
          ((localZeroMonodromyFunctor F).mapIso (FiniteRepresentation.isoOfEquiv e)) :
        WeilDeligneRepresentation.IsIsomorphic _ _))
    (weilClassForget F σ)

/-- The arithmetic pair L-factor `L(s, X ⊗ Y)` as a rational function of
`X = q^(-s)`: the Euler factor of the actual tensor on `(ker N)^I`, at the
published geometric Frobenius lift. -/
def arithmeticPairLFactor (X : LocalPairClass.{uF, uP} F) (Y : LocalPairClass.{uF, uP} F) :
    RatFunc ℂ :=
  WeilDeligne.pairLFactorClass (localInertia F) (localGeometricFrobenius F) X Y

/-- The base field as the bottom finite intermediate field of its closure. -/
def baseExtension : Extension F :=
  ⟨⊥, inferInstance⟩

/-- `A` is a common-closure pair over the bottom field that is equivalent to the
restriction of a representative of `X`. The norm characters agree by definition. -/
def IsBaseRestriction (X : LocalPairClass.{uF, uP} F)
    (A : Pair.{uF, uV} F (baseExtension F)) : Prop :=
  ∃ B : LocalWeilDeligneRepresentation.{uF, uP} F,
    WeilDeligneRepresentation.classOf B = X ∧
      Nonempty (WeilDeligneRepresentation.Equiv
        (WeilDeligneRepresentation.restrict (weilSubgroup F (baseExtension F)).subtype B) A)

/-- The bottom-field character corresponding to `ψ` under the actual field
isomorphism `⊥ ≃ F`. -/
def IsBaseCharacter (ψ : NontrivialAdditiveCharacter F)
    (ψ' : AdditiveCharacter F (baseExtension F)) : Prop :=
  letI := (fieldData F (baseExtension F)).topology
  ∀ x : (baseExtension F).field,
    ψ'.toAddChar x =
      ψ.toAddChar (IntermediateField.botEquiv F.Carrier (AlgebraicClosure F.Carrier) x)

/-- The bottom component of a common-closure reciprocity family agrees with a
candidate for the base field, through the same field isomorphism. -/
def IsBaseReciprocity (e : ReciprocityCandidate F) (eC : ReciprocityFamily F) : Prop :=
  letI := (fieldData F (baseExtension F)).topology
  ∀ w : weilSubgroup F (baseExtension F),
    ((IntermediateField.botEquiv F.Carrier (AlgebraicClosure F.Carrier)
        (reciprocityUnits F eC (baseExtension F) w : (baseExtension F).field)) : F.Carrier) =
      ((RankOne.reciprocityUnits F e w.val : F.Carrierˣ) : F.Carrier)

/-- Admissible bottom-field data for the pair `(X, Y)` and the base character `ψ`:
the transported character, a self-dual measure for it, and transported pairs. -/
def IsBaseEpsilonDatum (ψ : NontrivialAdditiveCharacter F)
    (X Y : LocalPairClass.{uF, uP} F) (ψ' : AdditiveCharacter F (baseExtension F))
    (μ : HaarMeasure F (baseExtension F)) (A B : Pair.{uF, uV} F (baseExtension F)) : Prop :=
  IsBaseCharacter F ψ ψ' ∧ CommonClosureSpectral.IsSelfDual F (baseExtension F) ψ' μ ∧
    IsBaseRestriction F X A ∧ IsBaseRestriction F Y B

/-- The arithmetic pair epsilon factor `ε(s, X ⊗ Y, ψ)` is `c q^(-ms)` for the
supplied system: admissible continuous data and a geometric Frobenius over the
bottom field exist, and every admissible choice gives this value at every `s`. -/
def IsArithmeticPairEpsilonFactor (eC : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F eC ε)
    (ψ : NontrivialAdditiveCharacter F) (X Y : LocalPairClass.{uF, uP} F)
    (c : ℂˣ) (m : ℤ) : Prop :=
  (∃ (ψ' : AdditiveCharacter F (baseExtension F)) (μ : HaarMeasure F (baseExtension F))
      (A B : Pair.{uF, uV} F (baseExtension F)),
    IsBaseEpsilonDatum F ψ X Y ψ' μ A B ∧
      A.toFiniteRepresentation.IsContinuous ∧ B.toFiniteRepresentation.IsContinuous) ∧
  Nonempty (GeometricFrobenius F (baseExtension F)) ∧
  ∀ (ψ' : AdditiveCharacter F (baseExtension F)) (μ : HaarMeasure F (baseExtension F))
    (A B : Pair.{uF, uV} F (baseExtension F)),
    IsBaseEpsilonDatum F ψ X Y ψ' μ A B →
    ∀ (hA : A.toFiniteRepresentation.IsContinuous) (hB : B.toFiniteRepresentation.IsContinuous)
      (Φ : GeometricFrobenius F (baseExtension F)) (s : ℂ),
      (CommonClosureGamma.conditionalPairEpsilonValue F eC ε hε (baseExtension F) ψ' μ
          A B hA hB Φ s : ℂ) =
        RankinSelberg.epsilonMonomial F.canonicalTopologicalData.residueCardinality c m s

end Langlands.Correspondence
