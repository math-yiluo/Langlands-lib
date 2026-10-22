import Langlands.WeilDeligne.Parameters
import Langlands.WeilDeligne.Restriction
import Langlands.WeilDeligne.Induction
import Langlands.WeilDeligne.SumsTensor
import Langlands.WeilDeligne.Dual
import Langlands.WeilDeligne.Twist
import Langlands.WeilDeligne.Kernels
import Langlands.WeilDeligne.FrobeniusStatements
import Mathlib.RepresentationTheory.FiniteIndex
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Restriction and induction of actual Weil–Deligne pairs

The companion's actual pair type and constructors are used throughout. Model
predicates specify the action and monodromy and do not supply an existence or
classification witness. These are proposition targets, not proofs.
-/

noncomputable section

namespace Langlands.WeilDeligneRepresentation

universe uG uH uV uU uT

variable {G : Type uG} {H : Type uH} [Group G] [Group H]

/-- An actual restriction model, via an actual intertwining equivalence.
This is a relation, not a chosen restriction constructor. -/
def IsRestrictionModel (φ : H →* G) (ν : G →* ℂˣ)
    (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (B : WeilDeligneRepresentation.{0, uH, uU} ℂ H (ν.comp φ))
    (e : Representation.Equiv (A.representation.comp φ) B.representation) : Prop :=
  e.toLinearMap ∘ₗ A.monodromy = B.monodromy ∘ₗ e.toLinearMap

/-- The exact norm-scaled monodromy on the actual induced coinvariant carrier.
The `ν(g)` factor matches Mathlib's action `[x ⊗ v] ↦ [x*g⁻¹ ⊗ v]`. -/
def IsInductionModel (S : Subgroup G) (ν : G →* ℂˣ)
    (A : WeilDeligneRepresentation.{0, uG, uV} ℂ S (ν.comp S.subtype))
    (B : WeilDeligneRepresentation.{0, uG, uU} ℂ G ν)
    (e : Representation.Equiv (A.representation.ind S.subtype) B.representation) : Prop :=
  ∀ (g : G) (v : A),
    B.monodromy (e (Representation.IndV.mk S.subtype A.representation g v)) =
      (ν g : ℂ) •
        e (Representation.IndV.mk S.subtype A.representation g (A.monodromy v))

/-- The companion's concrete restriction constructor realizes the model
through the identity map on its unchanged carrier. -/
def RestrictionConstructorCompatibility : Prop :=
  ∀ (G : Type uG) [Group G] (H : Type uH) [Group H]
    (φ : H →* G) (ν : G →* ℂˣ)
    (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν),
    IsRestrictionModel φ ν A (restrict φ A)
      (Representation.Equiv.refl (A.representation.comp φ))

/-- The companion's actual function-model induction realizes the coinvariant
model with the specified norm-scaled monodromy. The comparison is a conclusion. -/
def InductionConstructorCompatibility : Prop :=
  ∀ (G : Type uG) [Group G] (S : Subgroup G) [S.FiniteIndex]
    (ν : G →* ℂˣ)
    (A : WeilDeligneRepresentation.{0, uG, uV} ℂ S (ν.comp S.subtype)),
    ∃ e : Representation.Equiv (A.representation.ind S.subtype)
        (induce S A).representation,
      IsInductionModel S ν A (induce S A) e

/-- Restriction exists on the original carrier universe and is unique up to
actual pair isomorphism, including comparison across carrier universes. -/
def RestrictionModelsExistUniquely : Prop :=
  ∀ (G : Type uG) [Group G] (H : Type uH) [Group H]
    (φ : H →* G) (ν : G →* ℂˣ)
    (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν),
    (∃ B : WeilDeligneRepresentation.{0, uH, uV} ℂ H (ν.comp φ),
      ∃ e : Representation.Equiv (A.representation.comp φ) B.representation,
        IsRestrictionModel φ ν A B e) ∧
    ∀ (B : WeilDeligneRepresentation.{0, uH, uU} ℂ H (ν.comp φ))
      (C : WeilDeligneRepresentation.{0, uH, uT} ℂ H (ν.comp φ))
      (e : Representation.Equiv (A.representation.comp φ) B.representation)
      (f : Representation.Equiv (A.representation.comp φ) C.representation),
      IsRestrictionModel φ ν A B e → IsRestrictionModel φ ν A C f →
      Nonempty (Equiv B C)

/-- Finite-index induction exists on an actual finite-dimensional carrier and
is unique up to actual pair isomorphism. -/
def InductionModelsExistUniquely : Prop :=
  ∀ (G : Type uG) [Group G] (S : Subgroup G) [S.FiniteIndex]
    (ν : G →* ℂˣ)
    (A : WeilDeligneRepresentation.{0, uG, uV} ℂ S (ν.comp S.subtype)),
    (∃ B : WeilDeligneRepresentation.{0, uG, max uG uV} ℂ G ν,
      ∃ e : Representation.Equiv (A.representation.ind S.subtype) B.representation,
        IsInductionModel S ν A B e) ∧
    ∀ (B : WeilDeligneRepresentation.{0, uG, uU} ℂ G ν)
      (C : WeilDeligneRepresentation.{0, uG, uT} ℂ G ν)
      (e : Representation.Equiv (A.representation.ind S.subtype) B.representation)
      (f : Representation.Equiv (A.representation.ind S.subtype) C.representation),
      IsInductionModel S ν A B e → IsInductionModel S ν A C f →
      Nonempty (Equiv B C)

/-- Restriction invariants and its parameter/topology consequences. -/
def RestrictionModelConsequences : Prop :=
  ∀ (G : Type uG) [Group G] (H : Type uH) [Group H]
    (φ : H →* G) (ν : G →* ℂˣ)
    (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (B : WeilDeligneRepresentation.{0, uH, uU} ℂ H (ν.comp φ))
    (e : Representation.Equiv (A.representation.comp φ) B.representation),
    IsRestrictionModel φ ν A B e →
    B.rank = A.rank ∧
    (∀ n : ℕ,
      Module.finrank ℂ (LinearMap.ker (B.monodromy ^ n)) =
        Module.finrank ℂ (LinearMap.ker (A.monodromy ^ n)) ∧
      Module.finrank ℂ (LinearMap.range (B.monodromy ^ n)) =
        Module.finrank ℂ (LinearMap.range (A.monodromy ^ n))) ∧
    (B.monodromy = 0 ↔ A.monodromy = 0) ∧
    (∀ d : G →* Multiplicative ℤ,
      A.IsFrobeniusSemisimple d → B.IsFrobeniusSemisimple (d.comp φ)) ∧
    (∀ h : H, LinearMap.det (B.representation h) = LinearMap.det (A.representation (φ h))) ∧
    ∀ [TopologicalSpace G] [TopologicalSpace H],
      Continuous φ →
      (A.IsContinuous → B.IsContinuous) ∧
      ∀ (I : Subgroup G) (J : Subgroup H), J ≤ I.comap φ →
        (IsParameter I A → IsParameter J B)

/-- Induction multiplies the dimension of every monodromy kernel/image by the
subgroup index; Frobenius semisimplicity is preserved and reflected. -/
def InductionModelConsequences : Prop :=
  ∀ (G : Type uG) [Group G] (S : Subgroup G) [S.FiniteIndex]
    (ν : G →* ℂˣ)
    (A : WeilDeligneRepresentation.{0, uG, uV} ℂ S (ν.comp S.subtype))
    (B : WeilDeligneRepresentation.{0, uG, uU} ℂ G ν)
    (e : Representation.Equiv (A.representation.ind S.subtype) B.representation),
    IsInductionModel S ν A B e →
    B.rank = S.index * A.rank ∧
    (∀ n : ℕ,
      Module.finrank ℂ (LinearMap.ker (B.monodromy ^ n)) =
        S.index * Module.finrank ℂ (LinearMap.ker (A.monodromy ^ n)) ∧
      Module.finrank ℂ (LinearMap.range (B.monodromy ^ n)) =
        S.index * Module.finrank ℂ (LinearMap.range (A.monodromy ^ n))) ∧
    (B.monodromy = 0 ↔ A.monodromy = 0) ∧
    (∀ d : G →* Multiplicative ℤ,
      B.IsFrobeniusSemisimple d ↔ A.IsFrobeniusSemisimple (d.comp S.subtype)) ∧
    ∀ [TopologicalSpace G] [IsTopologicalGroup G], IsOpen (S : Set G) →
      (B.IsContinuous ↔ A.IsContinuous) ∧
      ∀ (I : Subgroup G) [I.Normal],
        IsParameter I B ↔ IsParameter (I.comap S.subtype) A

/-- Frobenius reciprocity for actual pair morphisms with a prescribed value
on the generator inclusion. The monodromy compatibility is explicit. -/
def InductionModelReciprocity : Prop :=
  ∀ (G : Type uG) [Group G] (S : Subgroup G) [S.FiniteIndex]
    (ν : G →* ℂˣ)
    (A : WeilDeligneRepresentation.{0, uG, uV} ℂ S (ν.comp S.subtype))
    (B : WeilDeligneRepresentation.{0, uG, uU} ℂ G ν)
    (C : WeilDeligneRepresentation.{0, uG, uT} ℂ G ν)
    (e : Representation.Equiv (A.representation.ind S.subtype) B.representation),
    IsInductionModel S ν A B e →
    ∀ f : A.representation.IntertwiningMap (C.representation.comp S.subtype),
      f.toLinearMap ∘ₗ A.monodromy = C.monodromy ∘ₗ f.toLinearMap →
      ∃! F : Hom B C,
        ∀ v : A, F.intertwiner (e (Representation.IndV.mk S.subtype A.representation 1 v)) =
          f v

/-- Restriction commutes with the actual sum, tensor, dual, character twist,
monodromy-kernel and zero-monodromy constructors. -/
def RestrictionOperationCompatibility : Prop :=
  ∀ (G : Type uG) [Group G] (H : Type uH) [Group H]
    (φ : H →* G) (ν : G →* ℂˣ)
    (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (B : WeilDeligneRepresentation.{0, uG, uU} ℂ G ν) (χ : G →* ℂˣ),
    Nonempty (Equiv (restrict φ (sum A B)) (sum (restrict φ A) (restrict φ B))) ∧
    Nonempty (Equiv (restrict φ (tensor A B)) (tensor (restrict φ A) (restrict φ B))) ∧
    Nonempty (Equiv (restrict φ (dual A)) (dual (restrict φ A))) ∧
    Nonempty (Equiv (restrict φ (twist χ A)) (twist (χ.comp φ) (restrict φ A))) ∧
    Nonempty (FiniteRepresentation.Equiv (kernelRepresentation (restrict φ A))
      (FiniteRepresentation.restrict φ A.kernelRepresentation)) ∧
    Nonempty (Equiv (restrict φ (zeroMonodromy ν A.toFiniteRepresentation))
      (zeroMonodromy (ν.comp φ) (FiniteRepresentation.restrict φ A.toFiniteRepresentation)))

/-- Finite-index induction commutes with sums, duals, twists and kernels and
satisfies the tensor projection formula, all for the actual constructors. -/
def InductionOperationCompatibility : Prop :=
  ∀ (G : Type uG) [Group G] (S : Subgroup G) [S.FiniteIndex] (ν : G →* ℂˣ)
    (A : WeilDeligneRepresentation.{0, uG, uV} ℂ S (ν.comp S.subtype))
    (B : WeilDeligneRepresentation.{0, uG, uU} ℂ S (ν.comp S.subtype))
    (C : WeilDeligneRepresentation.{0, uG, uT} ℂ G ν) (χ : G →* ℂˣ),
    Nonempty (Equiv (induce S (sum A B)) (sum (induce S A) (induce S B))) ∧
    Nonempty (Equiv (induce S (tensor A (restrict S.subtype C)))
      (tensor (induce S A) C)) ∧
    Nonempty (Equiv (induce S (dual A)) (dual (induce S A))) ∧
    Nonempty (Equiv (induce S (twist (χ.comp S.subtype) A)) (twist χ (induce S A))) ∧
    Nonempty (FiniteRepresentation.Equiv (kernelRepresentation (induce S A))
      (FiniteRepresentation.induce S A.kernelRepresentation)) ∧
    Nonempty (Equiv (induce S (zeroMonodromy (ν.comp S.subtype) A.toFiniteRepresentation))
      (zeroMonodromy ν (FiniteRepresentation.induce S A.toFiniteRepresentation))) ∧
    (Nonempty (Equiv A B) → Nonempty (Equiv (induce S A) (induce S B)))

/-- Induction in a finite-index subgroup tower uses the actual subgroup
identification, restriction and iterated induction constructors. -/
def InductionTransitivity : Prop :=
  ∀ (G : Type uG) [Group G] (S T : Subgroup G) [S.FiniteIndex] [T.FiniteIndex]
    (h : S ≤ T) (ν : G →* ℂˣ)
    (A : WeilDeligneRepresentation.{0, uG, uV} ℂ S (ν.comp S.subtype)),
    Nonempty (Equiv
      (induce T (induce (S.subgroupOf T)
        (restrict (Subgroup.subgroupOfEquivOfLe h).toMonoidHom A)))
      (induce S A))

/-- Positive rescaling of integer degree leaves the actual semisimplification
relation unchanged. This is needed when a field extension has residue degree
greater than one; it is not a chosen correction or a classification hypothesis. -/
def SemisimplificationDegreeRescaling : Prop :=
  ∀ (G : Type uG) [Group G] (ν : G →* ℂˣ)
    (d : G →* Multiplicative ℤ) (n : ℕ), 0 < n →
    ∀ (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
      (B : WeilDeligneRepresentation.{0, uG, uU} ℂ G ν),
      Frobenius.IsSemisimplification (d ^ n) A B ↔
        Frobenius.IsSemisimplification d A B

/-- Restriction transports an actual semisimplification to the actual restricted
pairs, using the pulled-back degree. Existence is not assumed in a data field. -/
def RestrictionSemisimplificationCompatibility : Prop :=
  ∀ (G : Type uG) [Group G] (H : Type uH) [Group H]
    (φ : H →* G) (ν : G →* ℂˣ) (d : G →* Multiplicative ℤ)
    (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (B : WeilDeligneRepresentation.{0, uG, uU} ℂ G ν),
    Frobenius.IsSemisimplification d A B →
      Frobenius.IsSemisimplification (d.comp φ) (restrict φ A) (restrict φ B)

/-- Finite-index induction transports the actual semisimplification relation.
The source degree is the pullback of the ambient degree, which need not be
surjective. Positive degree rescaling is a separate quantified statement. -/
def InductionSemisimplificationCompatibility : Prop :=
  ∀ (G : Type uG) [Group G] (S : Subgroup G) [S.FiniteIndex]
    (ν : G →* ℂˣ) (d : G →* Multiplicative ℤ)
    (A : WeilDeligneRepresentation.{0, uG, uV} ℂ S (ν.comp S.subtype))
    (B : WeilDeligneRepresentation.{0, uG, uU} ℂ S (ν.comp S.subtype)),
    Frobenius.IsSemisimplification (d.comp S.subtype) A B →
      Frobenius.IsSemisimplification d (induce S A) (induce S B)

/-- The complete restriction/induction statement family for actual Weil–Deligne
pairs, with five independent universes. -/
def RestrictionInductionStatements : Prop :=
  RestrictionConstructorCompatibility.{uG, uH, uV} ∧
  InductionConstructorCompatibility.{uG, uV} ∧
  RestrictionModelsExistUniquely.{uG, uH, uV, uU, uT} ∧
  InductionModelsExistUniquely.{uG, uV, uU, uT} ∧
  RestrictionModelConsequences.{uG, uH, uV, uU} ∧
  InductionModelConsequences.{uG, uV, uU} ∧
  InductionModelReciprocity.{uG, uV, uU, uT} ∧
  RestrictionOperationCompatibility.{uG, uH, uV, uU} ∧
  InductionOperationCompatibility.{uG, uV, uU, uT} ∧
  InductionTransitivity.{uG, uV} ∧
  SemisimplificationDegreeRescaling.{uG, uV, uU} ∧
  RestrictionSemisimplificationCompatibility.{uG, uH, uV, uU} ∧
  InductionSemisimplificationCompatibility.{uG, uV, uU}

end Langlands.WeilDeligneRepresentation
