import Langlands.LocalFactor.Ramification.Herbrand.KummerTowerStatement
import Langlands.LocalFactor.Ramification.Herbrand.WeilRestrictionProof
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Truncation quotients and restriction of Weil representations

The supporting predicates describe filtered topological group isomorphisms
induced by the existing intermediate-field maps. The eight proposition
definitions state the quotient and representation parts of truncation and
their finite Kummer-stage consequences. No truncation assertion is proved here.
-/

noncomputable section

namespace Langlands.Ramification.Kummer

open LocalClassField HerbrandBridge Weil.Local
open _root_.Langlands.Ramification.Padic
open VirtualRepresentation.LocalWeil.Ramification

universe u v

section Definitions

variable {p : ℕ} [Fact p.Prime]

/-- Normality of the existing Weil upper group, pulled back from the absolute
upper group. This instance is local to this module. -/
local instance (F : PadicField.{u} p) (x : ℝ) : (upperGroup F x).Normal :=
  Subgroup.Normal.comap inferInstance _

/-- A filtered topological quotient isomorphism induced by the specified
continuous homomorphism of absolute Galois groups. -/
def GaloisQuotientIsoAlong (K F : PadicField.{u} p)
    (ι : Field.absoluteGaloisGroup K.Carrier →ₜ* Field.absoluteGaloisGroup F.Carrier)
    (x : ℝ) : Prop :=
  ∃ φ : (Field.absoluteGaloisGroup K.Carrier ⧸ absoluteUpperRamificationGroup K x) ≃ₜ*
      (Field.absoluteGaloisGroup F.Carrier ⧸ absoluteUpperRamificationGroup F x),
    (∀ τ : Field.absoluteGaloisGroup K.Carrier,
      φ (QuotientGroup.mk τ) = QuotientGroup.mk (ι τ)) ∧
    ∀ y : ℝ, -1 ≤ y → y ≤ x →
      φ '' ((QuotientGroup.mk :
        Field.absoluteGaloisGroup K.Carrier →
          Field.absoluteGaloisGroup K.Carrier ⧸ absoluteUpperRamificationGroup K x) ''
        (absoluteUpperRamificationGroup K y : Set (Field.absoluteGaloisGroup K.Carrier))) =
      (QuotientGroup.mk :
        Field.absoluteGaloisGroup F.Carrier →
          Field.absoluteGaloisGroup F.Carrier ⧸ absoluteUpperRamificationGroup F x) ''
        (absoluteUpperRamificationGroup F y : Set (Field.absoluteGaloisGroup F.Carrier))

/-- A filtered topological quotient isomorphism induced by the specified
continuous homomorphism of local Weil groups. -/
def WeilQuotientIsoAlong (K F : PadicField.{u} p)
    (ι : localWeilGroup K →ₜ* localWeilGroup F) (x : ℝ) : Prop :=
  ∃ φ : (localWeilGroup K ⧸ upperGroup K x) ≃ₜ*
      (localWeilGroup F ⧸ upperGroup F x),
    (∀ w : localWeilGroup K,
      φ (QuotientGroup.mk w) = QuotientGroup.mk (ι w)) ∧
    ∀ y : ℝ, -1 ≤ y → y ≤ x →
      φ '' ((QuotientGroup.mk : localWeilGroup K → localWeilGroup K ⧸ upperGroup K x) ''
        (upperGroup K y : Set (localWeilGroup K))) =
      (QuotientGroup.mk : localWeilGroup F → localWeilGroup F ⧸ upperGroup F x) ''
        (upperGroup F y : Set (localWeilGroup F))

/-- The Galois quotient comparison along the Library's intermediate-field map. -/
def GaloisTruncationIsoAt (F : PadicField.{u} p)
    (E : FiniteIntermediateExtension F.Carrier) (x : ℝ) : Prop :=
  GaloisQuotientIsoAlong (E.asPadicField (p := p)) F (intermediateGaloisMap F E) x

/-- The Weil quotient comparison along the Library's intermediate-field map. -/
def WeilTruncationIsoAt (F : PadicField.{u} p)
    (E : FiniteIntermediateExtension F.Carrier) (x : ℝ) : Prop :=
  WeilQuotientIsoAlong (E.asPadicField (p := p)) F (intermediateWeilMap F E) x

/-- Isomorphism classes having a continuous representative trivial on the
actual Weil upper group of index `μ`. -/
def truncatedWeilClasses (F : PadicField.{u} p) (μ : ℝ) :
    Set (FiniteRepresentation.IsomorphismClasses.{0, u, v} ℂ (localWeilGroup F)) :=
  {c | ∃ A : FiniteRepresentation.{0, u, v} ℂ (localWeilGroup F),
    A.IsContinuous ∧ IsTrivialAt F A μ ∧ FiniteRepresentation.classOf A = c}

end Definitions

/-- The injectivity half of Galois truncation, stated as equality of comaps. -/
def TruncationGaloisComapStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (E : FiniteIntermediateExtension F.Carrier) (μ : ℝ),
    E.field.fixingSubgroup ⊔ absoluteUpperRamificationGroup F μ = ⊤ →
    ∀ x : ℝ, -1 ≤ x → x ≤ μ →
      (absoluteUpperRamificationGroup F x).comap (intermediateGaloisMap F E).toMonoidHom =
        absoluteUpperRamificationGroup (E.asPadicField (p := p)) x

/-- Transitivity gives the filtered topological Galois quotient isomorphism
through the transitivity index. -/
def TruncationGaloisQuotientStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (E : FiniteIntermediateExtension F.Carrier) (μ : ℝ),
    E.field.fixingSubgroup ⊔ absoluteUpperRamificationGroup F μ = ⊤ →
    ∀ x : ℝ, -1 ≤ x → x ≤ μ → GaloisTruncationIsoAt F E x

/-- The injectivity half of Weil truncation, stated as equality of comaps. -/
def TruncationWeilComapStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (E : FiniteIntermediateExtension F.Carrier) (μ : ℝ),
    E.field.fixingSubgroup ⊔ absoluteUpperRamificationGroup F μ = ⊤ →
    ∀ x : ℝ, -1 ≤ x → x ≤ μ →
      (upperGroup F x).comap (intermediateWeilMap F E).toMonoidHom =
        upperGroup (E.asPadicField (p := p)) x

/-- Transitivity gives the filtered topological Weil quotient isomorphism
through the transitivity index. -/
def TruncationWeilQuotientStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (E : FiniteIntermediateExtension F.Carrier) (μ : ℝ),
    E.field.fixingSubgroup ⊔ absoluteUpperRamificationGroup F μ = ⊤ →
    ∀ x : ℝ, -1 ≤ x → x ≤ μ → WeilTruncationIsoAt F E x

/-- At a nonnegative transitivity index the Weil inclusion preserves degree,
which gives compatibility with unramified twists. -/
def TruncationWeilDegreeStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (E : FiniteIntermediateExtension F.Carrier) (μ : ℝ),
    E.field.fixingSubgroup ⊔ absoluteUpperRamificationGroup F μ = ⊤ →
    0 ≤ μ →
    ∀ w : localWeilGroup (E.asPadicField (p := p)),
      localDegree F (intermediateWeilMap F E w) =
        localDegree (E.asPadicField (p := p)) w

/-- Restriction is bijective on continuous classes trivial at the transitivity
index and preserves irreducibility and every upper fixed-space rank. -/
def TruncationWeilRestrictionStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (E : FiniteIntermediateExtension F.Carrier) (μ : ℝ),
    E.field.fixingSubgroup ⊔ absoluteUpperRamificationGroup F μ = ⊤ →
    -1 ≤ μ →
    Set.BijOn (FiniteRepresentation.restrictClass (intermediateWeilMap F E).toMonoidHom)
      (truncatedWeilClasses.{u, v} F μ)
      (truncatedWeilClasses.{u, v} (E.asPadicField (p := p)) μ) ∧
    ∀ A : FiniteRepresentation.{0, u, v} ℂ (localWeilGroup F), IsTrivialAt F A μ →
      ((weilRestrict E A).IsIrreducible ↔ A.IsIrreducible) ∧
      ∀ r : ℝ, -1 ≤ r →
        Module.finrank ℂ (upperFixedSpace (E.asPadicField (p := p)) (weilRestrict E A) r) =
          Module.finrank ℂ (upperFixedSpace F A r)

/-- Every finite Kummer stage has the same filtered Galois quotient as the
base field through the common break `p e / (p - 1)`. -/
def KummerStageGaloisQuotientStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (ϖ : F.Carrier) (πs : ℕ → AlgebraicClosure F.Carrier),
    IsKummerRootSystem F ϖ πs →
    ∀ (n : ℕ) (x : ℝ), -1 ≤ x → x ≤ kummerBreak F →
      GaloisTruncationIsoAt F (kummerStage F πs n) x

/-- Every finite Kummer stage has the same filtered Weil quotient as the
base field through the common break `p e / (p - 1)`. -/
def KummerStageWeilQuotientStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (ϖ : F.Carrier) (πs : ℕ → AlgebraicClosure F.Carrier),
    IsKummerRootSystem F ϖ πs →
    ∀ (n : ℕ) (x : ℝ), -1 ≤ x → x ≤ kummerBreak F →
      WeilTruncationIsoAt F (kummerStage F πs n) x

end Langlands.Ramification.Kummer
