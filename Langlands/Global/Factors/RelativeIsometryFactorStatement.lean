import Langlands.Global.Factors.RelativePolePairingStatement
import Langlands.Correspondence.OperationCompatibility
import Langlands.Correspondence.SupercuspidalRelations
import Langlands.Correspondence.SupercuspidalFactorCompatibility
import Langlands.VirtualRepresentation.ExactDeterminant

/-!
# Determinant and pair-factor compatibility of the relative isometry

A finite-relative analogue of Henniart's Proposition 2.6 (a), determinant clause,
and (b), L- and epsilon-factor clauses, for the generated-span isometry of
witnessed relative pairs at a fixed level `E/F`. Virtual determinants, central
characters and pair factors are defined from the actual basis classes by integral
linearity and bilinearity. The pole-comparison input stays explicit.
-/

noncomputable section

universe uF uW uP uV uE

namespace Langlands.VirtualRepresentation.LocalWeil

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

-- As in `ExactGrothendieckGroup.determinant`: use the additive monoid inherited from
-- the character group, so that its canonical integer-module structure applies.
local instance {G : Type*} [Group G] : AddCommMonoid (Additive (G →* ℂˣ)) :=
  (inferInstance : AddCommGroup (Additive (G →* ℂˣ))).toAddCommMonoid

/-- The determinant of a unitary virtual Weil class: the determinant characters of
the basis classes, extended by integral linearity into the character group. -/
def unitaryDeterminant :
    UnitaryLattice.{uF, uV} F →ₗ[ℤ] Additive (Weil.Local.localWeilGroup F →* ℂˣ) :=
  extend fun b : UnitaryBasis.{uF, uV} F => Additive.ofMul
    (FiniteRepresentation.determinantCharacterClass
      (Weil.underlyingClass (Weil.Local.localWeilGroup F) b.val))

/-- The zero-monodromy pair class of an actual unitary Weil basis class. -/
def unitaryBasisPairClass (b : UnitaryBasis.{uF, uV} F) :
    Correspondence.LocalPairClass.{uF, uV} F :=
  Correspondence.weilPairClass F (n := b.val.1) b.val.2

/-- `L(s, x ⊗ y)` for unitary virtual Weil classes, as a rational function of
`q^(-s)`: the actual arithmetic pair L-factors of the basis classes, raised to
the products of multiplicities. -/
def unitaryPairLFactor (x y : UnitaryLattice.{uF, uV} F) : RatFunc ℂ :=
  x.prod fun a m => y.prod fun b n =>
    Correspondence.arithmeticPairLFactor F (unitaryBasisPairClass F a)
      (unitaryBasisPairClass F b) ^ (m * n)

/-- `ε(s, x ⊗ y, ψ) = c q^(-ms)` for unitary virtual Weil classes and the supplied
local-constant system: each pair of basis classes in the supports has an actual
arithmetic epsilon certificate, and `(c, m)` is their multiplicity-weighted
product. -/
def IsUnitaryPairEpsilonFactor (eC : LocalFactor.CommonClosure.ReciprocityFamily F)
    (ε : LocalFactor.NonabelianSystem.Assignment.{uF, uE} F)
    (hε : LocalFactor.NonabelianSystem.IsSystem F eC ε)
    (ψ : Correspondence.NontrivialAdditiveCharacter F)
    (x y : UnitaryLattice.{uF, uV} F) (e : ℂˣ × ℤ) : Prop :=
  ∃ f : UnitaryBasis.{uF, uV} F → UnitaryBasis.{uF, uV} F → ℂˣ × ℤ,
    (∀ a ∈ x.support, ∀ b ∈ y.support,
      Correspondence.IsArithmeticPairEpsilonFactor F eC ε hε ψ
        (unitaryBasisPairClass F a) (unitaryBasisPairClass F b) (f a b).1 (f a b).2) ∧
    e = (x.prod fun a m => y.prod fun b n => (f a b).1 ^ (m * n),
      x.sum fun a m => y.sum fun b n => m * n * (f a b).2)

/-- On a basis class, the virtual determinant is the actual determinant character. -/
theorem unitaryDeterminant_generator (b : UnitaryBasis.{uF, uV} F) :
    unitaryDeterminant F (generator b) = Additive.ofMul
      (FiniteRepresentation.determinantCharacterClass
        (Weil.underlyingClass (Weil.Local.localWeilGroup F) b.val)) := by
  simp [unitaryDeterminant, extend, generator]

/-- On two basis classes, the virtual pair L-factor is the actual arithmetic one. -/
theorem unitaryPairLFactor_generator (a b : UnitaryBasis.{uF, uV} F) :
    unitaryPairLFactor F (generator a) (generator b) =
      Correspondence.arithmeticPairLFactor F (unitaryBasisPairClass F a)
        (unitaryBasisPairClass F b) := by
  simp [unitaryPairLFactor, generator, Finsupp.prod_single_index]

end Langlands.VirtualRepresentation.LocalWeil

namespace Langlands.VirtualRepresentation.PadicSupercuspidal

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- `ω` is the central character of an actual unitary supercuspidal basis class. -/
def IsUnitaryBasisCentralCharacter (b : UnitaryBasis.{uF, uV} F)
    (ω : F.Carrierˣ →* ℂˣ) : Prop :=
  ∀ a : F.Carrierˣ, Correspondence.SupercuspidalCentralActsBy F (n := b.val.1) b.val.2 a (ω a)

/-- `ω` is the central character of a unitary virtual supercuspidal class: some
central characters of the basis classes in the support have multiplicity-weighted
product `ω`. -/
def IsUnitaryCentralCharacter (y : UnitaryLattice.{uF, uV} F)
    (ω : F.Carrierˣ →* ℂˣ) : Prop :=
  ∃ f : UnitaryBasis.{uF, uV} F → F.Carrierˣ →* ℂˣ,
    (∀ b ∈ y.support, IsUnitaryBasisCentralCharacter F b (f b)) ∧
      ω = y.prod fun b n => f b ^ n

/-- The published JPSS pair L-polynomial relation on two unitary supercuspidal
basis classes, written at their positive ranks `r + 1` and `n + 1`. -/
def IsUnitaryBasisPairLPolynomial (ψ : Correspondence.NontrivialAdditiveCharacter F)
    (ν : Correspondence.LocalAdditiveHaarMeasure F) (a b : UnitaryBasis.{uF, uV} F)
    (P : Polynomial ℂ) : Prop :=
  match a.val, b.val with
  | ⟨⟨r + 1, _⟩, π⟩, ⟨⟨n + 1, _⟩, τ⟩ =>
      Correspondence.IsSupercuspidalPairLPolynomial F ψ ν (r := r) (n := n) π τ P
  | _, _ => False

/-- The published JPSS pair epsilon relation `ε(s, π × τ, ψ) = c q^(-ms)` on two
unitary supercuspidal basis classes, written at their positive ranks. -/
def IsUnitaryBasisPairEpsilonFactor (ψ : Correspondence.NontrivialAdditiveCharacter F)
    (ν : Correspondence.LocalAdditiveHaarMeasure F) (a b : UnitaryBasis.{uF, uV} F)
    (e : ℂˣ × ℤ) : Prop :=
  match a.val, b.val with
  | ⟨⟨r + 1, _⟩, π⟩, ⟨⟨n + 1, _⟩, τ⟩ =>
      Correspondence.IsSupercuspidalPairEpsilonFactor F ψ ν (r := r) (n := n) π τ e
  | _, _ => False

/-- `L(s, x × y) = L` for unitary virtual supercuspidal classes: each pair of basis
classes in the supports has an actual JPSS L-polynomial `P`, and `L` is the
multiplicity-weighted product of the factors `1 / P(q^(-s))`. -/
def IsUnitaryPairLFactor (ψ : Correspondence.NontrivialAdditiveCharacter F)
    (ν : Correspondence.LocalAdditiveHaarMeasure F) (x y : UnitaryLattice.{uF, uV} F)
    (L : RatFunc ℂ) : Prop :=
  ∃ P : UnitaryBasis.{uF, uV} F → UnitaryBasis.{uF, uV} F → Polynomial ℂ,
    (∀ a ∈ x.support, ∀ b ∈ y.support, IsUnitaryBasisPairLPolynomial F ψ ν a b (P a b)) ∧
      L = x.prod fun a m => y.prod fun b n =>
        (algebraMap (Polynomial ℂ) (RatFunc ℂ) (P a b))⁻¹ ^ (m * n)

/-- `ε(s, x × y, ψ) = c q^(-ms)` for unitary virtual supercuspidal classes: each
pair of basis classes in the supports has an actual JPSS epsilon certificate, and
`(c, m)` is their multiplicity-weighted product. -/
def IsUnitaryPairEpsilonFactor (ψ : Correspondence.NontrivialAdditiveCharacter F)
    (ν : Correspondence.LocalAdditiveHaarMeasure F) (x y : UnitaryLattice.{uF, uV} F)
    (e : ℂˣ × ℤ) : Prop :=
  ∃ f : UnitaryBasis.{uF, uV} F → UnitaryBasis.{uF, uV} F → ℂˣ × ℤ,
    (∀ a ∈ x.support, ∀ b ∈ y.support, IsUnitaryBasisPairEpsilonFactor F ψ ν a b (f a b)) ∧
    e = (x.prod fun a m => y.prod fun b n => (f a b).1 ^ (m * n),
      x.sum fun a m => y.sum fun b n => m * n * (f a b).2)

/-- On two basis classes, the virtual pair L-factor relation is the actual JPSS
relation `L = 1 / P(q^(-s))`. -/
theorem isUnitaryPairLFactor_generator_iff
    (ψ : Correspondence.NontrivialAdditiveCharacter F)
    (ν : Correspondence.LocalAdditiveHaarMeasure F) (a b : UnitaryBasis.{uF, uV} F)
    (L : RatFunc ℂ) :
    IsUnitaryPairLFactor F ψ ν (generator a) (generator b) L ↔
      ∃ P : Polynomial ℂ, IsUnitaryBasisPairLPolynomial F ψ ν a b P ∧
        L = (algebraMap (Polynomial ℂ) (RatFunc ℂ) P)⁻¹ := by
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact ⟨P a b, hP a (by simp [generator]) b (by simp [generator]),
      by simp [generator, Finsupp.prod_single_index]⟩
  · rintro ⟨P, hP, rfl⟩
    refine ⟨fun _ _ => P, ?_, by simp [generator, Finsupp.prod_single_index]⟩
    intro a' ha' b' hb'
    simp only [generator, Finsupp.support_single _ one_ne_zero,
      Finset.mem_singleton] at ha' hb'
    subst ha' hb'
    exact hP

/-- On a basis class, the virtual central-character relation is the actual one. -/
theorem isUnitaryCentralCharacter_generator_iff (b : UnitaryBasis.{uF, uV} F)
    (ω : F.Carrierˣ →* ℂˣ) :
    IsUnitaryCentralCharacter F (generator b) ω ↔ IsUnitaryBasisCentralCharacter F b ω := by
  have hprod : ∀ f : UnitaryBasis.{uF, uV} F → F.Carrierˣ →* ℂˣ,
      ((generator b).prod fun b' n => f b' ^ n) = f b := by
    intro f
    rw [generator, Finsupp.prod_single_index
      (MonoidHom.ext fun a => by simp [MonoidHom.zpow_apply])]
    exact MonoidHom.ext fun a => by simp [MonoidHom.zpow_apply]
  constructor
  · rintro ⟨f, hf, rfl⟩
    rw [hprod]
    exact hf b (by simp [generator])
  · intro h
    refine ⟨fun _ => ω, ?_, (hprod fun _ => ω).symm⟩
    intro b' hb'
    simp only [generator, Finsupp.support_single _ one_ne_zero,
      Finset.mem_singleton] at hb'
    subst hb'
    exact h

end Langlands.VirtualRepresentation.PadicSupercuspidal

namespace Langlands.Global.PoleComparison

open Langlands.VirtualRepresentation Langlands.VirtualRepresentation.RelativeGlobal
open Langlands.Global.CompletionPadic Langlands.ClassField.Global
open Langlands.Global.AdelicFunctoriality

variable (F E : Type uF) [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
  (c : FundamentalClass.ClassFamily.{uF}) (v : FinitePlace F)

/-- `det x = ω_(T x) ∘ rec`: the image of each generated Weil class has a central
character whose pullback along the reciprocity candidate is its determinant. -/
def RelativeIsometryDeterminantCompatibility
    (T : weilImage.{uF, uW, uP} F E c v ≃ₗ[ℤ]
      automorphicImage.{uF, uW, uP} F E c v)
    (e : Correspondence.ReciprocityCandidate (padicField v)) : Prop :=
  ∀ x : weilImage.{uF, uW, uP} F E c v, ∃ ω : (padicField v).Carrierˣ →* ℂˣ,
    PadicSupercuspidal.IsUnitaryCentralCharacter (padicField v) (T x).1 ω ∧
      ∀ w : Weil.Local.localWeilGroup (padicField v),
        ω (Correspondence.reciprocityHom (padicField v) e w) =
          Additive.toMul (LocalWeil.unitaryDeterminant (padicField v) x.1) w

/-- `L(s, T x × T y) = L(s, x ⊗ y)` and `ε(s, T x × T y, ψ) = ε(s, x ⊗ y, ψ)` for
generated Weil classes. A self-dual measure exists; for every such measure the
L-factors agree, and for every local-constant system some `c q^(-ms)` is both
epsilon factors. -/
def RelativeIsometryPairFactorCompatibility
    (T : weilImage.{uF, uW, uP} F E c v ≃ₗ[ℤ]
      automorphicImage.{uF, uW, uP} F E c v)
    (ψ : Correspondence.NontrivialAdditiveCharacter (padicField v)) : Prop :=
  (∃ ν : Correspondence.LocalAdditiveHaarMeasure (padicField v),
    Correspondence.IsSelfDualMeasure (padicField v) ψ ν) ∧
  ∀ ν : Correspondence.LocalAdditiveHaarMeasure (padicField v),
    Correspondence.IsSelfDualMeasure (padicField v) ψ ν →
    ∀ x y : weilImage.{uF, uW, uP} F E c v,
      PadicSupercuspidal.IsUnitaryPairLFactor (padicField v) ψ ν (T x).1 (T y).1
          (LocalWeil.unitaryPairLFactor (padicField v) x.1 y.1) ∧
        ∀ (eC : LocalFactor.CommonClosure.ReciprocityFamily (padicField v))
          (ε : LocalFactor.NonabelianSystem.Assignment.{uF, uE} (padicField v))
          (hε : LocalFactor.NonabelianSystem.IsSystem (padicField v) eC ε),
          ∃ e : ℂˣ × ℤ,
            LocalWeil.IsUnitaryPairEpsilonFactor (padicField v) eC ε hε ψ x.1 y.1 e ∧
              PadicSupercuspidal.IsUnitaryPairEpsilonFactor (padicField v) ψ ν
                (T x).1 (T y).1 e

/-- The relative analogue of Henniart's Proposition 2.6 (a), determinant clause,
and (b), pair L- and epsilon-factor clauses, for an isometry. The determinant clause uses every
geometric local reciprocity candidate; the factor clauses use every additive
character. -/
def RelativeIsometryFactors
    (T : weilImage.{uF, uW, uP} F E c v ≃ₗ[ℤ]
      automorphicImage.{uF, uW, uP} F E c v) : Prop :=
  (∀ e : Correspondence.ReciprocityCandidate (padicField v),
    Correspondence.IsGeometricReciprocity (padicField v) e →
      RelativeIsometryDeterminantCompatibility F E c v T e) ∧
    ∀ ψ : Correspondence.NontrivialAdditiveCharacter (padicField v),
      RelativeIsometryPairFactorCompatibility.{uF, uW, uP, uE} F E c v T ψ

/-- Under the certified pole comparisons, every generated positive isometry of
the actual relative images satisfies the relative analogues of the determinant
and pair-factor clauses of Henniart's Proposition 2.6. -/
def RelativeIsometryFactorStatement : Prop :=
  ∀ (F E : Type uF) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    (c : FundamentalClass.ClassFamily.{uF}),
    RelativeWeilGroup.IsArithmeticClassFamily c →
  ∀ (v : FinitePlace F) (ψ : Correspondence.NontrivialAdditiveCharacter (padicField v)),
    RelativeCertifiedPoleComparisons.{uF, uW, uP} F E c v ψ →
    ∀ T : weilImage.{uF, uW, uP} F E c v ≃ₗ[ℤ] automorphicImage.{uF, uW, uP} F E c v,
      RelativeGeneratedPositiveIsometry F E c v T →
      RelativeIsometryFactors.{uF, uW, uP, uE} F E c v T

end Langlands.Global.PoleComparison
