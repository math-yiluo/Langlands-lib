import Langlands.Global.Factors.HenniartCompositeMapStatement
import Langlands.Correspondence.SupercuspidalSpecification
import Langlands.Correspondence.RankOneExistence
import Langlands.VirtualRepresentation.Weil.Twist
import Langlands.VirtualRepresentation.Supercuspidal.Unramified

/-!
# Removing the auxiliary choices in Henniart's construction

Henniart (2000), §§4.1–4.4, pages 451–453. A candidate at a finite quotient `q`
of the absolute Galois group of a p-adic field `K` is a map of unitary lattices
over `K` whose domain contains every unitary class factoring through `q` and
which has all properties of Henniart's 3.8 (`LatticeMap.HenniartProperties`).
A stable image of a class is the common value of all candidates at one finite
quotient. The rank induction, its lower-rank hypotheses, the finite candidate
sets, the unramified-twist extension and the final construction are stated
separately. Proposition definitions only.
-/

noncomputable section

namespace Langlands.Henniart

universe uK uW uV uE uQ

namespace StableMap

open Langlands.Correspondence Langlands.VirtualRepresentation

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

/-- `Φ` is a candidate at `q`: its domain contains every unitary class of `W_K`
factoring through `q`, and it has all properties of Henniart's 3.8 at `K`. -/
def IsCandidate {Q : Type uQ} [Group Q] [Finite Q]
    (q : Field.absoluteGaloisGroup K.Carrier →* Q)
    {W : Submodule ℤ (LocalWeil.UnitaryLattice.{uK, uW} K)}
    {A : Submodule ℤ (PadicSupercuspidal.UnitaryLattice.{uK, uV} K)}
    (Φ : W ≃ₗ[ℤ] A) : Prop :=
  LocalWeil.unitaryFiniteFactoringSupported.{uK, uW, uQ} K q ≤ W ∧
    LatticeMap.HenniartProperties.{uK, uW, uV, uE} K Φ

/-- The unitary irreducible class `σ` factors through a finite quotient of the
absolute Galois group of `K`. -/
def IsFiniteFactoring (σ : LocalWeil.UnitaryBasis.{uK, uW} K) : Prop :=
  ∃ (Q : Type uK) (_ : Group Q) (_ : Finite Q)
    (q : Field.absoluteGaloisGroup K.Carrier →* Q),
    generator σ ∈ LocalWeil.unitaryFiniteFactoringSupported.{uK, uW, uK} K q

/-- `y` is the stable image of `σ`: for one finite quotient `q` through which
`σ` factors, candidates at `q` exist and every candidate at `q` sends `σ` to `y`. -/
def IsStableImage (σ : LocalWeil.UnitaryBasis.{uK, uW} K)
    (y : PadicSupercuspidal.UnitaryLattice.{uK, uV} K) : Prop :=
  ∃ (Q : Type uK) (_ : Group Q) (_ : Finite Q)
    (q : Field.absoluteGaloisGroup K.Carrier →* Q),
    generator σ ∈ LocalWeil.unitaryFiniteFactoringSupported.{uK, uW, uK} K q ∧
    (∃ (W : Submodule ℤ (LocalWeil.UnitaryLattice.{uK, uW} K))
      (A : Submodule ℤ (PadicSupercuspidal.UnitaryLattice.{uK, uV} K)) (Φ : W ≃ₗ[ℤ] A),
      IsCandidate.{uK, uW, uV, uE, uK} K q Φ) ∧
    ∀ (W : Submodule ℤ (LocalWeil.UnitaryLattice.{uK, uW} K))
      (A : Submodule ℤ (PadicSupercuspidal.UnitaryLattice.{uK, uV} K)) (Φ : W ≃ₗ[ℤ] A),
      IsCandidate.{uK, uW, uV, uE, uK} K q Φ →
      ∀ x : W, (x : LocalWeil.UnitaryLattice.{uK, uW} K) = generator σ →
        (Φ x : PadicSupercuspidal.UnitaryLattice.{uK, uV} K) = y

/-- The central character of the unitary supercuspidal class `π` has finite order. -/
def HasFiniteOrderCentralCharacter (π : PadicSupercuspidal.UnitaryBasis.{uK, uV} K) :
    Prop :=
  ∃ ω : K.Carrierˣ →* ℂˣ,
    PadicSupercuspidal.IsUnitaryBasisCentralCharacter K π ω ∧ IsOfFinOrder ω

/-- Henniart's 4.2 (a) in rank `n`: every finite-image unitary irreducible class
of dimension `n` has a stable image. -/
def StableExistsAt (n : ℕ+) : Prop :=
  ∀ σ : LocalWeil.UnitaryBasis.{uK, uW} K, σ.val.1 = n → IsFiniteFactoring K σ →
    ∃ y : PadicSupercuspidal.UnitaryLattice.{uK, uV} K, IsStableImage.{uK, uW, uV, uE} K σ y

/-- Henniart's 4.2 (b), surjectivity in rank `n`: every unitary supercuspidal
class of `GL_n(K)` with finite-order central character is the stable image of a
finite-image unitary irreducible class of dimension `n`. -/
def StableSurjectiveAt (n : ℕ+) : Prop :=
  ∀ π : PadicSupercuspidal.UnitaryBasis.{uK, uV} K, π.val.1 = n →
    HasFiniteOrderCentralCharacter K π →
    ∃ σ : LocalWeil.UnitaryBasis.{uK, uW} K, σ.val.1 = n ∧
      IsStableImage.{uK, uW, uV, uE} K σ (generator π)

/-- Both assertions of Henniart's induction in rank `n`. -/
def RankStage (n : ℕ+) : Prop :=
  StableExistsAt.{uK, uW, uV, uE} K n ∧ StableSurjectiveAt.{uK, uW, uV, uE} K n

/-- The unramified twist of an irreducible Weil class by the character sending
geometric Frobenius to `z`. -/
def weilUnramifiedTwist (z : ℂˣ) :
    LocalWeil.Basis.{uK, uW} K ≃ LocalWeil.Basis.{uK, uW} K :=
  Weil.twistBasisEquiv (Weil.Local.unramifiedCharacter (Weil.Local.localDegree K) z)

end StableMap

open StableMap Correspondence VirtualRepresentation

/-- Henniart (2000), Théorème 3.1 with §§3.7–3.8, in local form: for every finite
quotient `q` of the absolute Galois group of `K` there is a candidate at `q`. -/
def CandidateExistenceStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (Q : Type uQ) [Group Q] [Finite Q]
    (q : Field.absoluteGaloisGroup K.Carrier →* Q),
    ∃ (W : Submodule ℤ (LocalWeil.UnitaryLattice.{uK, uW} K))
      (A : Submodule ℤ (PadicSupercuspidal.UnitaryLattice.{uK, uV} K)) (Φ : W ≃ₗ[ℤ] A),
      IsCandidate.{uK, uW, uV, uE, uQ} K q Φ

/-- Henniart (2000), Théorème 4.2 (a): every unitary irreducible class factoring
through a finite quotient has a stable image, independent of all auxiliary choices
once the finite quotient is large enough. -/
def ChoiceIndependenceStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (σ : LocalWeil.UnitaryBasis.{uK, uW} K),
    IsFiniteFactoring K σ →
      ∃ y : PadicSupercuspidal.UnitaryLattice.{uK, uV} K, IsStableImage.{uK, uW, uV, uE} K σ y

/-- Henniart (2000), §4.3: the candidate images are confined to a finite set.
For a fixed additive character and self-dual measure, only finitely many
supercuspidal classes of `GL_(k+1)(K)` have a given central character and a given
exponent `m` in the epsilon factor `c q^(-ms)` of the pair with the trivial
character of `GL_1(K)`. -/
def SupercuspidalEpsilonConductorFinitenessStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (ψ : NontrivialAdditiveCharacter K)
    (ν : LocalAdditiveHaarMeasure K), IsSelfDualMeasure K ψ ν →
    ∀ (k : ℕ) (ω : K.Carrierˣ →* ℂˣ) (m : ℤ),
      {π : SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat |
        (∀ a : K.Carrierˣ, SupercuspidalCentralActsBy K π a (ω a)) ∧
          ∃ c : ℂˣ, IsSupercuspidalPairEpsilonFactor K ψ ν (r := k) (n := 0) π
            (letI := K.canonicalTopologicalData.topology
             rankOneSupercuspidalClass.{uK, uV} K 1) (c, m)}.Finite

/-- Henniart (2000), §4.3, base case: rank one, where stable images are given by
local class field theory. -/
def RankOneStageStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p), RankStage.{uK, uW, uV, uE} K 1

/-- Henniart (2000), §4.3, proof of 4.2 (a) in rank `n ≥ 2`: from the stable
images and the surjectivity in every lower rank, used to lift the finitely many
separating lower-rank tests, every finite-image class of dimension `n` has a
stable image. -/
def ChoiceIndependenceStepStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (n : ℕ+), 1 < n →
    (∀ r : ℕ+, r < n → RankStage.{uK, uW, uV, uE} K r) →
      StableExistsAt.{uK, uW, uV, uE} K n

/-- Henniart (2000), §4.3, last sentence: in rank `n`, the stable images are
surjective onto the unitary supercuspidal classes with finite-order central
character, by Henniart (1988), Théorème 1.2. -/
def SurjectivityStepStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (n : ℕ+),
    StableExistsAt.{uK, uW, uV, uE} K n → StableSurjectiveAt.{uK, uW, uV, uE} K n

/-- Henniart (2000), §4.3: the inductive step on the rank, with the lower-rank
stable images and lower-rank surjectivity as explicit hypotheses. -/
def RankInductionStepStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (n : ℕ+), 1 < n →
    (∀ r : ℕ+, r < n → RankStage.{uK, uW, uV, uE} K r) → RankStage.{uK, uW, uV, uE} K n

/-- Henniart (2000), Théorème 4.2 (a) and the bijectivity in (b): both assertions
hold in every rank. -/
def StableCorrespondenceStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (n : ℕ+), RankStage.{uK, uW, uV, uE} K n

/-- Henniart (2000), §4.4, with Henniart (1993), §4.3: if two unramified twists
`z₁⁻¹ σ` and `z₂⁻¹ σ` of an irreducible class have stable images `y₁` and `y₂`,
then `z₁ y₁ = z₂ y₂`. The extended value does not depend on the twist. -/
def UnramifiedTwistIndependenceStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (σ : LocalWeil.Basis.{uK, uW} K)
    (z₁ z₂ : ℂˣ) (σ₁ σ₂ : LocalWeil.UnitaryBasis.{uK, uW} K)
    (y₁ y₂ : PadicSupercuspidal.UnitaryLattice.{uK, uV} K),
    σ₁.val = weilUnramifiedTwist K z₁⁻¹ σ → σ₂.val = weilUnramifiedTwist K z₂⁻¹ σ →
    IsStableImage.{uK, uW, uV, uE} K σ₁ y₁ → IsStableImage.{uK, uW, uV, uE} K σ₂ y₂ →
    PadicSupercuspidal.unramifiedTwistLatticeEquiv K z₁ (PadicSupercuspidal.includeUnitary K y₁) =
      PadicSupercuspidal.unramifiedTwistLatticeEquiv K z₂ (PadicSupercuspidal.includeUnitary K y₂)

/-- Henniart (2000), §4.4 and Théorème 1.2: Henniart's construction gives a
supercuspidal correspondence. Some supercuspidal map is a correspondence and
agrees with the stable images on every finite-image unitary irreducible class. -/
def HenniartConstructionStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p),
    ∃ c : SupercuspidalMap.{uK, uW, uV} K,
      IsSupercuspidalCorrespondence K c ∧
      ∀ σ : LocalWeil.UnitaryBasis.{uK, uW} K, IsFiniteFactoring K σ →
        ∃ y : PadicSupercuspidal.UnitaryLattice.{uK, uV} K,
          IsStableImage.{uK, uW, uV, uE} K σ y ∧
          PadicSupercuspidal.includeUnitary K y =
            generator (⟨σ.val.1, c σ.val.1 σ.val.2⟩ : PadicSupercuspidal.Basis.{uK, uV} K)

/-- Henniart's local construction, §§3.7–4.4: candidate existence, choice
independence, finiteness of candidate sets, the rank induction, the
unramified-twist extension and the final construction. -/
def HenniartStableMapStatement : Prop :=
  CandidateExistenceStatement.{uK, uW, uV, uE, uQ} ∧
    ChoiceIndependenceStatement.{uK, uW, uV, uE} ∧
    SupercuspidalEpsilonConductorFinitenessStatement.{uK, uV} ∧
    RankOneStageStatement.{uK, uW, uV, uE} ∧
    ChoiceIndependenceStepStatement.{uK, uW, uV, uE} ∧
    SurjectivityStepStatement.{uK, uW, uV, uE} ∧
    RankInductionStepStatement.{uK, uW, uV, uE} ∧
    StableCorrespondenceStatement.{uK, uW, uV, uE} ∧
    UnramifiedTwistIndependenceStatement.{uK, uW, uV, uE} ∧
    HenniartConstructionStatement.{uK, uW, uV, uE}

end Langlands.Henniart
