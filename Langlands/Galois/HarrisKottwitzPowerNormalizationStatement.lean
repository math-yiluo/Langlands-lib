import Langlands.Galois.AlgebraicHeckeAvatarStatement
import Langlands.Galois.CyclotomicTwist
import Langlands.Galois.HarrisNormalizedSystem

/-! # Arithmetic normalization of a fixed Kottwitz power family -/

noncomputable section
set_option autoImplicit false

universe uE uL uV uW

namespace Langlands.GaloisRepresentation

open Langlands.Automorphic Langlands.Global Langlands.Unramified Langlands.Cohomology.Weights
open NumberField (IsCMField)
open Polynomial

/-- A monic power root in characteristic zero does not require extending the
coefficient field. The positive exponent and monicity cannot be dropped. -/
def MonicCharacteristicPowerRootDescentStatement : Prop :=
  ∀ (L : Type uL) [Field L] [CharZero L] (M : Type uW) [Field M]
    (ι : L →+* M) (a : ℕ) (P : Polynomial M) (Q : Polynomial L),
    0 < a → P.Monic → Q.map ι = P ^ a →
    ∃! R : Polynomial L, R.Monic ∧ R.map ι = P ∧ R ^ a = Q

variable {E : Type uE} [Field E] {L : Type uL} [Field L] [NumberField L]

/-- Apply the inverse of the *given* completion-valued avatar. The carrier
is that of the original multiplicity representation, with its action twisted. -/
def harrisKottwitzInverseTwist (M : Collection.{uE, uL, uV} E L ∅)
    (ψ : ∀ lam : FinitePlace L, LambdaAdicCharacter E L lam) : Collection.{uE, uL, uV} E L ∅ :=
  fun lam =>
    twist (ψ lam.1).toMonoidHom⁻¹
      (Units.continuous_val.comp ((ψ lam.1).continuous.inv)) (M lam)

/-- Given the middle-degree monic factors and the same geometric Frobenius
powers at every coefficient place, remove the central scalar of Clozel's
comparison and obtain the arithmetic power family. The finite exceptional
set for the output may include the ramification of the correction. -/
def HarrisKottwitzPowerNormalizationStatement : Prop :=
  ∀ (E : Type uE) [Field E] [NumberField E] [IsCMField E] [CompactSpace (AdeleQuotient E)]
    (r : ℕ) (c : CuspidalOperatorRealization.IsoClass E r)
    (s : SpectralSystem (FinitePlace E) (r + 1)),
  c.HasSpectralSystem.{uE, uW} s →
  ∀ (L : Type uL) [Field L] [NumberField L] (ι : L →+* ℂ)
    (a w : ℤ) (S Sχ : Finset (FinitePlace E))
    (Q : FinitePlace E → Polynomial L) (M : Collection.{uE, uL, uV} E L ∅)
    (χ : HeckeCharacter E) (β : FinitePlace E → Lˣ)
    (ψ : ∀ lam : FinitePlace L, LambdaAdicCharacter E L lam),
    a ≠ 0 → Harris.IsAlgebraic χ → IsUniformHeckeAvatar ι χ Sχ β ψ →
    MatchesOutside ∅ M S (fun v => (Q v ^ a.natAbs).reverse) →
    (∀ v ∉ S,
      (Q v).natDegree = r + 1 ∧ (Q v).coeff 0 ≠ 0 ∧
      IsPurePolynomial (residueCardinality v) ((r : ℤ) + w) (Q v)) →
    (∀ v ∉ S, v ∉ Sχ →
      (∀ j : L →+* ℂ, IsWeilNumber (residueCardinality v) w (j (β v : L))) ∧
      ∃ hv : v ∉ s.exceptional,
        (Q v).reverse.map ι =
          (clozelEulerPolynomial (s.eigenvalues v hv) 1 (residueCardinality v)).comp
            (C (ι (β v : L)) * X)) →
    HarrisPowerSystem.{uE, uL, uV, uW} c ι ∅ (harrisKottwitzInverseTwist M ψ) a.natAbs

end Langlands.GaloisRepresentation
