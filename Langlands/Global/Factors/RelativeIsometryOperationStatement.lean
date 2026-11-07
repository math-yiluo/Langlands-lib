import Langlands.Global.Factors.RelativePolePairingStatement
import Langlands.VirtualRepresentation.Weil.LocalUnitaryOperations
import Langlands.VirtualRepresentation.Supercuspidal.Contragredient
import Langlands.VirtualRepresentation.Supercuspidal.UnitaryTwist
import Langlands.Correspondence.SupercuspidalOperationRealization
import Langlands.Correspondence.RankOneReciprocityBijection
import Langlands.Correspondence.RankOneExistence

/-!
# Contragredient, twist and character compatibility of the relative isometry

A finite-relative analogue of Henniart's Proposition 2.6 (a), contragredient and
twist clauses, and (c), for the generated-span isometry of witnessed relative
pairs at a fixed level `E/F`. The pole-comparison input stays explicit. Twists use modulus-one field characters pulled back
along a geometric local reciprocity candidate.
-/

noncomputable section

universe uF uW uP uV

namespace Langlands.VirtualRepresentation.PadicSupercuspidal

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Twist the actual unitary supercuspidal lattice by `χ ∘ det` in every rank,
for a modulus-one continuous field character `χ`. -/
def unitaryCharacterTwistLatticeEquiv (χ : Correspondence.QuasiCharacter F)
    (hχ : ∀ a, ‖(χ a : ℂ)‖ = 1) :
    UnitaryLattice.{uF, uV} F ≃ₗ[ℤ] UnitaryLattice.{uF, uV} F :=
  letI := F.canonicalTopologicalData.topology
  Supercuspidal.unitaryTwistLatticeEquiv
    (fun n => Correspondence.determinantQuasiCharacter F n χ)
    (fun n => Correspondence.isOpen_ker_determinantQuasiCharacter F n χ)
    (fun _ => GeneralLinear.ker_determinant_le_ker_comp χ.toMonoidHom)
    (fun _ _ => hχ _)

end Langlands.VirtualRepresentation.PadicSupercuspidal

namespace Langlands.VirtualRepresentation.LocalWeil

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- A modulus-one field character pulls back to a modulus-one Weil character. -/
theorem norm_weilCharacter_eq_one (e : Correspondence.ReciprocityCandidate F)
    (χ : Correspondence.QuasiCharacter F) (hχ : ∀ a, ‖(χ a : ℂ)‖ = 1)
    (w : Weil.Local.localWeilGroup F) :
    ‖(LocalFactor.RankOne.weilCharacter F e χ w : ℂ)‖ = 1 :=
  hχ _

/-- Twist the actual unitary Weil lattice by the pullback of a modulus-one
field character along the supplied reciprocity candidate. -/
def unitaryFieldCharacterTwistLatticeEquiv (e : Correspondence.ReciprocityCandidate F)
    (χ : Correspondence.QuasiCharacter F) (hχ : ∀ a, ‖(χ a : ℂ)‖ = 1) :
    UnitaryLattice.{uF, uV} F ≃ₗ[ℤ] UnitaryLattice.{uF, uV} F :=
  unitaryTwistLatticeEquiv F (LocalFactor.RankOne.weilCharacter F e χ)
    (norm_weilCharacter_eq_one F e χ hχ)

end Langlands.VirtualRepresentation.LocalWeil

namespace Langlands.Global.PoleComparison

open Langlands.VirtualRepresentation Langlands.VirtualRepresentation.RelativeGlobal
open Langlands.Global.CompletionPadic Langlands.ClassField.Global
open Langlands.Global.AdelicFunctoriality

variable (F E : Type uF) [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
  (c : FundamentalClass.ClassFamily.{uF}) (v : FinitePlace F)

/-- The generated Weil span is closed under the actual contragredient, and the
isometry carries it to the actual smooth contragredient. -/
def RelativeIsometryDualCompatibility
    (T : weilImage.{uF, uW, uP} F E c v ≃ₗ[ℤ]
      automorphicImage.{uF, uW, uP} F E c v) : Prop :=
  ∀ x : weilImage.{uF, uW, uP} F E c v,
    ∃ h : LocalWeil.unitaryDualLatticeEquiv (padicField v) x.1 ∈
        weilImage.{uF, uW, uP} F E c v,
      (T ⟨_, h⟩ : PadicSupercuspidal.UnitaryLattice.{uF, uF} (padicField v)) =
        PadicSupercuspidal.unitaryContragredientLatticeEquiv (padicField v) (T x).1

/-- For a modulus-one field character `χ`, the generated Weil span is closed
under twisting by `χ` pulled back along `e`, and the isometry carries this twist
to the actual twist by `χ ∘ det`. -/
def RelativeIsometryTwistCompatibility
    (T : weilImage.{uF, uW, uP} F E c v ≃ₗ[ℤ]
      automorphicImage.{uF, uW, uP} F E c v)
    (e : Correspondence.ReciprocityCandidate (padicField v))
    (χ : Correspondence.QuasiCharacter (padicField v)) (hχ : ∀ a, ‖(χ a : ℂ)‖ = 1) :
    Prop :=
  ∀ x : weilImage.{uF, uW, uP} F E c v,
    ∃ h : LocalWeil.unitaryFieldCharacterTwistLatticeEquiv (padicField v) e χ hχ x.1 ∈
        weilImage.{uF, uW, uP} F E c v,
      (T ⟨_, h⟩ : PadicSupercuspidal.UnitaryLattice.{uF, uF} (padicField v)) =
        PadicSupercuspidal.unitaryCharacterTwistLatticeEquiv (padicField v) χ hχ (T x).1

/-- The rank-one Weil class of `χ` pulled back along `e` lies in the generated
span, and the isometry sends it to the actual `GL₁` class of `χ`. -/
def RelativeIsometryCharacterCompatibility
    (T : weilImage.{uF, uW, uP} F E c v ≃ₗ[ℤ]
      automorphicImage.{uF, uW, uP} F E c v)
    (e : Correspondence.ReciprocityCandidate (padicField v))
    (χ : Correspondence.QuasiCharacter (padicField v)) : Prop :=
  ∃ x : weilImage.{uF, uW, uP} F E c v,
    LocalWeil.includeUnitary (padicField v) x.1 =
        generator (⟨1, Correspondence.rankOneWeilCharacterClass.{uF, uW}
          (padicField v) e χ⟩ : LocalWeil.Basis.{uF, uW} (padicField v)) ∧
      PadicSupercuspidal.includeUnitary (padicField v) (T x).1 =
        generator (⟨1, Correspondence.rankOneSupercuspidalClass.{uF, uF}
          (padicField v) χ⟩ : PadicSupercuspidal.Basis.{uF, uF} (padicField v))

/-- The relative analogue of Henniart's Proposition 2.6 (a), contragredient and
twist clauses, and (c), for an isometry. Twist and character clauses use every geometric local
reciprocity candidate and every modulus-one field character. -/
def RelativeIsometryOperations
    (T : weilImage.{uF, uW, uP} F E c v ≃ₗ[ℤ]
      automorphicImage.{uF, uW, uP} F E c v) : Prop :=
  RelativeIsometryDualCompatibility F E c v T ∧
    ∀ e : Correspondence.ReciprocityCandidate (padicField v),
      Correspondence.IsGeometricReciprocity (padicField v) e →
      ∀ (χ : Correspondence.QuasiCharacter (padicField v)) (hχ : ∀ a, ‖(χ a : ℂ)‖ = 1),
        RelativeIsometryTwistCompatibility F E c v T e χ hχ ∧
          RelativeIsometryCharacterCompatibility F E c v T e χ

/-- Under the certified pole comparisons, every generated positive isometry of
the actual relative images satisfies the contragredient, twist and character
clauses of Henniart's Proposition 2.6. -/
def RelativeIsometryOperationStatement : Prop :=
  ∀ (F E : Type uF) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    (c : FundamentalClass.ClassFamily.{uF}),
    RelativeWeilGroup.IsArithmeticClassFamily c →
  ∀ (v : FinitePlace F) (ψ : Correspondence.NontrivialAdditiveCharacter (padicField v)),
    RelativeCertifiedPoleComparisons.{uF, uW, uP} F E c v ψ →
    ∀ T : weilImage.{uF, uW, uP} F E c v ≃ₗ[ℤ] automorphicImage.{uF, uW, uP} F E c v,
      RelativeGeneratedPositiveIsometry F E c v T →
      RelativeIsometryOperations F E c v T

end Langlands.Global.PoleComparison
