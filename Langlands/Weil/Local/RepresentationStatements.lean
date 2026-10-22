import Langlands.Weil.Local.Parameters
import Langlands.Weil.Representation.Twist
import Langlands.WeilDeligne.FrobeniusStatements

/-!
# Structure statements for representations of the actual local Weil group

Every arithmetic input is obtained from the supplied finite p-adic field.
These are proposition definitions, without any assumed classification,
continuity bridge, or local assembly theorem.
-/

noncomputable section

namespace Langlands.Weil.Local

universe u v

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

/-- The full continuity bridge at actual local inertia, with usual complex
module topologies and the closed-kernel condition retained. -/
def LocalWeilContinuityFor : Prop :=
  ∀ A : LocalWeilRepresentation.{u, v} F,
    letI : TopologicalSpace A := moduleTopology ℂ A
    (A.IsContinuous ↔
      ∀ x : A, Continuous (fun g : localWeilGroup F => A.representation g x)) ∧
    (A.IsContinuous ↔
      Continuous (fun x : localWeilGroup F × A => A.representation x.1 x.2)) ∧
    (A.IsContinuous ↔ A.HasOpenInertiaKernel (localInertia F)) ∧
    (A.IsContinuous ↔
      IsOpen (A.representation.ker : Set (localWeilGroup F))) ∧
    (A.HasOpenInertiaKernel (localInertia F) ↔
      A.HasFiniteInertiaImage (localInertia F) ∧
        IsClosed (A.inertiaKernel (localInertia F) : Set (localInertia F)))

/-- Extension to the actual absolute Galois group is equivalent to continuous
finite image; on the same carrier the continuous extension is unique. -/
def LocalWeilGaloisTypeFor : Prop :=
  ∀ A : LocalWeilRepresentation.{u, v} F,
    (IsLocalGaloisType F A ↔ A.IsContinuous ∧ A.HasFiniteImage) ∧
    (A.IsContinuous → A.HasFiniteImage →
      ∃! τ : Representation ℂ (Field.absoluteGaloisGroup F.Carrier) A,
        (FiniteRepresentation.of τ).IsContinuous ∧
          τ.comp (localProjection F).toMonoidHom = A.representation)

/-- A general representation admits a commuting unramified correction on its
actual carrier which makes its image finite and of actual Galois type. -/
def LocalWeilUnramifiedCorrectionFor : Prop :=
  ∀ A : LocalWeilRepresentation.{u, v} F, A.IsContinuous →
    ∃ τ σ : Representation ℂ (localWeilGroup F) A,
      (FiniteRepresentation.of τ).IsContinuous ∧
      (FiniteRepresentation.of τ).IsUnramified (localInertia F) ∧
      (∀ g h : localWeilGroup F, Commute (A.representation g) (τ h)) ∧
      (∀ g : localWeilGroup F, σ g = A.representation g * τ g) ∧
      (FiniteRepresentation.of σ).IsContinuous ∧
      (FiniteRepresentation.of σ).HasFiniteImage ∧
      IsLocalGaloisType F (FiniteRepresentation.of σ)

/-- For irreducibles the correction is a scalar unramified character, and
finite order of the determinant exactly characterizes finite image. -/
def LocalWeilIrreducibleReductionFor : Prop :=
  ∀ A : LocalWeilRepresentation.{u, v} F,
    A.IsContinuous → A.IsIrreducible →
    (∃ (z : ℂˣ) (B : LocalWeilRepresentation.{u, v} F),
      B.IsContinuous ∧ B.IsIrreducible ∧ B.HasFiniteImage ∧
      IsLocalGaloisType F B ∧
      Nonempty (FiniteRepresentation.Equiv A
        (FiniteRepresentation.twist (localUnramifiedCharacter F z).toMonoidHom B))) ∧
    (A.HasFiniteImage ↔
      ∃ n : ℕ, 0 < n ∧
        ∀ g : localWeilGroup F, LinearMap.det (A.representation g) ^ n = 1)

/-- Every unramified character is uniquely the actual degree character with
its value at geometric Frobenius. Continuity is a conclusion here. -/
def LocalUnramifiedCharacterClassificationFor : Prop :=
  ∀ χ : localWeilGroup F →* ℂˣ,
    (∀ i : localInertia F, χ i = 1) ↔
      Continuous χ ∧ ∃! z : ℂˣ,
        (localUnramifiedCharacter F z).toMonoidHom = χ ∧
          z = χ (localGeometricFrobenius F)

/-- Determinant and rank-one characters are actual continuous characters,
uniquely quantified rather than supplied in normalization data. -/
def LocalWeilCharacterNormalizationFor : Prop :=
  ∀ A : LocalWeilRepresentation.{u, v} F, A.IsContinuous →
    (∃! δ : localWeilGroup F →ₜ* ℂˣ,
      ∀ g : localWeilGroup F, (δ g : ℂ) = LinearMap.det (A.representation g)) ∧
    (A.rank = 1 →
      ∃! χ : localWeilGroup F →ₜ* ℂˣ,
        Nonempty (FiniteRepresentation.Equiv A
          (FiniteRepresentation.of (Langlands.characterRepresentation χ.toMonoidHom))) ∧
        ∀ g : localWeilGroup F, (χ g : ℂ) = LinearMap.det (A.representation g))

/-- Every usual-topology continuous character of the actual local Weil group
satisfies the algebraic inertia condition needed for parameter twisting. -/
def LocalCharacterInertiaFor : Prop :=
  ∀ χ : localWeilGroup F →ₜ* ℂˣ,
    IsOpen ((χ.toMonoidHom.comp (localInertia F).subtype).ker :
      Set (localInertia F)) ∧
    (Set.range (χ.toMonoidHom.comp (localInertia F).subtype)).Finite

/-- The actual norm detects the degree kernel and has no nontrivial
root-of-unity value at nonzero degree. -/
def LocalNormFaithfulnessFor : Prop :=
  (localNormCharacter F).toMonoidHom.ker = localInertia F ∧
  ∀ (g : localWeilGroup F), localDegreeInt F g ≠ 0 →
    ∀ n : ℤ, n ≠ 0 → localNormCharacter F g ^ n ≠ 1

/-- The actual local norm, degree and inertia satisfy the arithmetic hypotheses
of the generic Frobenius-semisimplification and block targets, in the exact
form those targets consume. -/
def LocalFrobeniusHypothesesFor : Prop :=
  WeilDeligneRepresentation.Frobenius.NormCompatible
      (ν := (localNormCharacter F).toMonoidHom) (localDegree F).toMonoidHom
      F.canonicalTopologicalData.residueCardinality ∧
  CompactSpace (localDegree F).toMonoidHom.ker

/-- The complete local continuity, structure and normalization family for
every prime, field universe, and independently chosen carrier universe. -/
def LocalWeilRepresentationStatements : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p),
    LocalWeilContinuityFor.{u, v} F ∧
    LocalWeilGaloisTypeFor.{u, v} F ∧
    LocalWeilUnramifiedCorrectionFor.{u, v} F ∧
    LocalWeilIrreducibleReductionFor.{u, v} F ∧
    LocalUnramifiedCharacterClassificationFor F ∧
    LocalWeilCharacterNormalizationFor.{u, v} F ∧
    LocalCharacterInertiaFor F ∧
    LocalNormFaithfulnessFor F ∧
    LocalFrobeniusHypothesesFor F

end Langlands.Weil.Local
