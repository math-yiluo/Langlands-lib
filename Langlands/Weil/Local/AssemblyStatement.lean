import Langlands.Weil.Local.Assembly
import Mathlib.Topology.Algebra.Nonarchimedean.Basic

namespace Langlands.Weil.Local

universe u

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

/-- Arithmetic, inertia, topology and character properties of the actual construction. -/
def LocalAssemblyProperties : Prop :=
  (F.canonicalTopologicalData.residueCardinality = Nat.card (localResidueField F)) ∧
  (∀ w : localWeilGroup F,
    localResidueMap F (localProjection F w) =
      Galois.FiniteField.geometricFrobenius (localResidueField F) ^ localDegreeInt F w) ∧
  Function.Injective (localProjection F) ∧
  DenseRange (localProjection F) ∧
  Function.Surjective (localDegree F) ∧
  localInertia F =
    (F.absoluteInertia F.canonicalTopologicalData).comap (localProjection F).toMonoidHom ∧
  Set.range (localInertiaInclusion F) = (localInertia F : Set (localWeilGroup F)) ∧
  Topology.IsOpenEmbedding (localInertiaInclusion F) ∧
  IsOpen (localInertia F : Set (localWeilGroup F)) ∧
  IsCompact (localInertia F : Set (localWeilGroup F)) ∧
  (localInertia F).Normal ∧
  (∃ e : localInertia F ≃ₜ* F.absoluteInertia F.canonicalTopologicalData,
    ∀ i : localInertia F,
      (e i : Field.absoluteGaloisGroup F.Carrier) = localProjection F i) ∧
  NonarchimedeanGroup (localWeilGroup F) ∧
  LocallyCompactSpace (localWeilGroup F) ∧
  T2Space (localWeilGroup F) ∧
  TotallyDisconnectedSpace (localWeilGroup F) ∧
  localDegree F (localGeometricFrobenius F) = Multiplicative.ofAdd (1 : ℤ) ∧
  localResidueMap F (localProjection F (localGeometricFrobenius F)) =
    Galois.FiniteField.geometricFrobenius (localResidueField F) ∧
  (∀ w : localWeilGroup F,
    (localNormCharacter F w : ℂ) =
      (F.canonicalTopologicalData.residueCardinality : ℂ) ^ (-localDegreeInt F w)) ∧
  (localNormCharacter F (localGeometricFrobenius F) : ℂ) =
    (F.canonicalTopologicalData.residueCardinality : ℂ)⁻¹ ∧
  (∀ (z : ℂˣ) (i : localInertia F), localUnramifiedCharacter F z i = 1) ∧
  (∀ z : ℂˣ, localUnramifiedCharacter F z (localGeometricFrobenius F) = z)

/-- The full actual local Weil interface, for every prime `p` and every finite extension
of `ℚ_p`. -/
def LocalAssemblyStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p), LocalAssemblyProperties F

end Langlands.Weil.Local
