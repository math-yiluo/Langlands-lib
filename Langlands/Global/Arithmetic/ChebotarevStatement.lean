import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Frobenius
import Mathlib.RepresentationTheory.Character
import Mathlib.Analysis.Complex.Basic

/-!
# Finite Galois Frobenius realization and character rigidity

These are proposition definitions, not proofs of the assertions.
-/

noncomputable section

universe u v w z

namespace Langlands.Global

open NumberField IsDedekindDomain

/-- Every automorphism of a finite Galois number-field extension occurs as
arithmetic Frobenius above an unramified prime outside any finite set. -/
def ChebotarevPrimeRealizationStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (L : Type v) [Field L] [NumberField L] [Algebra K L] [IsGalois K L],
    ∀ (σ : L ≃ₐ[K] L) (S : Finset (HeightOneSpectrum (RingOfIntegers K))),
      ∃ p : HeightOneSpectrum (RingOfIntegers K), p ∉ S ∧
        ∃ q : HeightOneSpectrum (RingOfIntegers L),
          q.asIdeal.LiesOver p.asIdeal ∧
          Algebra.IsUnramifiedAt (RingOfIntegers K) q.asIdeal ∧
          (RingOfIntegers.mapAlgHom σ).IsArithFrobAt q.asIdeal

/-- Finite-dimensional complex representations of an actual finite Galois
group are determined by their unramified Frobenius traces outside a finite set. -/
def FiniteGaloisFrobeniusRigidityStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (L : Type v) [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (V : Type w) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (W : Type z) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ (L ≃ₐ[K] L) V)
    (τ : Representation ℂ (L ≃ₐ[K] L) W)
    (S : Finset (HeightOneSpectrum (RingOfIntegers K))),
    (∀ (p : HeightOneSpectrum (RingOfIntegers K)), p ∉ S →
      ∀ (q : HeightOneSpectrum (RingOfIntegers L)),
        q.asIdeal.LiesOver p.asIdeal →
        Algebra.IsUnramifiedAt (RingOfIntegers K) q.asIdeal →
        ∀ σ : L ≃ₐ[K] L,
          (RingOfIntegers.mapAlgHom σ).IsArithFrobAt q.asIdeal →
          ρ.character σ = τ.character σ) →
      Nonempty (ρ.Equiv τ)

/-- The coherent finite Galois Chebotarev and representation-rigidity input. -/
def ChebotarevRigidityStatement : Prop :=
  ChebotarevPrimeRealizationStatement.{u, v} ∧
  FiniteGaloisFrobeniusRigidityStatement.{u, v, w, z}

end Langlands.Global
