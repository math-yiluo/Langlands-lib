import Langlands.Global.HeckeCharacter
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.RingTheory.Frobenius
import Mathlib.GroupTheory.Index
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Finite abelian class-field targets on actual idele classes

Existence and uniqueness are assertions to prove, not data fields. The
normalization uses arithmetic Frobenius. The comparison with the actual
adelic norm, and the construction of the global Weil group, remain separate.
-/

noncomputable section

universe u v

namespace Langlands.Global

open NumberField

/-- At every unramified finite place, every local uniformizer maps to
arithmetic residue Frobenius at every prime above it. -/
def HasArithmeticArtinNormalization
    {K : Type u} {L : Type v} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (ρ : IdeleClasses K →* (L ≃ₐ[K] L)) : Prop :=
  ∀ (v : FinitePlace K) (w : FinitePlace L),
    w.asIdeal.LiesOver v.asIdeal →
    Algebra.IsUnramifiedAt (RingOfIntegers K) w.asIdeal →
    ∀ π : (FiniteCompletion K v)ˣ,
      Valued.v (π : FiniteCompletion K v) = WithZero.exp (-1 : ℤ) →
      (RingOfIntegers.mapAlgHom
        (ρ (finiteClassInclusion K v π))).IsArithFrobAt w.asIdeal

/-- Finite abelian Artin reciprocity: the normalized continuous surjection
to the actual finite Galois group exists and is unique. -/
def FiniteAbelianArtinReciprocityStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (L : Type v) [Field L] [NumberField L] [Algebra K L] [IsGalois K L],
    (∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ) →
    letI : TopologicalSpace (L ≃ₐ[K] L) := ⊥
    ∃! ρ : IdeleClasses K →ₜ* (L ≃ₐ[K] L),
      Function.Surjective ρ ∧ HasArithmeticArtinNormalization ρ.toMonoidHom

/-- Open subgroups of a number field's actual idele-class group have
finite index. This finiteness is an assertion, not part of `OpenSubgroup`. -/
def OpenIdeleClassSubgroupFiniteIndexStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (H : OpenSubgroup (IdeleClasses K)), H.toSubgroup.FiniteIndex

/-- Every open finite-index subgroup is the kernel of normalized
reciprocity for an actual finite abelian field in the algebraic closure. -/
def FiniteAbelianClassFieldExistenceStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (H : OpenSubgroup (IdeleClasses K)), H.toSubgroup.FiniteIndex →
    ∃ (L : IntermediateField K (AlgebraicClosure K))
      (hfin : FiniteDimensional K L),
      letI := hfin
      letI := NumberField.of_module_finite K L
      IsGalois K L ∧
      (∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ) ∧
      (letI : TopologicalSpace (L ≃ₐ[K] L) := ⊥
       ∃ ρ : IdeleClasses K →ₜ* (L ≃ₐ[K] L),
         Function.Surjective ρ ∧
         HasArithmeticArtinNormalization ρ.toMonoidHom ∧
         ρ.toMonoidHom.ker = H.toSubgroup)

/-- Among finite abelian subfields of a fixed algebraic closure, equal
normalized reciprocity kernels determine the same actual subfield. -/
def FiniteAbelianClassFieldKernelRigidityStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (L E : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K L] [FiniteDimensional K E]
    [IsGalois K L] [IsGalois K E],
    letI := NumberField.of_module_finite K L
    letI := NumberField.of_module_finite K E
    (∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ) →
    (∀ σ τ : E ≃ₐ[K] E, σ * τ = τ * σ) →
    letI : TopologicalSpace (L ≃ₐ[K] L) := ⊥
    letI : TopologicalSpace (E ≃ₐ[K] E) := ⊥
    ∀ (ρ : IdeleClasses K →ₜ* (L ≃ₐ[K] L))
      (τ : IdeleClasses K →ₜ* (E ≃ₐ[K] E)),
      Function.Surjective ρ → Function.Surjective τ →
      HasArithmeticArtinNormalization ρ.toMonoidHom →
      HasArithmeticArtinNormalization τ.toMonoidHom →
      ρ.toMonoidHom.ker = τ.toMonoidHom.ker → L = E

/-- A finite-order Hecke character is a faithful character of an actual
finite abelian Galois quotient, pulled back by normalized reciprocity. -/
def FiniteOrderHeckeArtinRealizationStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (χ : HeckeCharacter K), χ.HasFiniteOrder →
    ∃ (L : IntermediateField K (AlgebraicClosure K))
      (hfin : FiniteDimensional K L),
      letI := hfin
      letI := NumberField.of_module_finite K L
      IsGalois K L ∧
      (∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ) ∧
      (letI : TopologicalSpace (L ≃ₐ[K] L) := ⊥
       ∃ (ρ : IdeleClasses K →ₜ* (L ≃ₐ[K] L))
         (θ : (L ≃ₐ[K] L) →ₜ* ℂˣ),
         Function.Surjective ρ ∧ Function.Injective θ ∧
         HasArithmeticArtinNormalization ρ.toMonoidHom ∧
         ∀ x, θ (ρ x) = χ x)

/-- The finite abelian reciprocity, subgroup classification and finite-order
character realization prerequisites, with all existence assertions explicit. -/
def FiniteAbelianClassFieldStatement : Prop :=
  FiniteAbelianArtinReciprocityStatement.{u,v} ∧
  OpenIdeleClassSubgroupFiniteIndexStatement.{u} ∧
  FiniteAbelianClassFieldExistenceStatement.{u} ∧
  FiniteAbelianClassFieldKernelRigidityStatement.{u} ∧
  FiniteOrderHeckeArtinRealizationStatement.{u}

end Langlands.Global
