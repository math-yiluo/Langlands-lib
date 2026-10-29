import Langlands.Representation.Unitary.Basic
import Langlands.Weil.Representation.UnitaryProof
import Langlands.Weil.Representation.InductionContinuity

/-!
# Restriction of invariant positive forms and actual unitary representations

Precomposition keeps the original carrier and the original positive Hermitian
form. Irreducibility of the restricted representation is not required.
-/

noncomputable section

universe uG uH uJ uV

namespace Langlands

section Forms

variable {G : Type uG} {H : Type uH} {J : Type uJ}
  [Monoid G] [Monoid H] [Monoid J]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V}

namespace InvariantPositiveForm

/-- Restrict the same positive form along an arbitrary monoid homomorphism. -/
def comp (b : InvariantPositiveForm ρ) (φ : H →* G) :
    InvariantPositiveForm (ρ.comp φ) where
  toInnerProductCore := b.toInnerProductCore
  invariant h v w := b.invariant (φ h) v w

@[simp]
theorem comp_inner (b : InvariantPositiveForm ρ) (φ : H →* G) (v w : V) :
    (b.comp φ).inner v w = b.inner v w := rfl

@[simp]
theorem comp_id (b : InvariantPositiveForm ρ) :
    b.comp (MonoidHom.id G) = b := rfl

/-- Iterated precomposition retains precisely the same form. -/
theorem comp_comp (b : InvariantPositiveForm ρ) (φ : H →* G) (ψ : J →* H) :
    (b.comp φ).comp ψ = b.comp (φ.comp ψ) := rfl

end InvariantPositiveForm

/-- Unitarizability is preserved under restriction without topology assumptions. -/
theorem IsUnitarizable.comp (hρ : IsUnitarizable ρ) (φ : H →* G) :
    IsUnitarizable (ρ.comp φ) := by
  obtain ⟨b⟩ := hρ
  exact ⟨b.comp φ⟩

end Forms

namespace FiniteRepresentation

variable {G : Type uG} {H : Type uH} [Group G] [Group H]

/-- Restrict a chosen invariant positive form to the actual restricted action. -/
def restrictInvariantPositiveForm (φ : H →* G)
    {A : FiniteRepresentation.{0, uG, uV} ℂ G}
    (b : InvariantPositiveForm A.representation) :
    InvariantPositiveForm (restrict φ A).representation :=
  b.comp φ

@[simp]
theorem restrictInvariantPositiveForm_inner (φ : H →* G)
    {A : FiniteRepresentation.{0, uG, uV} ℂ G}
    (b : InvariantPositiveForm A.representation) (v w : A) :
    (restrictInvariantPositiveForm φ b).inner v w = b.inner v w := rfl

/-- Restriction preserves the genuine finite-dimensional unitarity predicate. -/
theorem isUnitary_restrict (φ : H →* G)
    {A : FiniteRepresentation.{0, uG, uV} ℂ G} (hA : A.IsUnitary) :
    (restrict φ A).IsUnitary :=
  (isUnitary_iff_isUnitarizable _).mpr
    (((isUnitary_iff_isUnitarizable A).mp hA).comp φ)

/-- Restriction of actual unitary objects, keeping the carrier unchanged. -/
def unitaryRestrict (φ : H →* G)
    (A : {A : FiniteRepresentation.{0, uG, uV} ℂ G // A.IsUnitary}) :
    {B : FiniteRepresentation.{0, uH, uV} ℂ H // B.IsUnitary} :=
  ⟨restrict φ A.val, isUnitary_restrict φ A.property⟩

/-- Restriction on genuine isomorphism classes of unitary objects. The target
includes reducible restrictions. -/
def unitaryRestrictClass (φ : H →* G) :
    IsomorphismClassesWith
        (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsUnitary) →
      IsomorphismClassesWith
        (fun B : FiniteRepresentation.{0, uH, uV} ℂ H => B.IsUnitary) :=
  Quotient.map (unitaryRestrict φ) (fun _ _ ⟨e⟩ => ⟨restrictEquiv φ e⟩)

@[simp]
theorem rank_unitaryRestrict (φ : H →* G)
    (A : {A : FiniteRepresentation.{0, uG, uV} ℂ G // A.IsUnitary}) :
    (unitaryRestrict φ A).val.rank = A.val.rank := rfl

section Continuous

variable [TopologicalSpace G] [TopologicalSpace H]

/-- Restriction of actual continuous unitary objects along a continuous map.
Neither group is required to be a topological group. -/
def continuousUnitaryRestrict (φ : H →* G) (hφ : Continuous φ)
    (A : {A : FiniteRepresentation.{0, uG, uV} ℂ G //
      A.IsContinuous ∧ A.IsUnitary}) :
    {B : FiniteRepresentation.{0, uH, uV} ℂ H //
      B.IsContinuous ∧ B.IsUnitary} :=
  ⟨restrict φ A.val, isContinuous_restrict φ hφ A.property.1,
    isUnitary_restrict φ A.property.2⟩

/-- The continuous unitary restriction construction descends through actual
representation isomorphisms, without requiring the restriction irreducible. -/
def continuousUnitaryRestrictClass (φ : H →* G) (hφ : Continuous φ) :
    IsomorphismClassesWith
        (fun A : FiniteRepresentation.{0, uG, uV} ℂ G =>
          A.IsContinuous ∧ A.IsUnitary) →
      IsomorphismClassesWith
        (fun B : FiniteRepresentation.{0, uH, uV} ℂ H =>
          B.IsContinuous ∧ B.IsUnitary) :=
  Quotient.map (continuousUnitaryRestrict φ hφ)
    (fun _ _ ⟨e⟩ => ⟨restrictEquiv φ e⟩)

@[simp]
theorem rank_continuousUnitaryRestrict (φ : H →* G) (hφ : Continuous φ)
    (A : {A : FiniteRepresentation.{0, uG, uV} ℂ G //
      A.IsContinuous ∧ A.IsUnitary}) :
    (continuousUnitaryRestrict φ hφ A).val.rank = A.val.rank := rfl

end Continuous

end FiniteRepresentation

end Langlands
