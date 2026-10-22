import Langlands.Weil.Local.ExtensionParameters
import Langlands.Weil.Representation.Dual
import Langlands.Weil.Representation.SumsTensor
import Langlands.Weil.Representation.Twist
import Langlands.WeilDeligne.FrobeniusStatements

/-!
# Restriction and induction statements along an extension of p-adic fields

Proposition definitions for the actual local Weil groups of `F` and `E` and the
published restriction and induction constructors along `extensionWeilMap F E f`.
No preservation result beyond the published constructors is assumed.
-/

noncomputable section

namespace Langlands.Weil.Local

universe u v w w'

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
  (f : F.Carrier →ₐ[Padic p] E.Carrier)

/-- Restriction to `W_E` preserves and reflects usual continuity, open inertia
kernel, finite image and semisimplicity. -/
def LocalExtensionRestrictionFor : Prop :=
  ∀ A : LocalWeilRepresentation.{u, w} F,
    ((extensionRestrict F E f A).IsContinuous ↔ A.IsContinuous) ∧
    ((extensionRestrict F E f A).HasOpenInertiaKernel (localInertia E) ↔
      A.HasOpenInertiaKernel (localInertia F)) ∧
    ((extensionRestrict F E f A).HasFiniteImage ↔ A.HasFiniteImage) ∧
    ((extensionRestrict F E f A).IsSemisimple ↔ A.IsSemisimple)

/-- Induction to `W_F` preserves and reflects usual continuity, open inertia
kernel, finite image and semisimplicity. -/
def LocalExtensionInductionFor : Prop :=
  ∀ B : LocalWeilRepresentation.{v, w} E,
    ((extensionInduce F E f B).IsContinuous ↔ B.IsContinuous) ∧
    ((extensionInduce F E f B).HasOpenInertiaKernel (localInertia F) ↔
      B.HasOpenInertiaKernel (localInertia E)) ∧
    ((extensionInduce F E f B).HasFiniteImage ↔ B.HasFiniteImage) ∧
    ((extensionInduce F E f B).IsSemisimple ↔ B.IsSemisimple)

/-- Restriction and induction of pairs preserve and reflect the Frobenius-semisimple
parameter condition, each side using its own actual inertia and geometric degree.
Nonzero monodromy is allowed. -/
def LocalExtensionParameterFor : Prop :=
  (∀ A : LocalWeilDeligneRepresentation.{u, w} F,
    IsLocalFrobeniusSemisimpleParameter E (extensionWDRestrict F E f A) ↔
      IsLocalFrobeniusSemisimpleParameter F A) ∧
  ∀ B : LocalWeilDeligneRepresentation.{v, w} E,
    IsLocalFrobeniusSemisimpleParameter F (extensionWDInduce F E f B) ↔
      IsLocalFrobeniusSemisimpleParameter E B

/-- Restriction and induction carry an actual Frobenius semisimplification to an
actual Frobenius semisimplification, for the geometric degrees of `E` and `F`.
The degree of `F` restricts to the residue degree times that of `E`. -/
def LocalExtensionSemisimplificationFor : Prop :=
  (∀ (A : LocalWeilDeligneRepresentation.{u, w} F)
      (A' : LocalWeilDeligneRepresentation.{u, w'} F),
    WeilDeligneRepresentation.Frobenius.IsSemisimplification
        (localDegree F).toMonoidHom A A' →
      WeilDeligneRepresentation.Frobenius.IsSemisimplification
        (localDegree E).toMonoidHom
        (extensionWDRestrict F E f A) (extensionWDRestrict F E f A')) ∧
  ∀ (B : LocalWeilDeligneRepresentation.{v, w} E)
      (B' : LocalWeilDeligneRepresentation.{v, w'} E),
    WeilDeligneRepresentation.Frobenius.IsSemisimplification
        (localDegree E).toMonoidHom B B' →
      WeilDeligneRepresentation.Frobenius.IsSemisimplification
        (localDegree F).toMonoidHom
        (extensionWDInduce F E f B) (extensionWDInduce F E f B')

/-- Frobenius reciprocity on both sides: induction is left and right adjoint to
restriction, witnessed by an actual unit and an actual counit intertwiner. -/
def LocalExtensionReciprocityFor : Prop :=
  ∀ B : LocalWeilRepresentation.{v, w} E,
    (∃ η : B.representation.IntertwiningMap
        (extensionRestrict F E f (extensionInduce F E f B)).representation,
      ∀ (A : LocalWeilRepresentation.{u, w'} F)
        (φ : B.representation.IntertwiningMap (extensionRestrict F E f A).representation),
        ∃! Φ : (extensionInduce F E f B).representation.IntertwiningMap A.representation,
          Φ.toLinearMap ∘ₗ η.toLinearMap = φ.toLinearMap) ∧
    (∃ ε : (extensionRestrict F E f (extensionInduce F E f B)).representation.IntertwiningMap
        B.representation,
      ∀ (A : LocalWeilRepresentation.{u, w'} F)
        (φ : (extensionRestrict F E f A).representation.IntertwiningMap B.representation),
        ∃! Φ : A.representation.IntertwiningMap (extensionInduce F E f B).representation,
          ε.toLinearMap ∘ₗ Φ.toLinearMap = φ.toLinearMap)

/-- Induction commutes with sums, duals and twists by restricted characters, and
satisfies the projection formula. -/
def LocalExtensionOperationsFor : Prop :=
  ∀ (B : LocalWeilRepresentation.{v, w} E) (B' : LocalWeilRepresentation.{v, w'} E)
    (A : LocalWeilRepresentation.{u, w'} F) (χ : localWeilGroup F →* ℂˣ),
    Nonempty (FiniteRepresentation.Equiv (extensionInduce F E f (B.sum B'))
      ((extensionInduce F E f B).sum (extensionInduce F E f B'))) ∧
    Nonempty (FiniteRepresentation.Equiv (extensionInduce F E f B.dual)
      (extensionInduce F E f B).dual) ∧
    Nonempty (FiniteRepresentation.Equiv
      (extensionInduce F E f (B.twist (χ.comp (extensionWeilMap F E f).toMonoidHom)))
      ((extensionInduce F E f B).twist χ)) ∧
    Nonempty (FiniteRepresentation.Equiv
      (extensionInduce F E f (B.tensor (extensionRestrict F E f A)))
      ((extensionInduce F E f B).tensor A))

/-- The complete restriction/induction family along every embedding of p-adic
fields, with independent field and carrier universes. -/
def LocalExtensionStatements : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    (f : F.Carrier →ₐ[Padic p] E.Carrier),
    LocalExtensionRestrictionFor.{u, v, w} F E f ∧
    LocalExtensionInductionFor.{u, v, w} F E f ∧
    LocalExtensionParameterFor.{u, v, w} F E f ∧
    LocalExtensionSemisimplificationFor.{u, v, w, w'} F E f ∧
    LocalExtensionReciprocityFor.{u, v, w, w'} F E f ∧
    LocalExtensionOperationsFor.{u, v, w, w'} F E f

end Langlands.Weil.Local
