import Langlands.Weil.Local.ExtensionParameters
import Langlands.Weil.Representation.InductionContinuity

/-!
# Usual-topology continuity along a finite extension

The actual Weil map `W_E → W_F` of a finite extension is continuous and an open
embedding with finite-index image, so restriction from `W_F` to `W_E` and
induction from `W_E` to `W_F` preserve usual-topology continuity, for Weil
representations and for the underlying representations of Weil-Deligne pairs.
-/

noncomputable section

universe u v w

namespace Langlands.Weil.Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
  (f : F.Carrier →ₐ[Padic p] E.Carrier)

/-! ## Weil representations -/

/-- Restriction on genuine classes of usual-topology continuous representations. -/
def extensionContinuousRestrictClass :
    FiniteRepresentation.IsomorphismClassesWith
      (fun A : LocalWeilRepresentation.{u, w} F => A.IsContinuous) →
    FiniteRepresentation.IsomorphismClassesWith
      (fun A : LocalWeilRepresentation.{v, w} E => A.IsContinuous) :=
  FiniteRepresentation.continuousRestrictClass (extensionWeilMap F E f).toMonoidHom
    (extensionWeilMap F E f).continuous

/-- Induction from `W_E` to `W_F` preserves usual-topology continuity. -/
theorem isContinuous_extensionInduce {A : LocalWeilRepresentation.{v, w} E}
    (hA : A.IsContinuous) : (extensionInduce F E f A).IsContinuous :=
  FiniteRepresentation.isContinuous_induceAlong (extensionWeilMap F E f).toMonoidHom
    (extensionWeilMap_isOpenEmbedding F E f) hA

/-- Induction of usual-topology continuous representations. -/
def extensionContinuousInduce (A : LocalContinuousWeilObjects.{v, w} E) :
    LocalContinuousWeilObjects.{u, max u w} F :=
  ⟨extensionInduce F E f A.val, isContinuous_extensionInduce F E f A.property⟩

/-- Induction on genuine classes of usual-topology continuous representations. -/
def extensionContinuousInduceClass :
    FiniteRepresentation.IsomorphismClassesWith
      (fun A : LocalWeilRepresentation.{v, w} E => A.IsContinuous) →
    FiniteRepresentation.IsomorphismClassesWith
      (fun A : LocalWeilRepresentation.{u, max u w} F => A.IsContinuous) :=
  FiniteRepresentation.continuousInduceAlongClass (extensionWeilMap F E f).toMonoidHom
    (extensionWeilMap_isOpenEmbedding F E f)

/-! ## Weil-Deligne pairs -/

/-- Restriction of a pair with continuous underlying representation is continuous. -/
theorem isContinuous_extensionWDRestrict {A : LocalWeilDeligneRepresentation.{u, w} F}
    (hA : A.IsContinuous) : (extensionWDRestrict F E f A).IsContinuous :=
  isContinuous_extensionRestrict F E f (A := A.toFiniteRepresentation) hA

/-- Induction of a pair with continuous underlying representation is continuous. -/
theorem isContinuous_extensionWDInduce {A : LocalWeilDeligneRepresentation.{v, w} E}
    (hA : A.IsContinuous) : (extensionWDInduce F E f A).IsContinuous :=
  isContinuous_extensionInduce F E f (A := A.toFiniteRepresentation) hA

end Langlands.Weil.Local
