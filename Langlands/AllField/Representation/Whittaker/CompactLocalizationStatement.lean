import Langlands.Representation.Whittaker.CompactLocalizationStatement
import Langlands.AllField.Group.GL.PadicUpperUnipotent
/-! # Character localization of compact induction in unipotent groups over local fields

A derived statement target using the actual compact induction and
character-relation quotients. This module does not prove the target.
-/

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding CompactLocalizationStatement
open Langlands.AllField.Whittaker

universe uF uV

/-- Compact induction from any closed subgroup of the upper-unipotent group over a
nonarchimedean local field, with the topology of the supplied data `T`, preserves the
full character quotient, as a complex vector space. -/
def CompactLocalizationStatement : Prop :=
  ∀ (F : Type uF) [Field F] (T : LocalFieldData F),
    letI := T.topology
    ∀ (n : ℕ),
      letI := T.generalLinearTopologicalGroup (n + 1)
      let U := GeneralLinear.upperUnipotent (n + 1) F
      ∀ (H : Subgroup U), IsClosed (H : Set U) →
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (σ : Representation ℂ H V), IsSmooth σ →
      ∀ (θ : Induction.SmoothCharacter ℂ U),
        Nonempty
          (Jacquet.Localization.Coinvariants (Induction.compactInduced H σ)
              (⊤ : Subgroup U) (θ.toMonoidHom.comp (⊤ : Subgroup U).subtype) ≃ₗ[ℂ]
            Jacquet.Localization.Coinvariants σ (⊤ : Subgroup H)
              ((θ.toMonoidHom.comp H.subtype).comp (⊤ : Subgroup H).subtype))

end Langlands.AllField.Whittaker
