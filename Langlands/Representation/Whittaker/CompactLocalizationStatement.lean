import Langlands.Group.GL.PadicUpperUnipotent
import Langlands.Representation.Induction.Definitions
import Langlands.Representation.Jacquet.Localization
import Mathlib.Analysis.Complex.Basic

/-! # Character localization of compact induction in p-adic unipotent groups

A derived statement target using the actual compact induction and
character-relation quotients. This module does not prove the target.
-/

namespace Langlands.Whittaker

universe uF uV

/-- Compact induction from any closed subgroup of the p-adic upper-unipotent
group preserves the full character quotient, as a complex vector space. -/
def CompactLocalizationStatement : Prop :=
  ∀ (p : ℕ) (_hp : Fact p.Prime) (F : PadicField.{uF} p),
    letI := F.canonicalTopologicalData.topology
    ∀ (n : ℕ),
      letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (n + 1)
      let U := GeneralLinear.upperUnipotent (n + 1) F.Carrier
      ∀ (H : Subgroup U), IsClosed (H : Set U) →
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (σ : Representation ℂ H V), IsSmooth σ →
      ∀ (θ : Induction.SmoothCharacter ℂ U),
        Nonempty
          (Jacquet.Localization.Coinvariants (Induction.compactInduced H σ)
              (⊤ : Subgroup U) (θ.toMonoidHom.comp (⊤ : Subgroup U).subtype) ≃ₗ[ℂ]
            Jacquet.Localization.Coinvariants σ (⊤ : Subgroup H)
              ((θ.toMonoidHom.comp H.subtype).comp (⊤ : Subgroup H).subtype))

end Langlands.Whittaker
