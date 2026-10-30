import Langlands.Group.GL.Maps
import Langlands.Representation.Smooth.Contragredient.Definitions
import Mathlib.Analysis.Complex.Basic
import Mathlib.RepresentationTheory.Irreducible

/-!
# Gelfand–Kazhdan realization of the smooth contragredient

This is the inverse-transpose formulation of Bernstein–Zelevinsky (1976),
Theorem 7.3, as a proposition definition. It is proved in
`GelfandKazhdanProof`. Its hypotheses do not include genericity.
-/

namespace Langlands

universe uF uV

/-- Inverse transpose realizes the actual smooth dual of every irreducible
admissible complex representation of a positive-rank p-adic general linear group. -/
def GelfandKazhdanContragredientStatement : Prop :=
  ∀ (p : ℕ) (_hp : Fact p.Prime) (F : PadicField.{uF} p),
    letI := F.canonicalNormedField
    ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (Matrix.GeneralLinearGroup (Fin (n + 1)) F.Carrier) V),
      IsAdmissible ρ → Representation.IsIrreducible ρ →
      ∃ E : V ≃ₗ[ℂ] SmoothDual ρ, ∀ g v,
        E (ρ (GeneralLinear.inverseTranspose (n + 1) F.Carrier g) v) =
          smoothContragredient ρ g (E v)

end Langlands
