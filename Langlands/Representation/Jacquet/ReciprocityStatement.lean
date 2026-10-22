import Langlands.Representation.Induction.Definitions
import Langlands.Representation.Jacquet.Coinvariants
import Mathlib.Basic.Complex.Basic

namespace Langlands.Jacquet

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [Module ℂ V]
variable [AddCommGroup W] [Module ℂ W]

/-- Frobenius reciprocity through actual coinvariants, with an explicit smooth
character and its inverse. Identifying that character with a parabolic
half-modulus is a separate specialization. -/
def CharacterReciprocityStatement : Prop :=
  ∀ [IsTopologicalGroup G] [T2Space G],
    (∀ O : Set G, IsOpen O → (1 : G) ∈ O →
      ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ O) →
    ∀ (P N : Subgroup G) (hNP : N ≤ P)
      (hPN : P ≤ Subgroup.normalizer N),
      IsClosed (P : Set G) →
      ∀ (rho : Representation ℂ G V) (sigma : Representation ℂ P W)
        (chi : Induction.SmoothCharacter ℂ P),
        IsSmooth rho → IsSmooth sigma →
        (∀ (n : N) (w : W), sigma ⟨(n : G), hNP n.property⟩ w = w) →
        (∀ n : N, chi.toMonoidHom ⟨(n : G), hNP n.property⟩ = 1) →
        ∃ e :
          (rho.IntertwiningMap (Induction.normalizedSmoothInduced P chi sigma)) ≃ₗ[ℂ]
          ((twist chi.toMonoidHom⁻¹ (action rho N P hPN)).IntertwiningMap sigma),
          ∀ f v,
            e f (mk rho N v) =
              Induction.eval P (twist chi.toMonoidHom sigma) (f v) 1

end Langlands.Jacquet
