import Langlands.Representation.Jacquet.CanonicalLiftDefinitions
import Langlands.Representation.Smooth.Contragredient.Definitions
import Langlands.Representation.Smooth.Contragredient.LawsProof

/-!
# Evaluation duality between compact compression stable images

Statements only. On a finite-dimensional space of `K`-fixed vectors, the
evaluation pairing identifies the stable image of compression by `g⁻¹` on the
actual smooth contragredient with the full dual of the stable image of
compression by `g` on the representation. No Jacquet quotient, opposite
parabolic, admissibility or canonical chosen equivalence is involved.
-/

namespace Langlands.Jacquet

universe uG uV

section Clause

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Some complex linear equivalence from the stable image of compression by
`g⁻¹` on the smooth contragredient to the full dual of the stable image of
compression by `g` on `ρ` is evaluation on every pair of stable-image vectors. -/
def CompactCompressionStableEvaluationDuality (ρ : Representation ℂ G V)
    (hρ : IsSmooth ρ) (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G) :
    Prop :=
  ∃ E : stableImage (smoothContragredient ρ) (isSmooth_smoothContragredient ρ) K hK g⁻¹
      ≃ₗ[ℂ] Module.Dual ℂ (stableImage ρ hρ K hK g),
    ∀ (ℓ : stableImage (smoothContragredient ρ) (isSmooth_smoothContragredient ρ) K hK g⁻¹)
      (v : stableImage ρ hρ K hK g),
      E ℓ v =
        smoothDualPairing ρ
          (stableImageToRepresentation (smoothContragredient ρ)
            (isSmooth_smoothContragredient ρ) K hK g⁻¹ ℓ)
          (stableImageToRepresentation ρ hρ K hK g v)

end Clause

/-- Evaluation duality between the stable images of compression by `g⁻¹` on the
smooth contragredient and by `g` on the representation, for every `g` and every
compact open subgroup with finite-dimensional fixed vectors, for every smooth
complex representation of every topological group. -/
def CompactCompressionStableDualityStatement : Prop :=
  ∀ {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G),
    FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup) →
      CompactCompressionStableEvaluationDuality ρ hρ K hK g

end Langlands.Jacquet
