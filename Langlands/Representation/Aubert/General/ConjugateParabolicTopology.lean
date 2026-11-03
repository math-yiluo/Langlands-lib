import Langlands.Representation.Aubert.General.ConjugateParabolic
import Langlands.Representation.Aubert.General.Conjugation

/-! # Topology of actual conjugate parabolic data -/

noncomputable section

namespace Langlands.Aubert.General

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Continuity of the actual Levi projection is invariant under conjugation. -/
theorem continuous_projection_conj {P M U P' M' U' : Subgroup G}
    (h : IsSemidirectDecomposition P M U)
    (h' : IsSemidirectDecomposition P' M' U') (g : G)
    (hPP' : ∀ x : G, x ∈ P' ↔ g⁻¹ * x * g ∈ P)
    (hMM' : ∀ x : G, x ∈ M' ↔ g⁻¹ * x * g ∈ M)
    (hUU' : ∀ x : G, x ∈ U' ↔ g⁻¹ * x * g ∈ U)
    (hp : Continuous h.projection) : Continuous h'.projection := by
  have hc : Continuous (fun p : P' =>
      (conjugationEquiv g hMM').symm
        (h.projection (conjugationEquiv g hPP' p))) :=
    (conjugationEquiv g hMM').symm.continuous.comp
      (hp.comp (conjugationEquiv g hPP').continuous)
  apply hc.congr
  intro p
  apply (conjugationEquiv g hMM').injective
  simpa only [ContinuousMulEquiv.apply_symm_apply] using
    (projection_conj h h' g hPP' hMM' hUU' p).symm

/-- The specified actual Levi in a conjugated decomposition has continuous
projection whenever the original decomposition does. -/
theorem IsSemidirectDecomposition.continuous_conjugateWithLevi_projection
    {P M U N : Subgroup G} (h : IsSemidirectDecomposition P M U)
    (hp : Continuous h.projection) (g : G)
    (hMN : ∀ x : G, x ∈ N ↔ g⁻¹ * x * g ∈ M) :
    Continuous (h.conjugateWithLevi g hMN).projection :=
  continuous_projection_conj h (h.conjugateWithLevi g hMN) g
    (mem_conjugateSubgroup g P) hMN (mem_conjugateSubgroup g U) hp

/-- Inverse conjugation on representatives identifies the actual left coset
spaces for any literal conjugation-membership witness. -/
def conjugationLeftQuotientHomeomorph (g : G) {P Q : Subgroup G}
    (hPQ : ∀ x : G, x ∈ Q ↔ g⁻¹ * x * g ∈ P) :
    Induction.LeftQuotient Q ≃ₜ Induction.LeftQuotient P :=
  Homeomorph.Quotient.congr
    ((Homeomorph.mulLeft g⁻¹).trans (Homeomorph.mulRight g)) (by
      intro x y
      rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply]
      change y * x⁻¹ ∈ Q ↔ (g⁻¹ * y * g) * (g⁻¹ * x * g)⁻¹ ∈ P
      rw [hPQ]
      simp [mul_assoc])

@[simp]
theorem conjugationLeftQuotientHomeomorph_mk (g : G) {P Q : Subgroup G}
    (hPQ : ∀ x : G, x ∈ Q ↔ g⁻¹ * x * g ∈ P) (x : G) :
    conjugationLeftQuotientHomeomorph g hPQ (Induction.quotientMap Q x) =
      Induction.quotientMap P (g⁻¹ * x * g) := rfl

@[simp]
theorem conjugationLeftQuotientHomeomorph_symm_mk (g : G) {P Q : Subgroup G}
    (hPQ : ∀ x : G, x ∈ Q ↔ g⁻¹ * x * g ∈ P) (x : G) :
    (conjugationLeftQuotientHomeomorph g hPQ).symm (Induction.quotientMap P x) =
      Induction.quotientMap Q (g * x * g⁻¹) := by
  apply (conjugationLeftQuotientHomeomorph g hPQ).injective
  rw [(conjugationLeftQuotientHomeomorph g hPQ).apply_symm_apply,
    conjugationLeftQuotientHomeomorph_mk]
  simp [mul_assoc]

/-- The actual conjugate subgroup has the inverse-conjugation quotient
homeomorphism, with the inherited quotient topologies. -/
def conjugateLeftQuotientHomeomorph (g : G) (P : Subgroup G) :
    Induction.LeftQuotient (conjugateSubgroup g P) ≃ₜ Induction.LeftQuotient P :=
  conjugationLeftQuotientHomeomorph g (mem_conjugateSubgroup g P)

@[simp]
theorem conjugateLeftQuotientHomeomorph_mk (g : G) (P : Subgroup G) (x : G) :
    conjugateLeftQuotientHomeomorph g P
        (Induction.quotientMap (conjugateSubgroup g P) x) =
      Induction.quotientMap P (g⁻¹ * x * g) := rfl

@[simp]
theorem conjugateLeftQuotientHomeomorph_symm_mk (g : G) (P : Subgroup G) (x : G) :
    (conjugateLeftQuotientHomeomorph g P).symm (Induction.quotientMap P x) =
      Induction.quotientMap (conjugateSubgroup g P) (g * x * g⁻¹) :=
  conjugationLeftQuotientHomeomorph_symm_mk g (mem_conjugateSubgroup g P) x

/-- Compactness of the actual left coset space survives conjugating the subgroup. -/
theorem compactSpace_leftQuotient_conjugateSubgroup (g : G) (P : Subgroup G)
    [CompactSpace (Induction.LeftQuotient P)] :
    CompactSpace (Induction.LeftQuotient (conjugateSubgroup g P)) :=
  (conjugateLeftQuotientHomeomorph g P).symm.compactSpace

end Langlands.Aubert.General
