import Langlands.GroupScheme.IdentityJetLocalBases
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Finite identity neighborhoods in separated group schemes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.IdentityJet

variable {S : Scheme.{u}} (G : GroupScheme S)

private theorem ideal_le_identityKer (n : ℕ) : ideal G n ≤ G.identitySection.ker := by
  intro U
  exact Ideal.pow_le_self (Nat.succ_ne_zero n)

/-- The identity section factors through its order-`n` neighborhood. -/
def identityLift (n : ℕ) : S ⟶ scheme G n :=
  G.identitySection.toImage ≫ Scheme.IdealSheafData.inclusion (ideal_le_identityKer G n)

@[reassoc (attr := simp)]
theorem identityLift_inclusion (n : ℕ) : identityLift G n ≫ inclusion G n = G.identitySection := by
  let h := ideal_le_identityKer G n
  calc
    _ = G.identitySection.toImage ≫ (Scheme.IdealSheafData.inclusion h ≫ (ideal G n).subschemeι) :=
      Category.assoc _ _ _
    _ = G.identitySection.toImage ≫ G.identitySection.imageι :=
      congrArg (G.identitySection.toImage ≫ ·) (Scheme.IdealSheafData.inclusion_subschemeι h)
    _ = _ := G.identitySection.toImage_imageι

@[reassoc (attr := simp)]
theorem identityLift_projection (n : ℕ) : identityLift G n ≫ projection G n = 𝟙 S := by
  simp [projection, G.identitySection_comp]

variable [IsSeparated G.X.hom]

private theorem identity_closedImmersion : IsClosedImmersion G.identitySection := by
  let : IsClosedImmersion (G.identitySection ≫ G.X.hom) := by
    rw [G.identitySection_comp]
    infer_instance
  exact IsClosedImmersion.of_comp G.identitySection G.X.hom

theorem range_inclusion_eq_range_identitySection (n : ℕ) :
    Set.range (inclusion G n) = Set.range G.identitySection := by
  let : IsClosedImmersion G.identitySection := identity_closedImmersion G
  change Set.range ((G.identitySection.ker ^ (n + 1)).subschemeι) = _
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_pow_succ,
    Scheme.Hom.support_ker, G.identitySection.isClosedEmbedding.isClosed_range.closure_eq]

/-- The lifted identity meets every scheme point of the identity neighborhood. -/
theorem surjective_identityLift (n : ℕ) : Surjective (identityLift G n) := by
  constructor
  intro x
  have hx : inclusion G n x ∈ Set.range G.identitySection :=
    range_inclusion_eq_range_identitySection G n ▸ ⟨x, rfl⟩
  obtain ⟨s, hs⟩ := hx
  refine ⟨s, (inclusion G n).isClosedEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, identityLift_inclusion, hs]

/-- Identity jet schemes are finite over the base before affineness of the
ambient group is known. -/
theorem finite_projection [LocallyOfFiniteType G.X.hom] (n : ℕ) :
    IsFinite (projection G n) := by
  let : Surjective (identityLift G n) := surjective_identityLift G n
  have hleft : Function.LeftInverse (projection G n) (identityLift G n) := fun y => by
    rw [← Scheme.Hom.comp_apply, identityLift_projection]
    rfl
  have hinj : Function.Injective (projection G n) := by
    intro x x' h
    obtain ⟨y, rfl⟩ := (surjective_identityLift G n).1 x
    obtain ⟨y', rfl⟩ := (surjective_identityLift G n).1 x'
    rw [hleft, hleft] at h
    rw [h]
  let : LocallyOfFiniteType (projection G n) := inferInstanceAs
    (LocallyOfFiniteType (inclusion G n ≫ G.X.hom))
  let : IsSeparated (projection G n) := inferInstanceAs
    (IsSeparated (inclusion G n ≫ G.X.hom))
  let : UniversallyClosed (identityLift G n ≫ projection G n) := by
    rw [identityLift_projection]
    infer_instance
  let : UniversallyClosed (projection G n) :=
    UniversallyClosed.of_comp_surjective (identityLift G n) (projection G n)
  let : IsProper (projection G n) := by constructor
  let : LocallyQuasiFinite (projection G n) := LocallyQuasiFinite.of_injective hinj
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

end Langlands.GroupScheme.IdentityJet
