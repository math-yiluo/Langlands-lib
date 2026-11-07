import Langlands.Automorphic.WeakInductionAssociationStatement
import Langlands.Global.Factors.RelativeWeilBrauer

/-!
# Continuity, rank and exact classes of induced reciprocity representations

These are unconditional structural steps toward weak induction association.
No local or global reciprocity existence theorem is used.
-/

noncomputable section

set_option autoImplicit false

universe u uV uG uH

namespace Langlands.VirtualRepresentation.ExactGrothendieckGroup

variable {G : Type uG} {H : Type uH} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G]

/-- On a genuine continuous representation, exact virtual induction along an
open embedding is the class of its algebraic induction. -/
theorem continuousInduceAlong_ofRepresentationWithProof (φ : H →ₜ* G)
    (hφ : Topology.IsOpenEmbedding φ) [φ.toMonoidHom.range.FiniteIndex]
    (A : FiniteRepresentation.{0, uH, uV} ℂ H) (hA : A.IsContinuous) :
    continuousInduceAlong φ hφ (ofRepresentation _ ⟨A, hA⟩) =
      ofRepresentation _
        ⟨FiniteRepresentation.induceAlong φ.toMonoidHom hφ.injective A,
          FiniteRepresentation.isContinuous_induceAlong φ.toMonoidHom hφ hA⟩ := by
  simp only [continuousInduceAlong, LinearMap.comp_apply, continuousRestrict,
    restrict_ofRepresentation, continuousInduce, induce_ofRepresentation]
  rfl

end Langlands.VirtualRepresentation.ExactGrothendieckGroup

namespace Langlands.ClassField.Global.RelativeWeilGroup

open scoped NumberField
open Langlands.Global Langlands.Automorphic Langlands.VirtualRepresentation

variable (c : FundamentalClass.ClassFamily.{u})
  (F E' L : Type u) [Field F] [NumberField F] [Field E'] [NumberField E']
  [Field L] [NumberField L] [Algebra F E'] [Algebra F L] [Algebra E' L]
  [IsScalarTower F E' L] [IsGalois F L]
  (h : FundamentalClass.Restriction c)

section Discrete

attribute [local instance] relativeGaloisTopology

/-- The relative Weil subgroup attached to the intermediate field has index
equal to the degree of that intermediate field. -/
theorem index_range_restrictionInclusion :
    (restrictionInclusion c F L E' h).toMonoidHom.range.index =
      Module.finrank F E' := by
  have : IsGalois E' L := IsGalois.tower_top_of_isGalois F E' L
  rw [range_restrictionInclusion,
    Subgroup.index_comap_of_surjective _ (projection_surjective c F L)]
  let φ : (L ≃ₐ[E'] L) →* (L ≃ₐ[F] L) := AlgEquiv.restrictScalarsHom F
  have hc : Nat.card φ.range = Module.finrank E' L := by
    rw [← Nat.card_congr (MonoidHom.ofInjective
      (AlgEquiv.restrictScalarsHom_injective F)).toEquiv]
    exact IsGalois.card_aut_eq_finrank E' L
  apply Nat.eq_of_mul_eq_mul_right (Module.finrank_pos (R := E') (M := L))
  calc
    φ.range.index * Module.finrank E' L = Nat.card (L ≃ₐ[F] L) := by
      rw [← hc, Subgroup.index_mul_card]
    _ = Module.finrank F L := IsGalois.card_aut_eq_finrank F L
    _ = Module.finrank F E' * Module.finrank E' L :=
      (Module.finrank_mul_finrank F E' L).symm

/-- Inducing the reciprocity character has the expected intermediate-field rank
in every carrier universe. -/
@[simp]
theorem inducedReciprocityRepresentation_rank (ξ : HeckeCharacter E') :
    (inducedReciprocityRepresentation.{u, uV} c F E' L h ξ).rank =
      Module.finrank F E' := by
  have : IsGalois E' L := IsGalois.tower_top_of_isGalois F E' L
  rw [inducedReciprocityRepresentation, FiniteRepresentation.rank_induceAlong,
    FiniteRepresentation.characterLine_rank, mul_one,
    index_range_restrictionInclusion]

/-- The algebraically induced reciprocity representation is continuous for the
discrete finite Galois topology used to construct its induction. -/
theorem inducedReciprocityRepresentation_isContinuous_discrete (ξ : HeckeCharacter E') :
    (inducedReciprocityRepresentation.{u, uV} c F E' L h ξ).IsContinuous := by
  have : IsGalois E' L := IsGalois.tower_top_of_isGalois F E' L
  exact FiniteRepresentation.isContinuous_induceAlong
    (restrictionInclusion c F L E' h).toMonoidHom
    (isOpenEmbedding_restrictionInclusion c F L E' h)
    (FiniteRepresentation.characterLine_isContinuous
      (continuousReciprocityCharacter c E' L ξ))

/-- The continuous exact class of the induced reciprocity representation is
induction of the exact character-line class. -/
theorem inducedReciprocityRepresentation_class (ξ : HeckeCharacter E') :
    haveI : IsGalois E' L := IsGalois.tower_top_of_isGalois F E' L
    ExactGrothendieckGroup.ofRepresentation _
        ⟨inducedReciprocityRepresentation.{u, uV} c F E' L h ξ,
          inducedReciprocityRepresentation_isContinuous_discrete c F E' L h ξ⟩ =
      ExactGrothendieckGroup.continuousInduceAlong
        (restrictionInclusion c F L E' h)
        (isOpenEmbedding_restrictionInclusion c F L E' h)
        (ExactGrothendieckGroup.characterClass.{u, uV}
          (continuousReciprocityCharacter c E' L ξ)) := by
  have : IsGalois E' L := IsGalois.tower_top_of_isGalois F E' L
  exact (ExactGrothendieckGroup.continuousInduceAlong_ofRepresentationWithProof
    (restrictionInclusion c F L E' h)
    (isOpenEmbedding_restrictionInclusion c F L E' h)
    (FiniteRepresentation.characterLine.{u, uV} (reciprocityCharacter c E' L ξ))
    (FiniteRepresentation.characterLine_isContinuous
      (continuousReciprocityCharacter c E' L ξ))).symm

end Discrete

/-- The same algebraic representation is continuous for the default Krull
topology on the finite Galois quotient. -/
theorem inducedReciprocityRepresentation_isContinuous (ξ : HeckeCharacter E') :
    (inducedReciprocityRepresentation.{u, uV} c F E' L h ξ).IsContinuous := by
  have key : ∀ t : TopologicalSpace (L ≃ₐ[F] L),
      relativeGaloisTopology F L = t →
        letI := t
        (inducedReciprocityRepresentation.{u, uV} c F E' L h ξ).IsContinuous := by
    rintro t rfl
    exact inducedReciprocityRepresentation_isContinuous_discrete c F E' L h ξ
  exact key _ (krullTopology_eq_relativeGaloisTopology F L).symm


/-- The actual induced reciprocity representation bundled with its proved
continuity, for use as a genuine object of the continuous exact virtual group. -/
def continuousInducedReciprocityRepresentation (ξ : HeckeCharacter E') :
    {A : FiniteRepresentation.{0, u, max u uV} ℂ (RelativeWeilGroup c F L) //
      A.IsContinuous} :=
  ⟨inducedReciprocityRepresentation.{u, uV} c F E' L h ξ,
    inducedReciprocityRepresentation_isContinuous c F E' L h ξ⟩

end Langlands.ClassField.Global.RelativeWeilGroup
