import Langlands.ClassFieldTheory.Local.CommonClosureFiniteRestrictions
import Langlands.ClassFieldTheory.Local.IntermediateReciprocityTransport

/-! # Cofinal finite Galois restrictions of actual fixing subgroups -/

noncomputable section

namespace Langlands.LocalClassField.FiniteQuotientTransport

universe u v

variable (K : Type u) [Field K] [PerfectField K]
  (E : FiniteIntermediateExtension K)
  {A : Type v} [Group A] [TopologicalSpace A] [DiscreteTopology A]

/-- Every continuous discrete quotient of a literal fixing subgroup factors
through restriction to a finite Galois overfield of the original base. -/
theorem exists_finiteRestriction_ker_le (f : E.field.fixingSubgroup →ₜ* A) :
    ∃ (M : FiniteGaloisIntermediateField K (AlgebraicClosure K))
      (h : E.field ≤ M.toIntermediateField),
      letI := finiteRestrictionAlgebra K E M h
      (finiteRestrictionHom K E M h).ker ≤ f.toMonoidHom.ker := by
  let : IsGalois K (AlgebraicClosure K) := ⟨⟩
  let V : Set Gal(AlgebraicClosure K/K) :=
    Subtype.val '' (f.toMonoidHom.ker : Set E.field.fixingSubgroup)
  have hfo : IsOpen (f.toMonoidHom.ker : Set E.field.fixingSubgroup) :=
    (isOpen_discrete ({1} : Set A)).preimage f.continuous
  have hVo : IsOpen V := E.field.fixingSubgroup_isOpen.isOpenMap_subtype_val _ hfo
  have hV1 : (1 : Gal(AlgebraicClosure K/K)) ∈ V :=
    ⟨1, f.toMonoidHom.ker.one_mem, rfl⟩
  obtain ⟨M, hM⟩ :=
    (InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois V).mp (hVo.mem_nhds hV1)
  have hME : M.toIntermediateField.fixingSubgroup ≤ E.field.fixingSubgroup := by
    intro σ hσ
    obtain ⟨τ, _, hτ⟩ := hM hσ
    exact hτ ▸ τ.property
  have hEM : E.field ≤ M.toIntermediateField := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup E.field,
      ← InfiniteGalois.fixedField_fixingSubgroup M.toIntermediateField]
    exact IntermediateField.fixedField_le hME
  refine ⟨M, hEM, ?_⟩
  let := finiteRestrictionAlgebra K E M hEM
  rw [finiteRestrictionHom_ker]
  intro σ hσ
  obtain ⟨τ, hτ, hτσ⟩ := hM hσ
  have heq : τ = σ := Subtype.ext hτσ
  exact heq ▸ hτ

variable (M : FiniteGaloisIntermediateField K (AlgebraicClosure K))
  (h : E.field ≤ M.toIntermediateField)

/-- Factor a discrete homomorphism through actual finite Galois restriction,
using its proved kernel containment. -/
def finiteRestrictionFactor (f : E.field.fixingSubgroup →ₜ* A)
    (hf : letI := finiteRestrictionAlgebra K E M h
      (finiteRestrictionHom K E M h).ker ≤ f.toMonoidHom.ker) :
    letI := finiteRestrictionAlgebra K E M h
    Gal(M/E.field) →* A := by
  letI := finiteRestrictionAlgebra K E M h
  exact (QuotientGroup.lift _ f.toMonoidHom hf).comp
    (QuotientGroup.quotientKerEquivOfSurjective (finiteRestrictionHom K E M h)
      (finiteRestriction_surjective K E M h)).symm.toMonoidHom

omit [PerfectField K] [DiscreteTopology A] in
/-- The finite factor agrees with the original map on every fixing automorphism. -/
theorem finiteRestrictionFactor_apply (f : E.field.fixingSubgroup →ₜ* A)
    (hf : letI := finiteRestrictionAlgebra K E M h
      (finiteRestrictionHom K E M h).ker ≤ f.toMonoidHom.ker)
    (σ : E.field.fixingSubgroup) :
    letI := finiteRestrictionAlgebra K E M h
    finiteRestrictionFactor K E M h f hf (finiteRestrictionHom K E M h σ) = f σ := by
  let := finiteRestrictionAlgebra K E M h
  let e := QuotientGroup.quotientKerEquivOfSurjective (finiteRestrictionHom K E M h)
    (finiteRestriction_surjective K E M h)
  change QuotientGroup.lift _ f.toMonoidHom hf (e.symm (finiteRestrictionHom K E M h σ)) = f σ
  have he : e (QuotientGroup.mk σ) = finiteRestrictionHom K E M h σ := rfl
  rw [← he, e.symm_apply_apply]
  rfl

omit [PerfectField K] in
/-- A discrete abelian character factors through the actual finite algebraic abelianization. -/
theorem abelianizationLift_finiteRestrictionFactor [IsMulCommutative A]
    (f : E.field.fixingSubgroup →ₜ* A)
    (hf : letI := finiteRestrictionAlgebra K E M h
      (finiteRestrictionHom K E M h).ker ≤ f.toMonoidHom.ker)
    (x : TopologicalAbelianization E.field.fixingSubgroup) :
    letI := finiteRestrictionAlgebra K E M h
    abelianizationLift f x =
      Abelianization.lift (finiteRestrictionFactor K E M h f hf)
        (finiteAbelianRestriction K E M h x) := by
  let := finiteRestrictionAlgebra K E M h
  induction x using QuotientGroup.induction_on with
  | H σ =>
    change abelianizationLift f (abelianizationProjection _ σ) =
      Abelianization.lift (finiteRestrictionFactor K E M h f hf)
        (finiteAbelianRestriction K E M h (abelianizationProjection _ σ))
    rw [finiteAbelianRestriction_projection]
    change f σ = finiteRestrictionFactor K E M h f hf (finiteRestrictionHom K E M h σ)
    exact (finiteRestrictionFactor_apply K E M h f hf σ).symm

/-- Finite Galois restrictions over the original base separate values in every
literal fixing subgroup's topological abelianization. -/
theorem finiteAbelianRestriction_separates
    (x y : TopologicalAbelianization E.field.fixingSubgroup)
    (heq : ∀ (M : FiniteGaloisIntermediateField K (AlgebraicClosure K))
      (h : E.field ≤ M.toIntermediateField),
      letI := finiteRestrictionAlgebra K E M h
      finiteAbelianRestriction K E M h x = finiteAbelianRestriction K E M h y) : x = y := by
  let : IsGalois K (AlgebraicClosure K) := ⟨⟩
  let : CompactSpace (Field.absoluteGaloisGroup K) :=
    inferInstanceAs (CompactSpace Gal(AlgebraicClosure K/K))
  let : CompactSpace E.field.fixingSubgroup :=
    isCompact_iff_compactSpace.mp E.field.fixingSubgroup_isClosed.isCompact
  let := absoluteGaloisNonarchimedean K
  let : NonarchimedeanGroup E.field.fixingSubgroup :=
    ReciprocitySystemUniqueness.fixingSubgroup_nonarchimedean E.field
  let := abelianizationHausdorff E.field.fixingSubgroup
  let := quotientNonarchimedean (commutator E.field.fixingSubgroup).topologicalClosure
  let P := ProfiniteGrp.of (TopologicalAbelianization E.field.fixingSubgroup)
  apply ProfiniteGrp.toLimit_injective P
  apply Subtype.ext
  funext U
  let : DiscreteTopology (P ⧸ U.toSubgroup) := QuotientGroup.discreteTopology U.isOpen
  let q : P →ₜ* P ⧸ U.toSubgroup :=
    { toMonoidHom := QuotientGroup.mk' U.toSubgroup
      continuous_toFun := QuotientGroup.continuous_mk }
  let f := q.comp (abelianizationProjection E.field.fixingSubgroup)
  obtain ⟨M, h, hf⟩ := exists_finiteRestriction_ker_le K E f
  let := finiteRestrictionAlgebra K E M h
  have hx := abelianizationLift_finiteRestrictionFactor K E M h f hf x
  have hy := abelianizationLift_finiteRestrictionFactor K E M h f hf y
  have hh := congrArg (Abelianization.lift (finiteRestrictionFactor K E M h f hf)) (heq M h)
  rw [← hx, ← hy] at hh
  have hq : abelianizationLift f = q := by
    apply abelianization_hom_ext
    intro σ
    rfl
  rw [hq] at hh
  exact hh

end Langlands.LocalClassField.FiniteQuotientTransport
