import Langlands.GroupScheme.Torus.WeilRestrictionEmbeddingLattices
import Langlands.Algebra.EmbeddingContinuity

/-! # Continuous Galois actions on Weil-restriction lattices -/

set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.Algebra.SeparableTensor

namespace Langlands.GroupScheme.WeilGm

variable (k K Ω : Type u) [Field k] [Field K] [Field Ω]
  [Algebra k K] [Algebra k Ω] [FiniteDimensional k K]
  [Finite (K →ₐ[k] Ω)] (h : Function.Bijective (embeddingEvaluation k K Ω))

private abbrev embeddingBaseChange : CommGroupScheme (Spec (CommRingCat.of.{u} Ω)) :=
  (CommGroupScheme.baseChange (algebraBaseMap k Ω)).obj
    (commGroupScheme (CommRingCat.of.{u} k) K)

local notation "W_Ω" => embeddingBaseChange k K Ω

section Characters

variable [TopologicalSpace (characterLattice (embeddingBaseChange k K Ω))]
  [DiscreteTopology (characterLattice (embeddingBaseChange k K Ω))]

/-- The continuous actual Galois action on the discrete character lattice. -/
def embeddingCharacterContinuousAction :
    C((Ω ≃ₐ[k] Ω) × characterLattice W_Ω, characterLattice W_Ω) where
  toFun p := characterLattice.galoisRepresentation k Ω (commGroupScheme (CommRingCat.of k) K)
    p.1 p.2
  continuous_toFun := by
    let e := embeddingCharacterEquiv k K Ω h
    have he : Continuous e := continuous_of_discreteTopology
    have hei : Continuous e.symm := continuous_of_discreteTopology
    have hf := hei.comp ((embeddingContinuousRepresentation k K Ω).continuous.comp
      (continuous_fst.prodMk (he.comp continuous_snd)))
    refine hf.congr fun p => ?_
    apply e.injective
    exact (e.apply_symm_apply _).trans
      (embeddingCharacterEquiv_galoisRepresentation k K Ω h p.1 p.2).symm

@[simp] theorem embeddingCharacterContinuousAction_apply
    (σ : Ω ≃ₐ[k] Ω) (χ : characterLattice W_Ω) :
    embeddingCharacterContinuousAction k K Ω h (σ, χ) =
      characterLattice.galoisRepresentation k Ω (commGroupScheme (CommRingCat.of k) K) σ χ :=
  rfl

end Characters

section Cocharacters

variable [TopologicalSpace (cocharacterLattice (embeddingBaseChange k K Ω))]
  [DiscreteTopology (cocharacterLattice (embeddingBaseChange k K Ω))]

/-- The continuous actual Galois action on the discrete cocharacter lattice. -/
def embeddingCocharacterContinuousAction :
    C((Ω ≃ₐ[k] Ω) × cocharacterLattice W_Ω, cocharacterLattice W_Ω) where
  toFun p := cocharacterLattice.galoisRepresentation k Ω (commGroupScheme (CommRingCat.of k) K)
    p.1 p.2
  continuous_toFun := by
    let e := embeddingCocharacterEquiv k K Ω h
    have he : Continuous e := continuous_of_discreteTopology
    have hei : Continuous e.symm := continuous_of_discreteTopology
    have hf := hei.comp ((embeddingContinuousRepresentation k K Ω).continuous.comp
      (continuous_fst.prodMk (he.comp continuous_snd)))
    refine hf.congr fun p => ?_
    apply e.injective
    exact (e.apply_symm_apply _).trans
      (embeddingCocharacterEquiv_galoisRepresentation k K Ω h p.1 p.2).symm

@[simp] theorem embeddingCocharacterContinuousAction_apply
    (σ : Ω ≃ₐ[k] Ω) (ν : cocharacterLattice W_Ω) :
    embeddingCocharacterContinuousAction k K Ω h (σ, ν) =
      cocharacterLattice.galoisRepresentation k Ω (commGroupScheme (CommRingCat.of k) K) σ ν :=
  rfl

end Cocharacters

end Langlands.GroupScheme.WeilGm
