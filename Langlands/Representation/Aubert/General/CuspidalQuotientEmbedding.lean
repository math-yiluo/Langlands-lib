import Langlands.Representation.Aubert.General.RationalLeviCuspidalJacquet
import Langlands.Representation.CompactCoefficient.GroupTransport

/-! # Irreducible inducing quotients and preservation of cuspidality -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

universe uG uV uI

open CategoryTheory

namespace Langlands.Aubert.General

section Cuspidal

variable {H : Type uG} [Group H] [TopologicalSpace H] [LocallyCompactSpace H]
  [NonarchimedeanGroup H]

/-- Surjective smooth morphisms preserve vanishing of every Jacquet module
in a fixed family. -/
theorem IsCuspidalFor.of_surjective {κ : Type uI}
    {P M U : κ → Subgroup H}
    {h : ∀ j, IsSemidirectDecomposition (P j) (M j) (U j)}
    {hU : ∀ j, IsClosed (U j : Set H)}
    {A B : SmoothRep.{0, uG, uV} ℂ H}
    (hA : IsCuspidalFor P M U h hU A)
    (q : A ⟶ B) (hq : Function.Surjective (SmoothRep.hom q)) :
    IsCuspidalFor P M U h hU B := by
  intro j
  have := hA j
  exact (CuspidalEmbedding.jacquet_map_surjective (h j) (hU j) q hq).subsingleton

end Cuspidal

/-- The proper-standard-parabolic instance of preservation under quotients. -/
theorem IsLeviCuspidal.of_surjective
    {H : Type uG} [Group H] [TopologicalSpace H] [LocallyCompactSpace H]
    [NonarchimedeanGroup H] {ι : Type uI}
    {P M U : Finset ι → Subgroup H} {hU : ∀ j, IsClosed (U j : Set H)}
    {J : Finset ι} {hM : IsClosed (M J : Set H)}
    {hJ : ∀ I : Finset J,
      IsSemidirectDecomposition ((P (leviIndex J I)).subgroupOf (M J))
        ((M (leviIndex J I)).subgroupOf (M J))
        ((U (leviIndex J I)).subgroupOf (M J))}
    {A B : SmoothRep.{0, uG, uV} ℂ (M J)}
    (hA : IsLeviCuspidal P M U hU J hM hJ A)
    (q : A ⟶ B) (hq : Function.Surjective (SmoothRep.hom q)) :
    IsLeviCuspidal P M U hU J hM hJ B := by
  let := hM.locallyCompactSpace
  exact IsCuspidalFor.of_surjective hA q hq

namespace CuspidalEmbedding

/-- The actual normalized first-adjointness morphism associated with a
Jacquet morphism. -/
def adjointOfJacquetMap
    {H : Type uG} [Group H] [TopologicalSpace H] [LocallyCompactSpace H]
    [NonarchimedeanGroup H] {P M U : Subgroup H}
    (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set H))
    (hδ : IsUnimodularModulus U hU)
    (A : SmoothRep.{0, uG, max uG uV} ℂ H)
    (B : SmoothRep.{0, uG, max uG uV} ℂ M)
    (q : (jacquetFunctor h hU).obj A ⟶ B) :
    A ⟶ (normalizedInductionFunctor h hU).obj B :=
  SmoothRep.ofHom ((General.FirstAdjointness.equiv h hU hδ A B).symm (SmoothRep.hom q))

/-- The named adjoint is injective for a surjection to nonzero data from
the Jacquet module of an irreducible source. -/
theorem adjointOfJacquetMap_injective
    {H : Type uG} [Group H] [TopologicalSpace H] [LocallyCompactSpace H]
    [NonarchimedeanGroup H] {P M U : Subgroup H}
    (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set H))
    (hδ : IsUnimodularModulus U hU)
    (A : SmoothRep.{0, uG, max uG uV} ℂ H) (hA : A.IsIrreducible)
    (B : SmoothRep.{0, uG, max uG uV} ℂ M) [Nontrivial B]
    (q : (jacquetFunctor h hU).obj A ⟶ B) (hq : Function.Surjective (SmoothRep.hom q)) :
    Function.Injective (SmoothRep.hom (adjointOfJacquetMap h hU hδ A B q)) := by
  have : A.representation.IsIrreducible := hA
  apply (Representation.IsIrreducible.injective_or_eq_zero
    (SmoothRep.hom (adjointOfJacquetMap h hU hδ A B q))).resolve_right
  intro hzero
  have hqzero : SmoothRep.hom q = 0 := by
    have heq := congrArg (General.FirstAdjointness.equiv h hU hδ A B) hzero
    simpa only [adjointOfJacquetMap, SmoothRep.hom_ofHom,
      LinearEquiv.apply_symm_apply, map_zero] using heq
  obtain ⟨b, hb⟩ := exists_ne (0 : B)
  obtain ⟨a, ha⟩ := hq b
  apply hb
  rw [← ha, hqzero]
  rfl

/-- Pullback keeps the vector carrier and therefore its nontriviality. -/
theorem nontrivial_pullback
    {H N : Type uG} [Group H] [TopologicalSpace H]
    [Group N] [TopologicalSpace N]
    (e : H ≃ₜ* N) (A : SmoothRep.{0, uG, uV} ℂ N) [Nontrivial A] :
    Nontrivial ((SmoothRep.pullbackFunctor e).obj A) := by
  change Nontrivial A
  infer_instance

/-- A nonzero Jacquet module of an irreducible representation has an
irreducible quotient which gives an actual induction embedding. The target
Levi may be identified by an arbitrary continuous group equivalence. -/
theorem exists_irreducible_quotient_embedding
    {H N : Type uG} [Group H] [TopologicalSpace H] [LocallyCompactSpace H]
    [NonarchimedeanGroup H] [Group N] [TopologicalSpace N]
    {P M U : Subgroup H}
    (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set H))
    (hδ : IsUnimodularModulus U hU)
    [CompactSpace (Induction.LeftQuotient P)]
    (e : M ≃ₜ* N)
    (A : SmoothRep.{0, uG, max uG uV} ℂ H) (hA : A.IsIrreducible)
    [Nontrivial ((jacquetFunctor h hU).obj A)] :
    ∃ B : SmoothRep.{0, uG, max uG uV} ℂ N,
      B.IsIrreducible ∧
      ∃ q : (SmoothRep.pullbackFunctor e.symm).obj ((jacquetFunctor h hU).obj A) ⟶ B,
        Function.Surjective (SmoothRep.hom q) ∧
        SmoothRep.IsSubrepresentation A
          ((normalizedInductionFunctor h hU).obj ((SmoothRep.pullbackFunctor e).obj B)) := by
  have : A.representation.IsIrreducible := hA
  have hfg : Module.Finite (MonoidAlgebra ℂ H) A.representation.asModule := inferInstance
  let rA := (jacquetFunctor h hU).obj A
  have hfgR : Module.Finite (MonoidAlgebra ℂ M) rA.representation.asModule :=
    JacquetFiniteGeneration.finite_of_compactQuotient h hU A hfg
  obtain ⟨B', hB', q, hq⟩ := exists_irreducible_quotient_of_finite rA hfgR
  let B := (SmoothRep.pullbackFunctor e.symm).obj B'
  have hB : B.IsIrreducible :=
    (Langlands.isIrreducible_comp_continuousMulEquiv_iff B'.representation e.symm).mpr hB'
  have : B'.representation.IsIrreducible := hB'
  have : Nontrivial B' :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ M) B'.representation.asModule
  have : Nontrivial B := nontrivial_pullback e.symm B'
  have : Nontrivial ((SmoothRep.pullbackFunctor e).obj B) := nontrivial_pullback e B
  refine ⟨B, hB, (SmoothRep.pullbackFunctor e.symm).map q, hq, ?_⟩
  exact ⟨adjointOfJacquetMap h hU hδ A
      ((SmoothRep.pullbackFunctor e).obj B) (roundTripPullbackMap e q),
    adjointOfJacquetMap_injective h hU hδ A hA
      ((SmoothRep.pullbackFunctor e).obj B) (roundTripPullbackMap e q) hq⟩

end CuspidalEmbedding

end Langlands.Aubert.General
