import Langlands.Representation.Aubert.General.RationalSupportCategoryTargets
import Langlands.Representation.Aubert.General.RationalCuspidalEmbeddingProof
import Langlands.Representation.Aubert.General.RationalInductionDualityReduction
import Langlands.Representation.Aubert.General.RationalUnipotentRegularity
import Langlands.BruhatTits.Parabolic.QuotientCompactProof

/-! # Cuspidal-series existence on actual rational points -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep
open Langlands.AlgebraicGeometry.PointTopology

/-- Renard VI.2.1 on the actual standard rational-point families, at the
hypothesis scope of `RationalCuspidalSeriesExistenceStatement`, once every
actual standard parabolic has compact coset space `P \ G`. The compact-limit
property of the standard unipotent radicals is discharged from
`hStandard`; no endpoint statement is used. -/
theorem rationalCuspidalSeriesExistence_of_compactSpace
    (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) :
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    ∀ [LocallyCompactSpace (RationalPoint k G.X)]
      [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
      (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
      (hStandard : StandardCocharacterStatement.{u})
      (hInter : StandardLeviIntersectionStatement.{u})
      (hRoots : HasRelativeRootSystem i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
      (hM : ∀ I, IsClosed (levi i ν I : Set (RationalPoint k G.X)))
      (_hCompact : ∀ I, CompactSpace (Induction.LeftQuotient (parabolic i ν I))),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      CuspidalSeriesExistenceTarget.{u, u, max (u + 1) v}
        (P := parabolic i ν) (M := levi i ν) (U := unipotent i ν)
        (h := isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν)
        (hU := hU) (hM := hM)
        (hL := isSemidirectDecomposition_in_levi i ν hInter hG hi hν) := by
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hInter hRoots hU hM hCompact
  let : Fintype (SimpleRoot i ν) := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  let h := isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν
  let hL := isSemidirectDecomposition_in_levi i ν hInter hG hi hν
  have hUc : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν I) :=
    fun I => standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν hStandard hG hi hν I
  intro π hπ
  have : π.representation.IsIrreducible := hπ
  -- A nonzero vector of `π`.
  obtain ⟨v₀, hv₀⟩ : ∃ x : π, x ≠ 0 := by
    have : Nontrivial π.representation.asModule :=
      IsSimpleModule.nontrivial (MonoidAlgebra ℂ (RationalPoint k G.X)) _
    exact exists_ne (0 : π.representation.asModule)
  -- The standard indices with nonzero actual Jacquet module.
  let S : Set (Finset (SimpleRoot i ν)) :=
    {I | Nontrivial ((jacquetFunctor.{u, max (u + 1) v} (h I) (hU I)).obj π)}
  have hbot : ∀ x : RationalPoint k G.X, x ∈ unipotent i ν Finset.univ → x = 1 := by
    intro x hx
    rw [unipotent_univ_eq_bot i ν] at hx
    exact Subgroup.mem_bot.mp hx
  have huniv : Finset.univ ∈ S := by
    refine ⟨⟨Jacquet.Localization.mk π.representation (unipotent i ν Finset.univ) 1 v₀,
      0, ?_⟩⟩
    intro hzero
    apply hv₀
    have hmem := (Jacquet.Localization.mk_eq_zero _ _ _ v₀).1 hzero
    have hle : Jacquet.Localization.relations π.representation
        (unipotent i ν Finset.univ) 1 ≤ ⊥ := by
      apply Submodule.span_le.2
      rintro _ ⟨⟨x, b⟩, rfl⟩
      have hx : (x : RationalPoint k G.X) = 1 := hbot x x.2
      simp [hx]
    exact (Submodule.mem_bot ℂ).1 (hle hmem)
  -- A standard index of minimal cardinality with nonzero Jacquet module.
  obtain ⟨I, hI, hImin⟩ :=
    (measure (Finset.card : Finset (SimpleRoot i ν) → ℕ)).wf.has_min S ⟨_, huniv⟩
  have hsmall : ∀ K : Finset I, K ≠ Finset.univ →
      Subsingleton ((jacquetFunctor.{u, max (u + 1) v} (h (leviIndex I K))
        (hU (leviIndex I K))).obj π) := by
    intro K hK
    rw [← not_nontrivial_iff_subsingleton]
    intro hns
    apply hImin (leviIndex I K) hns
    change (leviIndex I K).card < I.card
    rw [card_leviIndex]
    calc K.card < (Finset.univ : Finset I).card :=
          Finset.card_lt_card (Finset.ssubset_univ_iff.2 hK)
      _ = I.card := by rw [Finset.card_univ, Fintype.card_coe]
  let := (hM I).locallyCompactSpace
  -- Cuspidality of the minimal nonzero Jacquet module.
  have hcusp : IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) hU I (hM I) (hL I)
      ((jacquetFunctor.{u, max (u + 1) v} (h I) (hU I)).obj π) := by
    intro K
    have hsub := leviIndex_subset I K.1
    have hWN : unipotent i ν (leviIndex I K.1) ≤
        Subgroup.normalizer (unipotent i ν I : Set (RationalPoint k G.X)) :=
      (unipotent_le_parabolic_of_subset i ν hInter hG hi hν _ I hsub).trans
        (h I).le_normalizer
    apply CuspidalEmbedding.subsingleton_jacquet_of_forall_mem_relations
    apply CuspidalEmbedding.mem_relations_of_subsingleton (h I) (hU I)
      (unipotent i ν (leviIndex I K.1))
    · intro x hx
      change x ∈ (unipotent i ν (leviIndex I K.1) : Set (RationalPoint k G.X)) at hx
      rw [unipotent_product_of_subset i ν hInter hG hi hν _ I hsub] at hx
      exact Set.mem_mul.mp hx
    · intro w hwV
      apply (Jacquet.inverseHalfCharacter_eq_one _ _).2
      exact CuspidalEmbedding.closedNormalizerCharacter_eq_one_of_compactLimit
        (unipotent i ν I) (unipotent i ν (leviIndex I K.1)) (hU I) hWN
        (hUc (leviIndex I K.1)) ⟨w, hwV⟩
    · exact hsmall K.1 K.2
  -- Finite generation and an irreducible quotient.
  have hfg : Module.Finite (MonoidAlgebra ℂ (RationalPoint k G.X))
      π.representation.asModule := inferInstance
  have := hCompact I
  let rI := (jacquetFunctor.{u, max (u + 1) v} (h I) (hU I)).obj π
  have : Nontrivial rI := hI
  have : Module.Finite (MonoidAlgebra ℂ (levi i ν I)) rI.representation.asModule :=
    JacquetFiniteGeneration.finite_of_compactQuotient (h I) (hU I) π hfg
  have hco : IsCoatomic (Subrepresentation rI.representation) :=
    (Subrepresentation.subrepresentationSubmoduleOrderIso
      (ρ := rI.representation)).isCoatomic_iff.mpr inferInstance
  obtain ⟨T₀, hT₀⟩ : ∃ T₀ : Subrepresentation rI.representation, IsCoatom T₀ := by
    rcases hco.eq_top_or_exists_le_coatom ⊥ with hbot' | ⟨T₀, hT₀, -⟩
    · exfalso
      obtain ⟨y, hy⟩ := exists_ne (0 : rI)
      apply hy
      have hmem : y ∈ (⊥ : Subrepresentation rI.representation) := by
        rw [hbot']
        exact Submodule.mem_top
      exact hmem
    · exact ⟨T₀, hT₀⟩
  let σ := SmoothRep.quotient rI T₀
  have hσ : σ.IsIrreducible :=
    SmoothRep.RenardIrreducibleExistence.quotient_isIrreducible_of_isCoatom rI T₀ hT₀
  let q : rI ⟶ σ := SmoothRep.mkQ rI T₀
  have hq : Function.Surjective (SmoothRep.hom q) := SmoothRep.mkQ_surjective rI T₀
  -- The quotient is again cuspidal.
  have hσcusp : IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) hU I (hM I) (hL I)
      σ := by
    intro K
    have := hcusp K
    exact (CuspidalEmbedding.jacquet_map_surjective (hL I K.1) _ q hq).subsingleton
  -- First adjointness and irreducibility give an embedding into cuspidal induction.
  let F := (RationalPointFamily.FirstAdjointness.equiv i ν hStandard hG hi hν I (hU I)
    π σ).symm (SmoothRep.hom q)
  have hF : F ≠ 0 := by
    intro hF0
    have : σ.representation.IsIrreducible := hσ
    have : Nontrivial σ.representation.asModule :=
      IsSimpleModule.nontrivial (MonoidAlgebra ℂ (levi i ν I)) _
    obtain ⟨s, hs⟩ := exists_ne (0 : σ.representation.asModule)
    obtain ⟨y, hy⟩ := hq s
    apply hs
    have hq0 : SmoothRep.hom q = 0 := by
      have := congrArg (RationalPointFamily.FirstAdjointness.equiv i ν hStandard hG hi hν I
        (hU I) π σ) hF0
      simpa [F] using this
    rw [← hy, hq0]
    rfl
  have hinj : Function.Injective F :=
    (Representation.IsIrreducible.injective_or_eq_zero F).resolve_right hF
  -- An actual subrepresentation is an actual subquotient.
  exact ⟨I, hπ, σ, hσ, hσcusp,
    SmoothRep.IsSubrepresentation.isSubquotient ⟨SmoothRep.ofHom F, hinj⟩⟩

/-- `RationalCuspidalSeriesExistenceStatement` follows from compactness of the
coset spaces of actual dynamic parabolics. -/
theorem rationalCuspidalSeriesExistence_of_dynamicParabolicQuotientCompact
    (hcompact : BruhatTits.DynamicParabolicQuotientCompactStatement.{u}) :
    RationalCuspidalSeriesExistenceStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hInter hRoots hU hM
  exact rationalCuspidalSeriesExistence_of_compactSpace.{u, v} k G hG T i hi ν hν hStandard
    hInter hRoots hU hM
    (fun I => compactSpace_leftQuotient_parabolic i ν hcompact hStandard hG hi hν I)

/-- Renard, Corollaire VI.2.1, on the actual standard rational-point families:
every irreducible smooth representation lies in some actual cuspidal series. -/
theorem rationalCuspidalSeriesExistence :
    RationalCuspidalSeriesExistenceStatement.{u, v} :=
  rationalCuspidalSeriesExistence_of_dynamicParabolicQuotientCompact.{u, v}
    BruhatTits.dynamicParabolicQuotientCompact.{u}

end Langlands.Aubert.General.RationalPointFamily
