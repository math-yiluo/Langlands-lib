import Langlands.Representation.Aubert.General.RationalCuspidalEmbeddingProof
import Langlands.Representation.Aubert.General.RestrictedLeviTopology
import Langlands.Representation.Jacquet.LocalizationTransport

/-! # Minimal cuspidal Jacquet modules inside an actual standard Levi -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

universe uG uV uI u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Aubert.General

namespace IsSemidirectDecomposition

/-- The radical intersects its actual Levi trivially. -/
theorem unipotent_subgroupOf_levi_eq_bot
    {H : Type uG} [Group H] {P M U : Subgroup H}
    (h : IsSemidirectDecomposition P M U) :
    U.subgroupOf M = ⊥ := by
  apply le_antisymm _ bot_le
  intro m hm
  exact Subgroup.mem_bot.mpr
    ((h.projection_levi m).symm.trans (h.projection_unipotent ⟨m, hm⟩))

end IsSemidirectDecomposition

namespace CuspidalEmbedding

/-- A descendant of the ambient image of `I : Finset K` can be read inside
`K` without changing its ambient root labels. -/
def descendantEmbedding {Index : Type uI} (K : Finset Index) (I : Finset K) :
    (leviIndex K I) ↪ K where
  toFun a := ⟨a.val, leviIndex_subset K I a.property⟩
  inj' _ _ := Subtype.ext ∘ congrArg Subtype.val

theorem leviIndex_descendantEmbedding {Index : Type uI}
    (K : Finset Index) (I : Finset K) (J : Finset (leviIndex K I)) :
    leviIndex K (J.map (descendantEmbedding K I)) =
      leviIndex (leviIndex K I) J := by
  rw [leviIndex, Finset.map_map]
  rfl

theorem leviIndex_univ {Index : Type uI} (K : Finset Index) :
    leviIndex K Finset.univ = K := by
  classical
  ext a
  simp [leviIndex]

/-- The same actual coinvariants before and after flattening the copy of a
subgroup inside a larger subgroup. The linear map keeps every vector class. -/
def subgroupOfPullbackCoinvariantsEquiv
    {H : Type uG} [Group H] [TopologicalSpace H]
    {L M : Subgroup H} (hLM : L ≤ M) (V : Subgroup H)
    (A : SmoothRep.{0, uG, uV} ℂ (L.subgroupOf M)) :
    Jacquet.Localization.Coinvariants
        ((SmoothRep.pullbackFunctor (subgroupOfContinuousEquiv hLM).symm).obj A).representation
        (V.subgroupOf L) 1 ≃ₗ[ℂ]
      Jacquet.Localization.Coinvariants A.representation
        ((V.subgroupOf M).subgroupOf (L.subgroupOf M)) 1 :=
  Jacquet.Localization.transportEquiv _ _ _ _ 1 1
    { toFun := fun x => ⟨(subgroupOfContinuousEquiv hLM).symm x, x.property⟩
      invFun := fun x => ⟨subgroupOfContinuousEquiv hLM x, x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
    (LinearEquiv.refl ℂ A) (fun _ _ => rfl) (fun _ => rfl)

/-- A nonzero smooth module finitely generated over the group algebra has an
actual irreducible smooth quotient in the same carrier universe. -/
theorem exists_irreducible_quotient_of_finite
    {H : Type uG} [Group H] [TopologicalSpace H]
    (A : SmoothRep.{0, uG, uV} ℂ H) [Nontrivial A]
    (hfg : Module.Finite (MonoidAlgebra ℂ H) A.representation.asModule) :
    ∃ B : SmoothRep.{0, uG, uV} ℂ H,
      B.IsIrreducible ∧ ∃ q : A ⟶ B, Function.Surjective (SmoothRep.hom q) := by
  let := hfg
  have hco : IsCoatomic (Subrepresentation A.representation) :=
    (Subrepresentation.subrepresentationSubmoduleOrderIso
      (ρ := A.representation)).isCoatomic_iff.mpr inferInstance
  obtain ⟨T₀, hT₀⟩ : ∃ T₀ : Subrepresentation A.representation, IsCoatom T₀ := by
    rcases hco.eq_top_or_exists_le_coatom ⊥ with hbot | ⟨T₀, hT₀, -⟩
    · exfalso
      obtain ⟨y, hy⟩ := exists_ne (0 : A)
      apply hy
      have hmem : y ∈ (⊥ : Subrepresentation A.representation) := by
        rw [hbot]
        exact Submodule.mem_top
      exact hmem
    · exact ⟨T₀, hT₀⟩
  exact ⟨SmoothRep.quotient A T₀,
    SmoothRep.RenardIrreducibleExistence.quotient_isIrreducible_of_isCoatom A T₀ hT₀,
    SmoothRep.mkQ A T₀, SmoothRep.mkQ_surjective A T₀⟩

/-- An intertwiner into the pullback of its target by a group equivalence
and its inverse; its linear map is unchanged. -/
def roundTripPullbackMap
    {H N : Type uG} [Group H] [TopologicalSpace H] [Group N] [TopologicalSpace N]
    (e : H ≃ₜ* N) {A B : SmoothRep.{0, uG, uV} ℂ H} (q : A ⟶ B) :
    A ⟶ (SmoothRep.pullbackFunctor e).obj
      ((SmoothRep.pullbackFunctor e.symm).obj B) := SmoothRep.ofHom
  { toLinearMap := (SmoothRep.hom q).toLinearMap
    isIntertwining' m := by
      change (SmoothRep.hom q).toLinearMap.comp (A.representation m) =
        (B.representation (e.symm (e m))).comp (SmoothRep.hom q).toLinearMap
      rw [e.symm_apply_apply]
      exact (SmoothRep.hom q).isIntertwining' m }

@[simp]
theorem roundTripPullbackMap_apply
    {H N : Type uG} [Group H] [TopologicalSpace H] [Group N] [TopologicalSpace N]
    (e : H ≃ₜ* N) {A B : SmoothRep.{0, uG, uV} ℂ H} (q : A ⟶ B) (x : A) :
    SmoothRep.hom (roundTripPullbackMap e q) x = SmoothRep.hom q x := rfl

/-- First adjointness turns a surjective Jacquet map to nonzero data into
an embedding when the source is irreducible. -/
theorem embedding_of_surjective_jacquet_map
    {H : Type uG} [Group H] [TopologicalSpace H] [LocallyCompactSpace H]
    [NonarchimedeanGroup H] {P M U : Subgroup H}
    (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set H))
    (hδ : IsUnimodularModulus U hU)
    (A : SmoothRep.{0, uG, max uG uV} ℂ H) (hA : A.IsIrreducible)
    (B : SmoothRep.{0, uG, max uG uV} ℂ M) [Nontrivial B]
    (q : (jacquetFunctor h hU).obj A ⟶ B) (hq : Function.Surjective (SmoothRep.hom q)) :
    SmoothRep.IsSubrepresentation A ((normalizedInductionFunctor h hU).obj B) := by
  have : A.representation.IsIrreducible := hA
  let F := (General.FirstAdjointness.equiv h hU hδ A B).symm (SmoothRep.hom q)
  have hF : F ≠ 0 := by
    intro hF0
    obtain ⟨s, hs⟩ := exists_ne (0 : B)
    obtain ⟨y, hy⟩ := hq s
    apply hs
    have hq0 : SmoothRep.hom q = 0 := by
      have := congrArg (General.FirstAdjointness.equiv h hU hδ A B) hF0
      simpa only [F, LinearEquiv.apply_symm_apply, map_zero] using this
    rw [← hy, hq0]
    rfl
  exact ⟨SmoothRep.ofHom F,
    (Representation.IsIrreducible.injective_or_eq_zero F).resolve_right hF⟩

end CuspidalEmbedding

namespace RationalPointFamily

open GroupScheme SmoothRep
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hInter : StandardLeviIntersectionStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)

include hInter hG hi hν in
/-- The fine-radical product survives intersection with any larger standard
Levi: the second factor also lies there because the other two do. -/
theorem unipotent_product_in_levi_of_subsets
    (L I K : Finset (SimpleRoot i ν)) (hLI : L ⊆ I) (hIK : I ⊆ K) :
    ∀ x ∈ (unipotent i ν L).subgroupOf (levi i ν K),
      ∃ w ∈ (levi i ν I).subgroupOf (levi i ν K) ⊓
          (unipotent i ν L).subgroupOf (levi i ν K),
        ∃ n ∈ (unipotent i ν I).subgroupOf (levi i ν K), w * n = x := by
  intro x hx
  change (x : RationalPoint k G.X) ∈
    (unipotent i ν L : Set (RationalPoint k G.X)) at hx
  rw [unipotent_product_of_subset i ν hInter hG hi hν L I hLI] at hx
  obtain ⟨w, hw, n, hn, heq⟩ := Set.mem_mul.mp hx
  have hwK := levi_le_of_subset i ν hInter hG hi hν I K hIK hw.1
  have hnK : n ∈ levi i ν K := by
    have hn' : n = w⁻¹ * (x : RationalPoint k G.X) := by
      rw [← heq, inv_mul_cancel_left]
    rw [hn']
    exact (levi i ν K).mul_mem ((levi i ν K).inv_mem hwK) x.property
  exact ⟨⟨w, hwK⟩, ⟨hw.1, hw.2⟩, ⟨n, hnK⟩, hn, Subtype.ext heq⟩

section Topological

variable [TopologicalSpace k] [ValuativeRel k] [IsNonarchimedeanLocalField k]

local instance leviEmbeddingPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (hStandard : StandardCocharacterStatement.{u})
  (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
  (hM : ∀ I, IsClosed (levi i ν I : Set (RationalPoint k G.X)))

include hStandard in
/-- An irreducible smooth representation of an actual standard Levi has a
nonzero cuspidal standard Jacquet module. No endpoint or quotient-compactness
premise is needed for this minimal-index assertion. -/
theorem exists_nonzero_cuspidal_leviJacquet
    (K : Finset (SimpleRoot i ν))
    (τ : SmoothRep.{0, u, v} ℂ (levi i ν K)) (hτ : τ.IsIrreducible) :
    ∃ I : Finset K,
      Nontrivial ((leviNormalizedJacquetFunctor (hM K)
        (levi_le_of_subset i ν hInter hG hi hν _ K (leviIndex_subset K I))
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν K I)
        (hU (leviIndex K I))).obj τ) ∧
      IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) hU
        (leviIndex K I) (hM (leviIndex K I))
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν (leviIndex K I))
        ((leviNormalizedJacquetFunctor (hM K)
          (levi_le_of_subset i ν hInter hG hi hν _ K (leviIndex_subset K I))
          (isSemidirectDecomposition_in_levi i ν hInter hG hi hν K I)
          (hU (leviIndex K I))).obj τ) := by
  classical
  let := (hM K).locallyCompactSpace
  let h := isSemidirectDecomposition_in_levi i ν hInter hG hi hν K
  let hUK := fun I : Finset K => (hU (leviIndex K I)).preimage
    (continuous_subtype_val : Continuous (fun x : levi i ν K => (x : RationalPoint k G.X)))
  have : τ.representation.IsIrreducible := hτ
  obtain ⟨v₀, hv₀⟩ : ∃ x : τ, x ≠ 0 := by
    have : Nontrivial τ.representation.asModule :=
      IsSimpleModule.nontrivial (MonoidAlgebra ℂ (levi i ν K)) _
    exact exists_ne (0 : τ.representation.asModule)
  let S : Set (Finset K) :=
    {I | Nontrivial ((jacquetFunctor.{u, v} (h I) (hUK I)).obj τ)}
  have hbot : (unipotent i ν (leviIndex K Finset.univ)).subgroupOf
      (levi i ν K) = ⊥ := by
    rw [CuspidalEmbedding.leviIndex_univ]
    exact (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν K).unipotent_subgroupOf_levi_eq_bot
  have huniv : Finset.univ ∈ S := by
    refine ⟨⟨Jacquet.Localization.mk τ.representation
      ((unipotent i ν (leviIndex K Finset.univ)).subgroupOf (levi i ν K)) 1 v₀,
      0, ?_⟩⟩
    intro hzero
    apply hv₀
    have hmem := (Jacquet.Localization.mk_eq_zero _ _ _ v₀).1 hzero
    have hle : Jacquet.Localization.relations τ.representation
        ((unipotent i ν (leviIndex K Finset.univ)).subgroupOf (levi i ν K)) 1 ≤ ⊥ := by
      apply Submodule.span_le.2
      rintro _ ⟨⟨x, b⟩, rfl⟩
      have hx : (x : levi i ν K) = 1 := Subgroup.mem_bot.mp (hbot ▸ x.property)
      simp only [hx, map_one, Module.End.one_apply, MonoidHom.one_apply,
        Units.val_one, one_smul, sub_self]
      exact Submodule.zero_mem _
    exact (Submodule.mem_bot ℂ).1 (hle hmem)
  obtain ⟨I, hI, hImin⟩ :=
    (measure (Finset.card : Finset K → ℕ)).wf.has_min S ⟨_, huniv⟩
  let A := leviIndex K I
  let rI := (jacquetFunctor.{u, v} (h I) (hUK I)).obj τ
  have hAK : levi i ν A ≤ levi i ν K :=
    levi_le_of_subset i ν hInter hG hi hν A K (leviIndex_subset K I)
  let flat := (SmoothRep.pullbackFunctor (subgroupOfContinuousEquiv hAK).symm).obj rI
  refine ⟨I, hI, ?_⟩
  change IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) hU A
    (hM A) (isSemidirectDecomposition_in_levi i ν hInter hG hi hν A) flat
  let := (hM A).locallyCompactSpace
  intro J
  let J' : Finset K := J.val.map (CuspidalEmbedding.descendantEmbedding K I)
  have hlabels : leviIndex K J' = leviIndex A J.val :=
    CuspidalEmbedding.leviIndex_descendantEmbedding K I J.val
  have hsmall : Subsingleton ((jacquetFunctor.{u, v} (h J') (hUK J')).obj τ) := by
    rw [← not_nontrivial_iff_subsingleton]
    intro hns
    apply hImin J' hns
    change J'.card < I.card
    rw [Finset.card_map]
    calc J.val.card < (Finset.univ : Finset A).card :=
          Finset.card_lt_card (Finset.ssubset_univ_iff.2 J.property)
      _ = I.card := by rw [Finset.card_univ, Fintype.card_coe, card_leviIndex]
  have hsmall' : Subsingleton (Jacquet.Localization.Coinvariants τ.representation
      ((unipotent i ν (leviIndex A J.val)).subgroupOf (levi i ν K)) 1) := by
    rw [← hlabels]
    exact hsmall
  have hsub := leviIndex_subset A J.val
  have hWN : (unipotent i ν (leviIndex A J.val)).subgroupOf (levi i ν K) ≤
      Subgroup.normalizer
        ((unipotent i ν A).subgroupOf (levi i ν K) : Set (levi i ν K)) :=
    (Subgroup.subgroupOf_mono (levi i ν K)
      (unipotent_le_parabolic_of_subset i ν hInter hG hi hν _ A hsub)).trans
      (h I).le_normalizer
  have hrels : ∀ y : rI, y ∈ Jacquet.Localization.relations rI.representation
      (((unipotent i ν (leviIndex A J.val)).subgroupOf (levi i ν K)).subgroupOf
        ((levi i ν A).subgroupOf (levi i ν K))) 1 := by
    apply CuspidalEmbedding.mem_relations_of_subsingleton (h I) (hUK I)
      ((unipotent i ν (leviIndex A J.val)).subgroupOf (levi i ν K))
    · exact unipotent_product_in_levi_of_subsets i ν hInter hG hi hν
        (leviIndex A J.val) A K hsub (leviIndex_subset K I)
    · intro w hwV
      apply (Jacquet.inverseHalfCharacter_eq_one _ _).2
      exact CuspidalEmbedding.closedNormalizerCharacter_eq_one_of_compactLimit
        _ _ (hUK I) hWN
        (isLimitOfCompactSubgroups_subgroupOf _ _ (hM K)
          (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
            i ν hStandard hG hi hν (leviIndex A J.val))) ⟨w, hwV⟩
    · exact hsmall'
  have hnested : Subsingleton (Jacquet.Localization.Coinvariants rI.representation
      (((unipotent i ν (leviIndex A J.val)).subgroupOf (levi i ν K)).subgroupOf
        ((levi i ν A).subgroupOf (levi i ν K))) 1) := by
    constructor
    intro a b
    obtain ⟨a, rfl⟩ := Jacquet.Localization.mk_surjective _ _ _ a
    obtain ⟨b, rfl⟩ := Jacquet.Localization.mk_surjective _ _ _ b
    exact (Jacquet.Localization.mk_eq_iff _ _ _ a b).2 (hrels _)
  have hflat : Subsingleton (Jacquet.Localization.Coinvariants flat.representation
      ((unipotent i ν (leviIndex A J.val)).subgroupOf (levi i ν A)) 1) :=
    (CuspidalEmbedding.subgroupOfPullbackCoinvariantsEquiv hAK
      (unipotent i ν (leviIndex A J.val)) rI).injective.subsingleton
  exact hflat



end Topological

end RationalPointFamily

end Langlands.Aubert.General
