import Langlands.Representation.CuspidalSupport.RationalCuspidalInducedEmbeddingStatement
import Langlands.Representation.Aubert.General.FirstAdjointness
import Langlands.Representation.Jacquet.LocalizationExactnessProof

/-! # Finite actual induced maps and their kernel argument

This internal assembly constructs the finite sum of actual adjoint orbit maps.
Cuspidal projections remain explicit intermediate inputs.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory

namespace Langlands.Aubert.General

universe uI uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {κ : Type uI} [Fintype κ]
  (P M U : Finset κ → Subgroup G)
  (h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I))
  (hU : ∀ I, IsClosed (U I : Set G))
  (hδ : ∀ I, IsUnimodularModulus (U I) (hU I))
  (E : SmoothRep.{0, uG, uV} ℂ G)
  (τ : ∀ I : Finset κ, SmoothRep.{0, uG, max uI uG uV} ℂ (M I))
  (q : ∀ I, ((jacquetFunctor (h I) (hU I)).obj E).representation.IntertwiningMap
    (τ I).representation)

/-- The finite sum of the actual normalized first-adjointness orbit maps. -/
def finiteInducedJacquetMap :
    letI := Classical.decEq (Finset κ)
    E.representation.IntertwiningMap
      (SmoothRep.directSum.{uG, uI, max uG uV} (fun I =>
        (normalizedInductionFunctor (h I) (hU I)).obj (τ I))).representation := by
  classical
  exact ∑ I : Finset κ,
    (SmoothRep.hom (SmoothRep.directSumι.{uG, uI, max uG uV} (fun J =>
      (normalizedInductionFunctor (h J) (hU J)).obj (τ J)) I)).comp
        (FirstAdjointness.backward (h I) (hU I) (hδ I) E (τ I) (q I))

/-- Every component is precisely the corresponding adjoint orbit map. -/
@[simp] theorem finiteInducedJacquetMap_component (I : Finset κ) (v : E) :
    letI := Classical.decEq (Finset κ)
    SmoothRep.hom (SmoothRep.directSumπ.{uG, uI, max uG uV} (fun J =>
      (normalizedInductionFunctor (h J) (hU J)).obj (τ J)) I)
        (finiteInducedJacquetMap P M U h hU hδ E τ q v) =
      FirstAdjointness.backward (h I) (hU I) (hδ I) E (τ I) (q I) v := by
  classical
  unfold finiteInducedJacquetMap
  erw [Representation.IntertwiningMap.sum_apply, map_sum]
  change (∑ J : Finset κ,
    DirectSum.component ℂ (Finset κ)
      (fun J => (normalizedInductionFunctor (h J) (hU J)).obj (τ J)) I
      (DirectSum.lof ℂ (Finset κ)
        (fun J => (normalizedInductionFunctor (h J) (hU J)).obj (τ J)) J
          (FirstAdjointness.backward (h J) (hU J) (hδ J) E (τ J) (q J) v))) = _
  simp [DirectSum.component.of]

variable (hM : ∀ I, IsClosed (M I : Set G))
  (hL : ∀ (I : Finset κ) (J : Finset I),
    IsSemidirectDecomposition ((P (leviIndex I J)).subgroupOf (M I))
      ((M (leviIndex I J)).subgroupOf (M I)) ((U (leviIndex I J)).subgroupOf (M I)))

/-- The only objectwise cuspidal-projection input needed by the kernel argument:
a map to a cuspidal object whose postcomposition kills no nonzero map from a
cuspidal object. This is an intermediate target, not an additional premise of
the rational embedding statement. -/
def CuspidalJacquetProjectionTarget : Prop :=
  ∀ A : SmoothRep.{0, uG, uV} ℂ G,
    ∃ σ : ∀ I : Finset κ, SmoothRep.{0, uG, max uI uG uV} ℂ (M I),
      (∀ I, IsLeviCuspidal P M U hU I (hM I) (hL I) (σ I)) ∧
      ∃ p : ∀ I, ((jacquetFunctor (h I) (hU I)).obj A).representation.IntertwiningMap
          (σ I).representation,
        ∀ I (B : SmoothRep.{0, uG, uV} ℂ (M I)),
          IsLeviCuspidal P M U hU I (hM I) (hL I) B →
          ∀ j : B.representation.IntertwiningMap
            ((jacquetFunctor (h I) (hU I)).obj A).representation,
            (p I).comp j = 0 → j = 0

include hδ in
/-- Minimal nonzero Jacquet detection, finite orbit-map assembly and the
objectwise projection input imply the actual finite induced-cuspidal embedding.
No faithfulness of an I/R unit or exactness of an induction functor is assumed. -/
theorem finiteCuspidalInducedEmbedding_of_projections
    (hlim : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups (U I))
    (hdetect : ∀ B : SmoothRep.{0, uG, uV} ℂ G, Nontrivial B →
      ∃ I, Nontrivial ((jacquetFunctor (h I) (hU I)).obj B) ∧
        IsLeviCuspidal P M U hU I (hM I) (hL I)
          ((jacquetFunctor (h I) (hU I)).obj B))
    (hproj : CuspidalJacquetProjectionTarget.{uI, uG, uV} P M U h hU hM hL) :
    FiniteCuspidalInducedEmbeddingTarget.{uI, uG, uV} P M U h hU hM hL := by
  classical
  intro A
  obtain ⟨σ, hσ, p, hp⟩ := hproj A
  let f := finiteInducedJacquetMap P M U h hU hδ A σ p
  refine ⟨σ, hσ, f, ?_⟩
  suffices hz : ∀ v : A, f v = 0 → v = 0 from
    fun x y hxy => sub_eq_zero.mp (hz (x - y) (by rw [map_sub, hxy, sub_self]))
  let B := SmoothRep.subrepresentation A f.ker
  let j : B ⟶ A := SmoothRep.subtype A f.ker
  have hB : Subsingleton B := by
    by_contra hB
    have hBn : Nontrivial B := not_subsingleton_iff_nontrivial.mp hB
    obtain ⟨I, hI, hc⟩ := hdetect B hBn
    let rj := SmoothRep.hom ((jacquetFunctor (h I) (hU I)).map j)
    have hrj : Function.Injective rj :=
      Jacquet.Localization.map_injective_of_smooth (U I) (hlim I) 1
        (IsLocallyConstant.const _) (M I) (h I).levi_le_normalizer
        (Jacquet.Localization.isInvariant_one _ _ _) (SmoothRep.hom j)
        (SmoothRep.subtype_injective A f.ker) A.isSmooth
    have hzero : (p I).comp rj = 0 := by
      apply Representation.IntertwiningMap.ext
      apply Jacquet.Localization.hom_ext
      ext v
      have hf : f (SmoothRep.hom j v) = 0 := v.property
      have he := congrArg
        (fun w => SmoothRep.hom (SmoothRep.directSumπ.{uG, uI, max uG uV} (fun J =>
          (normalizedInductionFunctor (h J) (hU J)).obj (σ J)) I) w) hf
      have hback : FirstAdjointness.backward (h I) (hU I) (hδ I) A (σ I) (p I)
          (SmoothRep.hom j v) = 0 :=
        (finiteInducedJacquetMap_component P M U h hU hδ A σ p I
          (SmoothRep.hom j v)).symm.trans (he.trans (map_zero _))
      have hev := congrArg (fun w =>
        Induction.eval (P I) (inducingRepresentation (h I) (hU I) (σ I)) w 1) hback
      change (p I) (Jacquet.Localization.mk A.representation (U I) 1
          (A.representation 1 (SmoothRep.hom j v))) = 0 at hev
      change (p I) (Jacquet.Localization.mk A.representation (U I) 1
          (SmoothRep.hom j v)) = 0
      simpa only [map_one, Module.End.one_apply] using hev
    have hrjzero := hp I _ hc rj hzero
    have := hI
    obtain ⟨x, hx⟩ := exists_ne (0 : (jacquetFunctor (h I) (hU I)).obj B)
    apply hx
    apply hrj
    rw [hrjzero]
    rfl
  intro v hv
  exact congrArg Subtype.val (hB.elim (⟨v, hv⟩ : B) 0)

end Langlands.Aubert.General
