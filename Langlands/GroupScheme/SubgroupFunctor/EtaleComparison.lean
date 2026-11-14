import Langlands.GroupScheme.RelativeLevi.UnipotentRadicalRigidity
import Langlands.GroupScheme.Torus.IsomorphismLocusEtale

/-! # Comparing represented subgroups on an etale cover -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

variable {S : Scheme.{u}}

/-- An actual group-scheme homomorphism is invertible if it becomes invertible
on every member of an etale cover of the base. -/
theorem isIso_of_baseChange_etaleCover
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    {H G : GroupScheme S} (i : H ⟶ G)
    (hi : ∀ j, IsIso ((GroupScheme.baseChange (𝒰.f j)).map i)) : IsIso i := by
  let : ∀ j, Etale (𝒰.f j) := 𝒰.map_prop
  let O : 𝒰.I₀ → S.Opens := fun j => TorusIsomorphismLocus.etaleImage (𝒰.f j)
  let 𝒱 := S.openCoverOfIsOpenCover O (by
    apply TopologicalSpace.IsOpenCover.mk
    apply top_le_iff.mp
    intro s _
    rw [TopologicalSpace.Opens.mem_iSup]
    obtain ⟨j, t, ht⟩ := 𝒰.exists_eq s
    exact ⟨j, t, ht⟩)
  apply TorusIsomorphismLocus.isIso_of_openCover i 𝒱
  intro j
  have := hi j
  exact TorusIsomorphismLocus.isIso_etaleImage i (𝒰.f j)

namespace SubgroupFunctor

variable {P N U : GroupScheme S}

/-- Equality of monomorphically represented subgroup functors is detected by
the actual inclusions after base change to an arbitrary etale cover. -/
theorem range_eq_of_baseChange_etaleCover
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (n : N ⟶ P) (r : U ⟶ P) [Mono n.hom.hom] [Mono r.hom.hom]
    (h : ∀ j, range ((GroupScheme.baseChange (𝒰.f j)).map n) =
      range ((GroupScheme.baseChange (𝒰.f j)).map r)) : range n = range r := by
  have hfst (j : 𝒰.I₀) :
      IsIso ((GroupScheme.baseChange (𝒰.f j)).map (subgroupIntersectionFst n r)) := by
    let b := 𝒰.f j
    let : Mono ((GroupScheme.baseChange b).map r).hom.hom := by
      change Mono ((Over.pullback b).map r.hom.hom)
      infer_instance
    let : IsIso (pullback.fst ((GroupScheme.baseChange b).map n) ((GroupScheme.baseChange b).map r)) :=
      RelativeLevi.isIso_subgroupIntersectionFst_of_range_le _ _ (h j).le
    change IsIso ((GroupScheme.baseChange b).map (pullback.fst n r))
    rw [← PreservesPullback.iso_hom_fst]
    infer_instance
  have hsnd (j : 𝒰.I₀) :
      IsIso ((GroupScheme.baseChange (𝒰.f j)).map (subgroupIntersectionSnd n r)) := by
    let b := 𝒰.f j
    let : Mono ((GroupScheme.baseChange b).map n).hom.hom := by
      change Mono ((Over.pullback b).map n.hom.hom)
      infer_instance
    let : IsIso (pullback.snd ((GroupScheme.baseChange b).map n) ((GroupScheme.baseChange b).map r)) :=
      RelativeLevi.isIso_subgroupIntersectionSnd_of_range_le _ _ (h j).ge
    change IsIso ((GroupScheme.baseChange b).map (pullback.snd n r))
    rw [← PreservesPullback.iso_hom_snd]
    infer_instance
  let : IsIso (subgroupIntersectionFst n r) :=
    isIso_of_baseChange_etaleCover 𝒰 _ hfst
  let : IsIso (subgroupIntersectionSnd n r) :=
    isIso_of_baseChange_etaleCover 𝒰 _ hsnd
  have h₁ : range (subgroupIntersectionHom n r) = range n :=
    range_iso_comp (asIso (subgroupIntersectionFst n r)) n
  have h₂ : range (subgroupIntersectionHom n r) = range r := by
    rw [subgroupIntersectionHom, subgroupIntersection_condition]
    exact range_iso_comp (asIso (subgroupIntersectionSnd n r)) r
  exact h₁.symm.trans h₂

/-- Compatible comparison of representatives whose inclusions have equal
images after an etale cover of the base. -/
def isoOfEtaleCoverRangeEq
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (n : N ⟶ P) (r : U ⟶ P) [Mono n.hom.hom] [Mono r.hom.hom]
    (h : ∀ j, range ((GroupScheme.baseChange (𝒰.f j)).map n) =
      range ((GroupScheme.baseChange (𝒰.f j)).map r)) : N ≅ U :=
  (show (range r).IsRepresentedBy n from
    ⟨inferInstance, range_eq_of_baseChange_etaleCover 𝒰 n r h⟩).isoOfIsRepresentedBy
      ⟨inferInstance, rfl⟩

/-- The etale-cover comparison respects the inclusions into the ambient group. -/
theorem isoOfEtaleCoverRangeEq_hom_comp
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (n : N ⟶ P) (r : U ⟶ P) [Mono n.hom.hom] [Mono r.hom.hom]
    (h : ∀ j, range ((GroupScheme.baseChange (𝒰.f j)).map n) =
      range ((GroupScheme.baseChange (𝒰.f j)).map r)) :
    (isoOfEtaleCoverRangeEq 𝒰 n r h).hom ≫ r = n :=
  IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

end SubgroupFunctor

end Langlands.GroupScheme
