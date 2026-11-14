import Langlands.GroupScheme.RelativeLevi.BorelEtaleTransport
import Langlands.GroupScheme.SubgroupFunctor.EtaleLocality

/-! # Gluing matching local opposite Borel subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G B Z : GroupScheme S} [IsAffineHom G.X.hom]
    (i : B ⟶ G) (t : Z ⟶ G)

/-- Compatible closed local opposite Borels descend to a global opposite
Borel with the prescribed intersection on every test scheme. -/
theorem exists_oppositeBorel_of_etaleLocal_matching
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (C : ∀ a : 𝒰.I₀, GroupScheme (𝒰.X a))
    (j : ∀ a : 𝒰.I₀, C a ⟶ (GroupScheme.baseChange (𝒰.f a)).obj G)
    (hB : ∀ a, IsRelativeBorelSubgroup (j a))
    (hc : ∀ a, IsClosedSubgroup (j a))
    (hinter : ∀ a, SubgroupFunctor.range (j a) ⊓
        SubgroupFunctor.range ((GroupScheme.baseChange (𝒰.f a)).map i) =
      SubgroupFunctor.range ((GroupScheme.baseChange (𝒰.f a)).map t))
    (hm : SubgroupFunctor.IsMatchingEtale 𝒰 (fun a => SubgroupFunctor.range (j a)))
    (ht : IsClosedSubgroup t)
    (hti : SubgroupFunctor.range t ≤ SubgroupFunctor.range i) :
    ∃ (C₀ : GroupScheme S) (j₀ : C₀ ⟶ G),
      IsRelativeBorelSubgroup j₀ ∧ IsClosedSubgroup j₀ ∧
        SubgroupFunctor.range j₀ ⊓ SubgroupFunctor.range i = SubgroupFunctor.range t := by
  let F := SubgroupFunctor.etaleDescentSubgroup 𝒰
    (fun a => SubgroupFunctor.range (j a))
  have hF : F.IsClosedRepresentable :=
    SubgroupFunctor.isClosedRepresentable_etaleDescentSubgroup 𝒰 _ hm
      (fun a => ⟨C a, j a, ⟨(hB a).isRelativeParabolicSubgroup.mono, rfl⟩, hc a⟩)
  obtain ⟨C₀, j₀, hjr, hjc⟩ := hF
  have hbc (a : 𝒰.I₀) :
      (SubgroupFunctor.range j₀).baseChange (𝒰.f a) = SubgroupFunctor.range (j a) := by
    rw [hjr.2]
    exact SubgroupFunctor.baseChange_etaleDescentSubgroup 𝒰 _ hm a
  have hjB : IsRelativeBorelSubgroup j₀ := by
    apply IsRelativeBorelSubgroup.of_etale_cover 𝒰 hjc
    intro a
    have hr : (SubgroupFunctor.range (j a)).IsRepresentedBy
        ((GroupScheme.baseChange (𝒰.f a)).map j₀) := by
      refine ⟨(hjr.baseChange (𝒰.f a)).1, ?_⟩
      rw [SubgroupFunctor.range_baseChangeHom, hbc]
    have hl : (SubgroupFunctor.range (j a)).IsRepresentedBy (j a) :=
      ⟨(hB a).isRelativeParabolicSubgroup.mono, rfl⟩
    rw [← hr.isoOfIsRepresentedBy_hom_comp hl]
    exact (hB a).iso_comp (hr.isoOfIsRepresentedBy hl)
  have : Mono j₀.hom.hom := hjr.1
  have : IsClosedImmersion t.hom.hom.left := ht
  have : Mono t.hom.hom := Over.mono_of_mono_left _
  refine ⟨C₀, j₀, hjB, hjc, le_antisymm ?_ ?_⟩
  · apply (SubgroupFunctor.le_range_iff_baseChange_etaleCover 𝒰 t).mpr
    intro a
    rw [SubgroupFunctor.inf_baseChange, hbc,
      ← SubgroupFunctor.range_baseChangeHom,
      ← SubgroupFunctor.range_baseChangeHom, hinter]
  · have htj : SubgroupFunctor.range t ≤ SubgroupFunctor.range j₀ := by
      apply (SubgroupFunctor.le_range_iff_baseChange_etaleCover 𝒰 j₀).mpr
      intro a
      rw [hbc, ← SubgroupFunctor.range_baseChangeHom, ← hinter a]
      exact fun _ _ hx => hx.1
    exact fun U x hx => ⟨htj U hx, hti U hx⟩

end Langlands.GroupScheme
