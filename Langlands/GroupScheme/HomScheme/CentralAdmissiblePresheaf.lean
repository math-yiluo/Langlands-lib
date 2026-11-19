import Langlands.GroupScheme.CentralIsogeny.FpqcReflectionHelpers
import Langlands.GroupScheme.HomScheme.AdmissibleFpqcSheaf
import Langlands.GroupScheme.HomScheme.TorusSubgroupChartGluingProof
import Langlands.GroupScheme.HomScheme.TorusSubgroupValuativeSeparation
import Langlands.GroupScheme.Reductive.GlobalKernelCentrality
import Mathlib.CategoryTheory.Subfunctor.Basic

/-! # The small presheaf of actual central closed torus subgroups -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.TorusSubgroupModuli

open SubgroupFunctor Langlands.AlgebraicGeometry.UnramifiedFunctor

variable {S : Scheme.{u}} {G : GroupScheme S} {T M : Over S}

/-- The range of the evaluated family is central exactly when its raw
base-changed inclusion is central. -/
theorem central_evaluate_iff {H : GroupScheme M.left}
    (j : H ⟶ (baseChange M.hom).obj G) (a : T ⟶ M) :
    evaluate j a ≤ center ((baseChange T.hom).obj G) ↔
      IsCentral ((baseChange a.left).map j) := by
  rw [evaluate, ← isCentral_iff_range_le_center]
  let e := Descent.pullbackComparison M.hom a.left T.hom a.w G
  constructor
  · intro h
    have h' := h.comp_iso e.symm
    change IsCentral ((((baseChange a.left).map j) ≫ e.hom) ≫ e.inv) at h'
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h'
  · intro h
    exact h.comp_iso e

private theorem central_restrict_iff (a : T ⟶ M)
    (x : AdmissibleSubgroup ((baseChange M.hom).obj G)) :
    (restrict a x).val ≤ center ((baseChange T.hom).obj G) ↔
      IsCentral ((baseChange a.left).map (admissibleRepresentative x).hom) := by
  rw [restrict_eq_evaluate x _ (admissibleRepresentative x).represents.2]
  exact central_evaluate_iff _ _

/-- The subpresheaf of small actual admissible subgroups whose all-test
range is contained in the all-test centre. -/
def centralAdmissibleSubfunctor (G : GroupScheme S) :
    Subfunctor (smallAdmissiblePresheaf G) where
  obj T := {x | (smallAdmissibleEquiv G T.unop x).val ≤ center ((baseChange T.unop.hom).obj G)}
  map {M T} a := by
    intro x hx
    let r := admissibleRepresentative (smallAdmissibleEquiv G M.unop x)
    have hc : SubgroupFunctor.range r.hom ≤ center _ := r.represents.2.symm ▸ hx
    have hr := ((isCentral_iff_range_le_center r.hom).mpr hc).baseChange a.unop.left
    change (smallAdmissibleEquiv G T.unop ((smallAdmissiblePresheaf G).map a x)).val ≤ center _
    have h := smallAdmissibleEquiv_map a.unop x
    rw [Quiver.Hom.op_unop] at h
    exact h.symm ▸ (central_restrict_iff a.unop _).mpr hr

/-- The small presheaf of actual central closed torus subgroups. -/
abbrev smallCentralAdmissiblePresheaf (G : GroupScheme S) : (Over S)ᵒᵖ ⥤ Type u :=
  (centralAdmissibleSubfunctor G).toFunctor

/-- A section of the small admissible presheaf is central exactly when
its actual representative is central. -/
theorem mem_centralAdmissible_iff (x : (smallAdmissiblePresheaf G).obj (op T)) :
    x ∈ (centralAdmissibleSubfunctor G).obj (op T) ↔
      IsCentral (admissibleRepresentative (smallAdmissibleEquiv G T x)).hom := by
  let r := admissibleRepresentative (smallAdmissibleEquiv G T x)
  change (smallAdmissibleEquiv G T x).val ≤ center _ ↔ IsCentral r.hom
  rw [← r.represents.2, isCentral_iff_range_le_center]

/-- Centrality of the restriction is centrality of the base-changed
actual representative. -/
theorem mem_centralAdmissible_map_iff (a : T ⟶ M)
    (x : (smallAdmissiblePresheaf G).obj (op M)) :
    (smallAdmissiblePresheaf G).map a.op x ∈ (centralAdmissibleSubfunctor G).obj (op T) ↔
      IsCentral ((baseChange a.left).map
        (admissibleRepresentative (smallAdmissibleEquiv G M x)).hom) := by
  change (smallAdmissibleEquiv G T ((smallAdmissiblePresheaf G).map a.op x)).val ≤
    center _ ↔ _
  rw [smallAdmissibleEquiv_map]
  exact central_restrict_iff a _

private lemma isSheafFor_of_local_membership
    {C : Type v} [Category.{w} C] {P : Cᵒᵖ ⥤ Type u} (Q : Subfunctor P)
    {X : C} {R : Presieve X} (hP : Presieve.IsSheafFor P R)
    (hmem : ∀ x : P.obj (op X),
      (∀ ⦃T : C⦄ (a : T ⟶ X), R a → P.map a.op x ∈ Q.obj (op T)) →
      x ∈ Q.obj (op X)) :
    Presieve.IsSheafFor Q.toFunctor R := by
  intro x hx
  obtain ⟨s, hs, hu⟩ := hP (x.map Q.ι) (hx.map Q.ι)
  have hsQ : s ∈ Q.obj (op X) := hmem s fun _ a ha => by
    rw [hs a ha]
    exact (x a ha).property
  refine ⟨⟨s, hsQ⟩, fun _ a ha => Subtype.ext (hs a ha), fun s' hs' => Subtype.ext ?_⟩
  exact hu s'.val (hs'.map Q.ι)

/-- Centrality descends along Zariski covers of an admissible family. -/
theorem smallCentralAdmissiblePresheaf_zariskiSheaf (G : GroupScheme S) :
    ZariskiSheaf (smallCentralAdmissiblePresheaf G) := by
  intro T 𝒰
  refine isSheafFor_of_local_membership (centralAdmissibleSubfunctor G)
    (smallAdmissible_isSheafFor_cover G (hasEffectiveAdmissibleDescent G) T 𝒰) ?_
  intro x hx
  apply (mem_centralAdmissible_iff x).mpr
  apply GlobalKernelCentrality.isCentral_of_openCover 𝒰
  intro k
  let a := SubgroupFunctor.coverMap 𝒰 k
  exact (mem_centralAdmissible_map_iff a x).mp (hx a (.mk k))

/-- Centrality descends along single faithfully flat, quasi-compact maps of tests. -/
theorem smallCentralAdmissiblePresheaf_faithfullyFlatSheaf (G : GroupScheme S) :
    FaithfullyFlatSheaf (smallCentralAdmissiblePresheaf G) := by
  intro T M a hflat hsurj hqc
  refine isSheafFor_of_local_membership (centralAdmissibleSubfunctor G)
    (smallAdmissiblePresheaf_faithfullyFlatSheaf S G a hflat hsurj hqc) ?_
  intro x hx
  apply (mem_centralAdmissible_iff x).mpr
  apply IsCentral.of_baseChange a.left
  exact (mem_centralAdmissible_map_iff a x).mp (hx a (Presieve.singleton_self a))

/-- The central subpresheaf inherits valuative separation. -/
theorem smallCentralAdmissiblePresheaf_valuativeSeparation (G : GroupScheme S) :
    ValuativeSeparation (smallCentralAdmissiblePresheaf G) := by
  intro A _ _ _ f x y h
  apply Subtype.ext
  exact smallAdmissiblePresheaf_valuativeSeparation G A f (congrArg Subtype.val h)

end Langlands.GroupScheme.TorusSubgroupModuli
