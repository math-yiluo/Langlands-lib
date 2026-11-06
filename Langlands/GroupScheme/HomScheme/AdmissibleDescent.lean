import Langlands.GroupScheme.HomScheme.AdmissibleMatching

/-! # Recovery and uniqueness for descent of actual admissible families -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.TorusSubgroupModuli

variable {S : Scheme.{u}} {G : GroupScheme S} {T : Over S}

/-- Every admissible subgroup has membership local on arbitrary test covers. -/
theorem isZariskiLocal_of_isAdmissible {J : GroupScheme S}
    (F : AdmissibleSubgroup J) : SubgroupFunctor.IsZariskiLocal F.val :=
  (admissibleRepresentative F).represents.isZariskiLocal

variable (𝒰 : Scheme.OpenCover.{u} T.left)

/-- Ordinary base change is actual family restriction followed by the
direct-to-iterated ambient identification. -/
theorem baseChange_eq_comap_restrict
    (F : AdmissibleSubgroup ((baseChange T.hom).obj G)) (i : 𝒰.I₀) :
    F.val.baseChange (𝒰.f i) =
      (restrict (SubgroupFunctor.coverMap 𝒰 i) F).val.comap
        (Descent.pullbackComparison T.hom (𝒰.f i)
          (SubgroupFunctor.coverObj 𝒰 i : Over S).hom rfl G).hom := by
  let e := Descent.pullbackComparison T.hom (𝒰.f i)
    (SubgroupFunctor.coverObj 𝒰 i : Over S).hom rfl G
  rw [restrict_val_eq]
  change F.val.baseChange (𝒰.f i) =
    ((F.val.baseChange (𝒰.f i)).comap e.inv).comap e.hom
  rw [← SubgroupFunctor.comap_comp, e.hom_inv_id, SubgroupFunctor.comap_id]

/-- Equality of actual admissible families is detected on an open cover of
their parameter scheme. -/
theorem eq_of_restrict_cover
    (F H : AdmissibleSubgroup ((baseChange T.hom).obj G))
    (h : ∀ i, restrict (SubgroupFunctor.coverMap 𝒰 i) F =
      restrict (SubgroupFunctor.coverMap 𝒰 i) H) :
    F = H := by
  apply Subtype.ext
  apply (SubgroupFunctor.eq_iff_isRepresentedBy_baseChange_openCover 𝒰
    (admissibleRepresentative F).represents
    (admissibleRepresentative H).represents).mpr
  intro i
  rw [baseChange_eq_comap_restrict 𝒰 F i,
    baseChange_eq_comap_restrict 𝒰 H i, h i]

variable (F : ∀ i, AdmissibleSubgroup
  ((baseChange (SubgroupFunctor.coverObj 𝒰 i : Over S).hom).obj G))

/-- The actual all-test subgroup obtained from local admissible families. -/
def matchingSubgroup : SubgroupFunctor ((baseChange T.hom).obj G) :=
  SubgroupFunctor.descentSubgroup 𝒰 (fun i => (coverSubgroup 𝒰 F i).val)

/-- Under ordinary matching, the constructed subgroup has the prescribed
local base changes in the iterated ambient pullbacks. -/
theorem baseChange_matchingSubgroup (hF : IsMatchingAdmissible 𝒰 F)
    (i : 𝒰.I₀) :
    (matchingSubgroup 𝒰 F).baseChange (𝒰.f i) = (coverSubgroup 𝒰 F i).val :=
  SubgroupFunctor.baseChange_descentSubgroup 𝒰 _
    (isMatching_coverSubgroup 𝒰 F hF) i

/-- The constructed subgroup has Zariski-local membership on all tests. -/
theorem isZariskiLocal_matchingSubgroup :
    SubgroupFunctor.IsZariskiLocal (matchingSubgroup 𝒰 F) :=
  SubgroupFunctor.isZariskiLocal_descentSubgroup 𝒰 _
    (fun i => isZariskiLocal_of_isAdmissible (coverSubgroup 𝒰 F i))

/-- Once its admissibility has been proved, the descended subgroup restricts
to each original actual family. -/
theorem restrict_matchingSubgroup (hF : IsMatchingAdmissible 𝒰 F)
    (h : IsAdmissible (matchingSubgroup 𝒰 F)) (i : 𝒰.I₀) :
    restrict (SubgroupFunctor.coverMap 𝒰 i) ⟨matchingSubgroup 𝒰 F, h⟩ = F i := by
  apply Subtype.ext
  rw [restrict_val_eq]
  change ((matchingSubgroup 𝒰 F).baseChange (𝒰.f i)).comap
    (Descent.pullbackComparison T.hom (𝒰.f i)
      (SubgroupFunctor.coverObj 𝒰 i : Over S).hom rfl G).inv = _
  rw [baseChange_matchingSubgroup 𝒰 F hF i]
  change ((F i).val.comap
    (Descent.pullbackComparison T.hom (𝒰.f i)
      (SubgroupFunctor.coverObj 𝒰 i : Over S).hom rfl G).hom).comap
    (Descent.pullbackComparison T.hom (𝒰.f i)
      (SubgroupFunctor.coverObj 𝒰 i : Over S).hom rfl G).inv = _
  rw [← SubgroupFunctor.comap_comp]
  simp only [Iso.inv_hom_id, SubgroupFunctor.comap_id]

end Langlands.GroupScheme.TorusSubgroupModuli
