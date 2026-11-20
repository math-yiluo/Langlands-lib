import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionTargets
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ProjectedLeviCompact
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalModulusFactorization

/-! # Literal Levi Iwasawa factors and Weyl lifts at a special compact -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.Aubert.General Langlands.BruhatTits.SpecialCompact
open Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

section Projection

universe uG

variable {G : Type uG} [Group G] {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (K : Subgroup G)

/-- The Levi projection of the compact intersection is literal when the
compact intersection factors into its Levi and radical intersections. -/
theorem projectedLeviCompact_eq_subgroupOf_of_factorization
    (hfactor : ((K ⊓ P : Subgroup G) : Set G) =
      ((K ⊓ M : Subgroup G) : Set G) * ((K ⊓ U : Subgroup G) : Set G)) :
    projectedLeviCompact h K = K.subgroupOf M := by
  apply le_antisymm ?_ (subgroupOf_le_projectedLeviCompact h K)
  rintro m ⟨p, hpK, hp⟩
  have hm : (p : G) ∈ ((K ⊓ P : Subgroup G) : Set G) := ⟨hpK, p.property⟩
  rw [hfactor] at hm
  obtain ⟨a, ha, u, hu, hau⟩ := Set.mem_mul.mp hm
  let m' : M := ⟨a, ha.2⟩
  let u' : U := ⟨u, hu.2⟩
  have he : (⟨m', h.levi_le m'.property⟩ : P) * ⟨u', h.unipotent_le u'.property⟩ = p :=
    Subtype.ext hau
  rw [← he, h.projection_mul] at hp
  exact hp ▸ ha.1

end Projection

universe u

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
  (K : Subgroup (rationalPoints G))

/-- The minimal parabolic and compact intersect each standard Levi in an
Iwasawa pair inside that actual Levi. -/
def StandardLeviIwasawaFactorsAt : Prop :=
  ∀ J ⊆ simpleRelativeRoots i ν,
    IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))
      (K.subgroupOf (standardLeviPoints i ν J))

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
include hG hi hν in
/-- Project the ambient Iwasawa factorization and use the parabolic
factorization of the compact to identify the literal lower factors. -/
theorem standardLeviIwasawaFactorsAt_of_factorization
    (hP : IsIwasawaPair (standardParabolicPoints i ν ∅) K)
    (hK : HasParabolicFactorization i ν K) : StandardLeviIwasawaFactorsAt (i := i) (ν := ν) K := by
  intro J hJ
  let d := isSemidirectDecomposition_standard hG hi hν hJ
  have hU : standardUnipotentPoints i ν J ≤ standardParabolicPoints i ν ∅ :=
    (standardUnipotentPoints_le_empty_of_subset hG hi hν hJ).trans
      (fun _ hu => standardUnipotent_le_standardParabolic i ν ∅ _ hu)
  have h := isIwasawaPair_projectedLeviCompact d K (standardParabolicPoints_empty_le hG hi hν hJ)
    hU hP
  rw [projectedLeviCompact_eq_subgroupOf_of_factorization d K (hK J hJ)] at h
  exact h

namespace WeakExpansion

set_option maxHeartbeats 1000000 in
omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
include hG hi hν in
/-- Choose representatives in the given compact. Admissibility on one lift
implies admissibility on the chosen lift of the same Weyl element. -/
theorem exists_representatives_liftsInCompact
    (I I' : Finset (RationalPointFamily.SimpleRoot i ν))
    {L : OpenSubgroup (rationalPoints G)}
    (hL : HasWeylRepresentatives i (L : Subgroup (rationalPoints G))) :
    ∃ R : Representatives i ν (RationalPointFamily.rootSet i ν I)
      (RationalPointFamily.rootSet i ν I'), LiftsInCompact I I' (K := L) R := by
  classical
  let J := RationalPointFamily.rootSet i ν I
  let J' := RationalPointFamily.rootSet i ν I'
  let n (s : WeylIndex i ν J J') := (hL s.out.val).choose
  have hn (s : WeylIndex i ν J J') :
      (QuotientGroup.mk (n s) : relativeWeylGroup i) = s.out.val := (hL s.out.val).choose_spec.2
  refine ⟨⟨fun s => s.out, fun s => Quotient.out_eq s, n, hn, fun s => ?_⟩,
    fun s => (hL s.out.val).choose_spec.1⟩
  apply (mem_admissibleWeylElements_iff i ν J J' hG hi hν
    (RationalPointFamily.rootSet_subset i ν I) (n s)).mp
  rw [hn s]
  exact s.out.property

set_option maxHeartbeats 1200000 in
include hG hν in
/-- The compact appearing in the weighted weak expansion has all literal
Levi Iwasawa factors and permits all Weyl lifts there. -/
theorem standardLeviIwasawaFactorsAt_and_weylRepresentatives_of_special
    {L : OpenSubgroup (rationalPoints G)} (hL : IsSpecialVertexCompact ν hi L)
    (hP : IsIwasawaPair (standardParabolicPoints i ν ∅) (L : Subgroup (rationalPoints G))) :
    StandardLeviIwasawaFactorsAt (i := i) (ν := ν) (L : Subgroup (rationalPoints G)) ∧
      HasWeylRepresentatives i (L : Subgroup (rationalPoints G)) := by
  let := hi.isSplitSubtorus.mono
  obtain ⟨C, D, _, _, x, _, hc, he⟩ := hL
  have hh : SpecialCompactProperties F i ν (L : Subgroup (rationalPoints G)) := he ▸ hc
  exact ⟨standardLeviIwasawaFactorsAt_of_factorization hG hi hν
    (L : Subgroup (rationalPoints G)) hP hh.2.2.2, hh.2.2.1⟩

end WeakExpansion

end Langlands.HarishChandraSchwartz
