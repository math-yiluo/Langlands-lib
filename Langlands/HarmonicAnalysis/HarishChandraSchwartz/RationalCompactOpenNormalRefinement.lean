import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInducedFixedOrbits
import Langlands.Representation.Smooth.FixedVectors.OrderProof
import Langlands.Representation.Plancherel.RationalTwistStabilizer
import Mathlib.Topology.Algebra.ClopenNhdofOne

/-! # Compact open normal refinements for VIII.1.3 -/

noncomputable section

universe u uX uV uA

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

section Topological

variable {X : Type uX} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]

/-- The exact compact-open normal refinement used in VIII.1.3: every compact
open `H` admits a compact open subgroup below both `H` and `K`, normal in `K`.
This is a conclusion, not part of the data of a chosen compact subgroup. -/
def CompactOpenNormalRefinementStatement (K : OpenSubgroup X) : Prop :=
  ∀ (H : Subgroup X), IsOpen (H : Set X) → IsCompact (H : Set X) →
    ∃ L : CompactOpenSubgroup X,
      L.toSubgroup ≤ H ∧ L.toSubgroup ≤ K.toSubgroup ∧
        (L.toSubgroup.subgroupOf K.toSubgroup).Normal

/-- Compactness of `K` supplies the normal refinement, using Mathlib's open
normal subgroup theorem inside the compact group `K`. -/
theorem compactOpenNormalRefinement (K : OpenSubgroup X)
    (hKc : IsCompact (K : Set X)) : CompactOpenNormalRefinementStatement K := by
  intro H hHo _
  let : CompactSpace K.toSubgroup := isCompact_iff_compactSpace.mp hKc
  let HK : OpenSubgroup K.toSubgroup :=
    { toSubgroup := H.comap K.toSubgroup.subtype
      isOpen' := hHo.preimage continuous_subtype_val }
  obtain ⟨N, hN⟩ := IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one
    HK.isClopen HK.one_mem
  let L : Subgroup X := N.toSubgroup.map K.toSubgroup.subtype
  have hLo : IsOpen (L : Set X) :=
    K.isOpen.isOpenMap_subtype_val _ N.toOpenSubgroup.isOpen
  have hLc : IsCompact (L : Set X) :=
    N.toOpenSubgroup.isClosed.isCompact.image continuous_subtype_val
  have hLK : L ≤ K.toSubgroup := Subgroup.map_subtype_le _
  have hLH : L ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact hN hx
  have hLN : L.subgroupOf K.toSubgroup = N.toSubgroup :=
    Subgroup.comap_map_eq_self_of_injective K.toSubgroup.subtype_injective N.toSubgroup
  refine ⟨⟨⟨L, hLo⟩, hLc⟩, hLH, hLK, ?_⟩
  rw [hLN]
  exact N.isNormal'

omit [IsTopologicalGroup X] in
/-- An antitone support-index family is finite at arbitrary compact open
levels if it is finite at compact open levels contained and normal in `K`. -/
theorem finite_of_compactOpenNormalRefinement {A : Type uA}
    (K : OpenSubgroup X) (hrefine : CompactOpenNormalRefinementStatement K)
    (s : Subgroup X → Set A) (hs : Antitone s)
    (hfin : ∀ L : CompactOpenSubgroup X, L.toSubgroup ≤ K.toSubgroup →
      (L.toSubgroup.subgroupOf K.toSubgroup).Normal → (s L.toSubgroup).Finite)
    (H : Subgroup X) (hHo : IsOpen (H : Set X)) (hHc : IsCompact (H : Set X)) :
    (s H).Finite := by
  obtain ⟨L, hLH, hLK, hLN⟩ := hrefine H hHo hHc
  exact (hfin L hLK hLN).subset (hs hLH)

end Topological

section FixedVectors

variable {X : Type uX} [Group X] {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Shrinking the subgroup preserves the existence of a nonzero fixed vector. -/
theorem fixedVectors_ne_bot_of_le (ρ : Representation ℂ X V)
    {L H : Subgroup X} (hLH : L ≤ H) (hH : fixedVectors ρ H ≠ ⊥) :
    fixedVectors ρ L ≠ ⊥ := by
  intro hL
  apply hH
  have h := fixedVectors_antitone ρ hLH
  rw [hL] at h
  exact le_antisymm h bot_le

end FixedVectors

/-- Actual rational-point specialization of the normal-refinement assertion.
The chosen `K` may be the source's special maximal compact; only its explicit
openness and compactness are needed for this topological step. -/
def RationalCompactOpenNormalRefinementStatement
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] : Prop :=
  letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  letI : NonarchimedeanGroup (rationalPoints G) := rationalPoints_nonarchimedeanGroup G
  ∀ K : OpenSubgroup (rationalPoints G), IsCompact (K : Set (rationalPoints G)) →
    CompactOpenNormalRefinementStatement K

/-- The canonical rational-point group satisfies the exact refinement target. -/
theorem rationalCompactOpenNormalRefinement
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] :
    RationalCompactOpenNormalRefinementStatement G := by
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : NonarchimedeanGroup (rationalPoints G) := rationalPoints_nonarchimedeanGroup G
  exact fun K hKc => compactOpenNormalRefinement K hKc

end Langlands.HarishChandraSchwartz
