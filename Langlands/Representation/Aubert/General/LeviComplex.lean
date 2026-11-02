import Langlands.Representation.Aubert.General.StandardComplex
import Langlands.Representation.Aubert.General.AlternatingOperator

/-! The actual standard-subset smooth complex inside a closed standard Levi. -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Aubert.General.LeviComplex

open CategoryTheory

universe uI uG uV

variable {ι : Type uI}
variable {G : Type uG} [Group G]

/-- Restrict a standard-subset subgroup family to the actual subgroup `L`. -/
abbrev family (L : Subgroup G) (F : Finset ι → Subgroup G) (J : Finset ι)
    (K : Finset J) : Subgroup L :=
  (F (leviIndex J K)).subgroupOf L

/-- Reading a finset of `J` in the ambient root set preserves inclusion. -/
theorem leviIndex_monotone (J : Finset ι) : Monotone (leviIndex J) :=
  fun _ _ hKL => Finset.map_subset_map.mpr hKL

/-- Increasing standard parabolics remain increasing inside a fixed Levi. -/
theorem family_monotone (L : Subgroup G) {F : Finset ι → Subgroup G}
    (hF : Monotone F) (J : Finset ι) : Monotone (family L F J) :=
  fun _ _ hKL => Subgroup.subgroupOf_mono L (hF (leviIndex_monotone J hKL))

/-- Decreasing standard radicals remain decreasing inside a fixed Levi. -/
theorem family_antitone (L : Subgroup G) {F : Finset ι → Subgroup G}
    (hF : Antitone F) (J : Finset ι) : Antitone (family L F J) :=
  fun _ _ hKL => Subgroup.subgroupOf_mono L (hF (leviIndex_monotone J hKL))

variable [LinearOrder ι] [Fintype ι]
variable [TopologicalSpace G] [LocallyCompactSpace G] [NonarchimedeanGroup G]
variable (P M U : Finset ι → Subgroup G)
variable (hclosed : ∀ K, IsClosed (U K : Set G))
variable (hP : Monotone P) (hU : Antitone U)
variable (J : Finset ι) (hM : IsClosed (M J : Set G))
variable (hJ : ∀ K : Finset J,
  IsSemidirectDecomposition (family (M J) P J K)
    (family (M J) M J K) (family (M J) U J K))
variable (hJδ : letI := hM.locallyCompactSpace
  ∀ K : Finset J, IsUnimodularModulus (family (M J) U J K)
    ((hclosed (leviIndex J K)).preimage continuous_subtype_val))

/-- The actual terminal cokernel functor inside `M J`, at support subset `K`.
The universe contains both the root index and the ambient group universe, so
this functor can be composed with ambient Jacquet and cokernel functors. -/
def sharpFunctor (K : Finset J) :
    SmoothRep.{0, uG, max uI uG uV} ℂ (M J) ⥤
      SmoothRep.{0, uG, max uI uG uV} ℂ (M J) :=
  letI := hM.locallyCompactSpace
  StandardComplex.sharpFunctor.{uI, uG, max uI uV}
    (family (M J) P J) (family (M J) M J) (family (M J) U J) hJ
    (fun L => (hclosed (leviIndex J L)).preimage continuous_subtype_val) hJδ
    (family_monotone (M J) hP J) (family_antitone (M J) hU J) K

/-- The Levi cokernel object is the value of its actual functor. -/
abbrev sharpObject (A : SmoothRep.{0, uG, max uI uG uV} ℂ (M J))
    (K : Finset J) :=
  (sharpFunctor P M U hclosed hP hU J hM hJ hJδ K).obj A

end Langlands.Aubert.General.LeviComplex
