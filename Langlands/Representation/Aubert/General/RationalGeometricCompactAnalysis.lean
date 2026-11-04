import Langlands.Representation.Aubert.General.RationalGeometricCompactHaar

/-! # Analytic choices for the actual rational compact comparison -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 400000

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme MeasureTheory MeasureTheory.Measure
open Langlands.AlgebraicGeometry.PointTopology
open Induction QuotientIntegration

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (I J : Finset (SimpleRoot i ν))
  (dI : IsSemidirectDecomposition (parabolic i ν I) (levi i ν I) (unipotent i ν I))
  (n : Group.RelativeWeyl.normalizer (torusPoints i))
  [TopologicalSpace (RationalPoint k G.X)]

local notation "A" => RationalPoint k G.X
local notation "Q" => parabolic i ν I
local notation "U" => unipotent i ν I
local notation "P" => geometricSplitIntermediate i ν I J dI n
local notation "H" => Subgroup.subgroupOf
  (geometricTargetIntersection Q (parabolic i ν J) (n : A)) Q
local notation "N" => geometricCompactKernel i ν I J dI n
local notation "D" => geometricCompactKernelIntersection i ν I J dI n

section Topology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  (hUI : IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))

include hUI in
/-- Local compactness of the restricted projection kernel follows from its
original-point homeomorphism with the closed ambient radical. -/
theorem geometricCompactKernel_locallyCompactSpace : LocallyCompactSpace N := by
  let : LocallyCompactSpace U := hUI.locallyCompactSpace
  exact (geometricCompactKernelEquiv i ν I J dI n).toHomeomorph.locallyCompactSpace_iff.mpr
    inferInstance

variable [IsTopologicalGroup (RationalPoint k G.X)]
  (hPI : IsClosed (parabolic i ν I : Set (RationalPoint k G.X)))
  (hPJ : IsClosed (parabolic i ν J : Set (RationalPoint k G.X)))

omit [LocallyCompactSpace A] in
include hPI hPJ in
/-- The actual stabilizer intersection is closed in the restricted kernel. -/
theorem isClosed_geometricCompactKernelIntersection : IsClosed (D : Set N) :=
  isClosed_splitKernelIntersection _ (Subgroup.subgroupOf H P)
    ((isClosed_geometricStabilizer i ν I J n hPI hPJ).preimage
      (continuous_subtype_val : Continuous (Subgroup.subtype P)))

include hUI hPI hPJ in
/-- The literal nested intersection, rather than a replacement subgroup,
is locally compact. -/
theorem geometricCompactKernelIntersection_locallyCompactSpace : LocallyCompactSpace D := by
  let : LocallyCompactSpace N :=
    geometricCompactKernel_locallyCompactSpace i ν I J dI n hUI
  exact (isClosed_geometricCompactKernelIntersection i ν I J dI n hPI hPJ).locallyCompactSpace

end Topology

section CompactOpen

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (hUI : IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))

include hUI in
/-- The required compact open subgroup basis of the actual restricted kernel
uses only the ambient nonarchimedean structure and closed radical. -/
theorem geometricCompactKernel_compactOpenBasis :
    ∀ O : Set N, IsOpen O → (1 : N) ∈ O →
      ∃ V : OpenSubgroup N, IsCompact (V : Set N) ∧ (V : Set N) ⊆ O := by
  let : LocallyCompactSpace N :=
    geometricCompactKernel_locallyCompactSpace i ν I J dI n hUI
  intro O hO h1
  exact compactOpenSubgroupBasis N O (hO.mem_nhds h1)

include hUI in
/-- Each original kernel element belongs to a compact open subgroup. The
compact-limit hypothesis is used on the original ambient radical. -/
theorem geometricCompactKernel_compactOpenCover
    (hUc : Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν I))
    (x : N) :
    ∃ V : OpenSubgroup N, IsCompact (V : Set N) ∧ x ∈ V := by
  let : LocallyCompactSpace U := hUI.locallyCompactSpace
  let e := geometricCompactKernelEquiv i ν I J dI n
  obtain ⟨V, hV, hx⟩ :=
    CorrectedFiltration.exists_compactOpen_mem_of_isLimitOfCompactSubgroups U hUc (e x)
  exact ⟨OpenSubgroup.comap e.toMonoidHom e.continuous V,
    e.toHomeomorph.isClosedEmbedding.isCompact_preimage hV, hx⟩

end CompactOpen

section Measures

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
  (hUI : IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
  (hPI : IsClosed (parabolic i ν I : Set (RationalPoint k G.X)))
  (hPJ : IsClosed (parabolic i ν J : Set (RationalPoint k G.X)))
  (hUc : Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν I))

local instance kernelMeasurableSpace : MeasurableSpace N := borel N
local instance kernelBorelSpace : BorelSpace N := ⟨rfl⟩
local instance intersectionMeasurableSpace : MeasurableSpace D := borel D
local instance intersectionBorelSpace : BorelSpace D := ⟨rfl⟩
local instance quotientMeasurableSpace : MeasurableSpace (Induction.LeftQuotient D) :=
  borel (Induction.LeftQuotient D)
local instance quotientBorelSpace : BorelSpace (Induction.LeftQuotient D) := ⟨rfl⟩

/-- A regular left Haar measure on the original restricted kernel, with its
Borel measurable structure. The choice does not depend on a representation. -/
def geometricCompactKernelHaar : Measure N := by
  letI : LocallyCompactSpace N :=
    geometricCompactKernel_locallyCompactSpace i ν I J dI n hUI
  exact haar

/-- A regular left Haar measure on the literal nested intersection, again
chosen independently of every representation. -/
def geometricCompactIntersectionHaar : Measure D := by
  letI : LocallyCompactSpace D :=
    geometricCompactKernelIntersection_locallyCompactSpace i ν I J dI n hUI hPI hPJ
  exact haar

local notation "μN" => geometricCompactKernelHaar i ν I J dI n hUI
local notation "μD" => geometricCompactIntersectionHaar i ν I J dI n hUI hPI hPJ

local instance kernelHaar_isHaarMeasure : IsHaarMeasure μN := by
  let : LocallyCompactSpace N :=
    geometricCompactKernel_locallyCompactSpace i ν I J dI n hUI
  unfold geometricCompactKernelHaar
  infer_instance
local instance kernelHaar_regular : (μN).Regular := by
  let : LocallyCompactSpace N :=
    geometricCompactKernel_locallyCompactSpace i ν I J dI n hUI
  unfold geometricCompactKernelHaar
  infer_instance
local instance intersectionHaar_isHaarMeasure : IsHaarMeasure μD := by
  let : LocallyCompactSpace D :=
    geometricCompactKernelIntersection_locallyCompactSpace i ν I J dI n hUI hPI hPJ
  unfold geometricCompactIntersectionHaar
  infer_instance
local instance intersectionHaar_regular : (μD).Regular := by
  let : LocallyCompactSpace D :=
    geometricCompactKernelIntersection_locallyCompactSpace i ν I J dI n hUI hPI hPJ
  unfold geometricCompactIntersectionHaar
  infer_instance

include hUc in
/-- The chosen kernel Haar measure is also right invariant, derived from
the compact-limit premise rather than assumed as extra data. -/
theorem geometricCompactKernelHaar_rightInvariant : IsMulRightInvariant μN := by
  let : LocallyCompactSpace N :=
    geometricCompactKernel_locallyCompactSpace i ν I J dI n hUI
  exact (Haar.compactOpenCoverUnimodularity
    (geometricCompactKernel_compactOpenCover i ν I J dI n hUI hUc)).1 μN

include hUc in
/-- The same conclusion holds for the closed nested intersection. -/
theorem geometricCompactIntersectionHaar_rightInvariant : IsMulRightInvariant μD := by
  let : LocallyCompactSpace N :=
    geometricCompactKernel_locallyCompactSpace i ν I J dI n hUI
  exact (Haar.compactOpenCoverUnimodularity
    (geometricCompactKernel_compactOpenCover i ν I J dI n hUI hUc)).2 D
      (isClosed_geometricCompactKernelIntersection i ν I J dI n hPI hPJ) μD

/-- The compatible quotient measure supplied by the proved closed-subgroup
existence theorem for these two actual two-sided Haar measures. -/
def geometricCompactQuotientMeasure : Measure (Induction.LeftQuotient D) := by
  letI : LocallyCompactSpace N :=
    geometricCompactKernel_locallyCompactSpace i ν I J dI n hUI
  letI := geometricCompactKernelHaar_rightInvariant i ν I J dI n hUI hUc
  letI := geometricCompactIntersectionHaar_rightInvariant i ν I J dI n hUI hPI hPJ hUc
  exact Classical.choose (compatibleMeasureExists D
    (isClosed_geometricCompactKernelIntersection i ν I J dI n hPI hPJ) μN μD)

local notation "μQ" => geometricCompactQuotientMeasure i ν I J dI n hUI hPI hPJ hUc

/-- All compatibility fields, including the original Weil integral formula,
hold for the selected quotient measure. -/
theorem geometricCompactQuotientMeasure_isCompatible :
    letI := geometricCompactIntersectionHaar_rightInvariant i ν I J dI n hUI hPI hPJ hUc
    IsCompatible D μN μD μQ := by
  let : LocallyCompactSpace N :=
    geometricCompactKernel_locallyCompactSpace i ν I J dI n hUI
  let := geometricCompactKernelHaar_rightInvariant i ν I J dI n hUI hUc
  let := geometricCompactIntersectionHaar_rightInvariant i ν I J dI n hUI hPI hPJ hUc
  exact Classical.choose_spec (compatibleMeasureExists D
    (isClosed_geometricCompactKernelIntersection i ν I J dI n hPI hPJ) μN μD)

local instance quotientMeasure_finiteOnCompacts : IsFiniteMeasureOnCompacts μQ := by
  let := geometricCompactIntersectionHaar_rightInvariant i ν I J dI n hUI hPI hPJ hUc
  let := (geometricCompactQuotientMeasure_isCompatible i ν I J dI n hUI hPI hPJ hUc).regular
  infer_instance

variable
  (hStandard : StandardCocharacterStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hN : HasPointNormalizerComparison i)
  (dJ : IsSemidirectDecomposition (parabolic i ν J) (levi i ν J) (unipotent i ν J))
  (hMI : IsClosed (levi i ν I : Set (RationalPoint k G.X)))
  (hprojI : Continuous dI.projection) (hprojJ : Continuous dJ.projection)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (levi i ν J) V) (hσ : IsSmooth σ)

set_option maxHeartbeats 800000 in
/-- The actual compact comparison with all kernel topology, measurable,
Haar, quotient measure and compact open basis inputs discharged. -/
def geometricCompactEquivOfCompactLimit
    (hSource : GeometricSourceDecomposition
      (parabolic i ν) (levi i ν) (unipotent i ν) I J (n : RationalPoint k G.X))
    (hTarget : GeometricTargetDecomposition
      (parabolic i ν) (levi i ν) (unipotent i ν) I J (n : RationalPoint k G.X)) :
    letI : LocallyCompactSpace N :=
      geometricCompactKernel_locallyCompactSpace i ν I J dI n hUI
    Representation.Equiv (geometricCompactSource i ν I J dI dJ n σ)
      (geometricCompactTarget i ν I J dI n hPI hPJ hSource hTarget σ) := by
  letI : LocallyCompactSpace N :=
    geometricCompactKernel_locallyCompactSpace i ν I J dI n hUI
  let : LocallyCompactSpace Q := hPI.locallyCompactSpace
  letI := geometricCompactKernelHaar_rightInvariant i ν I J dI n hUI hUc
  letI := geometricCompactIntersectionHaar_rightInvariant i ν I J dI n hUI hPI hPJ hUc
  exact geometricCompactEquiv i ν hStandard hG hi hν hN I J dI dJ n
    hPI hPJ hMI hprojI hprojJ hSource hTarget σ hσ μQ
    (geometricCompactKernel_compactOpenBasis i ν I J dI n hUI)
    μN μD inferInstance inferInstance
    (geometricCompactQuotientMeasure_isCompatible i ν I J dI n hUI hPI hPJ hUc)
    (fun O hO h1 => compactOpenSubgroupBasis Q O (hO.mem_nhds h1))

end Measures

end Langlands.Aubert.General.RationalPointFamily
