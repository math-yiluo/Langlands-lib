import Langlands.Representation.Induction.SplitKernelHaarTrivial
import Langlands.Representation.Induction.SplitStagesRetraction
import Langlands.Group.GL.MirabolicMixedOrbitStages
import Langlands.Group.GL.MirabolicMixedOrbitRadicals

/-! The actual left-orbit stages Haar ratio is one at both representatives. -/

noncomputable section

namespace Langlands.Derivative.MirabolicProductMinus

open GeneralLinear GeneralLinear.Mirabolic GeneralLinear.Mirabolic.MixedOrbit
  Induction
open scoped NNReal

universe uR

variable {R : Type uR} [CommRing R] (k r : ℕ) (i : Fin 2)

/-- Both actual left stabilizers contain the whole plus-projection kernel. -/
theorem leftPhiKernel_le_stabilizer :
    (plusProjection (n := k + r + 1) (F := R)).ker ≤ leftStabilizer k r R i := by
  intro g hg
  have hu : g.val ∈ radical (k + r + 2) R :=
    (projection_eq_one_iff g.val).mp (congrArg Subtype.val hg)
  have hi : (⟨g.val, hu⟩ : radical (k + r + 2) R) ∈ leftRadicalIntersection k r R i := by
    rw [leftRadicalIntersection_eq_top]
    exact Subgroup.mem_top _
  exact hi

/-- The same kernel containment supplies the actual restricted stages retraction. -/
theorem leftPhiKernel_le_stages :
    (plusProjection (n := k + r + 1) (F := R)).ker ≤ leftStages k r R i :=
  (leftPhiKernel_le_stabilizer k r i).trans (leftStabilizer_le_stages k r R i)

/-- The actual restricted retraction used in the Haar computation. -/
abbrev leftPhiHaarRetraction :=
  splitStagesRetraction (plusProjection (n := k + r + 1) (F := R))
    plusSuccessor plusProjection_plusSuccessor (leftStages k r R i)
    (leftPhiKernel_le_stages k r i)

local notation "p" => plusProjection (n := k + r + 1) (F := R)
local notation "s" => plusSuccessor (n := k + r + 1) (F := R)
local notation "P" => leftStages k r R i
local notation "H" => leftStabilizer k r R i
local notation "rP" => leftPhiHaarRetraction k r (R := R) i
local notation "sP" => MonoidHom.subgroupComap s P
local notation "HP" => Subgroup.subgroupOf H P

/-- The nested kernel is still contained in the actual nested inducing subgroup. -/
theorem leftPhiStagesKernel_le_stabilizer : (rP).ker ≤ HP := by
  intro n hn
  exact leftPhiKernel_le_stabilizer k r i (congrArg Subtype.val hn)

/-- Section containment is used only over the actual section preimage. -/
theorem leftPhiHaar_section_mem (l : (P).comap s) : sP l ∈ HP := by
  have hl := l.property
  change p (s l.val) ∈ leftSection k r R i at hl
  rw [plusProjection_plusSuccessor] at hl
  exact hl

section Topology

variable [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]

theorem leftPhiHaar_stabilizer_isClosed : IsClosed (HP : Set P) :=
  (leftStabilizer_isClosed k r R i).preimage continuous_subtype_val

omit [IsTopologicalRing R] in
/-- The actual restricted retraction has closed kernel. -/
theorem leftPhiHaar_kernel_isClosed : IsClosed ((rP).ker : Set P) :=
  isClosed_singleton.preimage
    (continuous_splitStagesRetraction p s plusProjection_plusSuccessor P
      (leftPhiKernel_le_stages k r i) continuous_plusProjection)

/-- Local compactness follows from the closed matrix subgroups and the actual
continuous retraction; it is not a further condition on a p-adic application. -/
theorem leftPhiHaar_kernel_locallyCompact
    [LocallyCompactSpace (GeneralLinear (k + r + 3) R)] :
    LocallyCompactSpace (leftPhiHaarRetraction k r (R := R) i).ker := by
  let : LocallyCompactSpace (mirabolic (k + r + 2) R) :=
    Mirabolic.locallyCompactSpace
  let : LocallyCompactSpace (plusSubgroup (k + r + 1) R) :=
    plusSubgroup_isClosed.locallyCompactSpace
  let : LocallyCompactSpace (leftStages k r R i) :=
    (leftStages_isClosed k r R i).locallyCompactSpace
  exact (leftPhiHaar_kernel_isClosed k r i).locallyCompactSpace

variable [LocallyCompactSpace (leftPhiHaarRetraction k r (R := R) i).ker]
variable [MeasurableSpace (leftPhiHaarRetraction k r (R := R) i).ker]
variable [BorelSpace (leftPhiHaarRetraction k r (R := R) i).ker]
variable [MeasurableSpace (((leftStabilizer k r R i).subgroupOf (leftStages k r R i)).comap
  (leftPhiHaarRetraction k r (R := R) i).ker.subtype)]
variable [BorelSpace (((leftStabilizer k r R i).subgroupOf (leftStages k r R i)).comap
  (leftPhiHaarRetraction k r (R := R) i).ker.subtype)]

/-- At both actual left orbit representatives, the exact restricted-stages
intersection-to-kernel Haar character is the constant character one. -/
theorem leftPhiStagesHaarRatio_eq_one :
    splitKernelHaarRatio rP sP HP (leftPhiHaar_section_mem k r i)
      (leftPhiHaar_stabilizer_isClosed k r i) = 1 :=
  splitKernelHaarRatio_eq_one_of_ker_le rP HP
    (leftPhiStagesKernel_le_stabilizer k r i) sP (leftPhiHaar_section_mem k r i)
    (leftPhiHaar_stabilizer_isClosed k r i)

end Topology

section Padic

variable {p₀ : ℕ} [Fact p₀.Prime] {F : PadicField.{uR} p₀} (T : F.TopologicalData)

/-- The actual ratio is one for every supplied p-adic topology, with local
compactness derived and the actual kernel and intersection given their Borel structures. -/
theorem padic_leftPhiStagesHaarRatio_eq_one :
    letI := T.topology
    letI := T.fieldT2
    letI := isTopologicalRing_of_topologicalData F T
    letI := T.generalLinearLocallyCompactSpace (k + r + 3)
    letI := leftPhiHaar_kernel_locallyCompact k r (R := F.Carrier) i
    letI : MeasurableSpace (leftPhiHaarRetraction k r (R := F.Carrier) i).ker := borel _
    letI : BorelSpace (leftPhiHaarRetraction k r (R := F.Carrier) i).ker := ⟨rfl⟩
    letI : MeasurableSpace
        (((leftStabilizer k r F.Carrier i).subgroupOf (leftStages k r F.Carrier i)).comap
          (leftPhiHaarRetraction k r (R := F.Carrier) i).ker.subtype) := borel _
    letI : BorelSpace
        (((leftStabilizer k r F.Carrier i).subgroupOf (leftStages k r F.Carrier i)).comap
          (leftPhiHaarRetraction k r (R := F.Carrier) i).ker.subtype) := ⟨rfl⟩
    splitKernelHaarRatio (leftPhiHaarRetraction k r (R := F.Carrier) i)
      (plusSuccessor.subgroupComap (leftStages k r F.Carrier i))
      ((leftStabilizer k r F.Carrier i).subgroupOf (leftStages k r F.Carrier i))
      (leftPhiHaar_section_mem k r i) (leftPhiHaar_stabilizer_isClosed k r i) = 1 := by
  let := T.topology
  let := T.fieldT2
  let := isTopologicalRing_of_topologicalData F T
  let := T.generalLinearLocallyCompactSpace (k + r + 3)
  let := leftPhiHaar_kernel_locallyCompact k r (R := F.Carrier) i
  let : MeasurableSpace (leftPhiHaarRetraction k r (R := F.Carrier) i).ker := borel _
  let : BorelSpace (leftPhiHaarRetraction k r (R := F.Carrier) i).ker := ⟨rfl⟩
  let : MeasurableSpace
      (((leftStabilizer k r F.Carrier i).subgroupOf (leftStages k r F.Carrier i)).comap
        (leftPhiHaarRetraction k r (R := F.Carrier) i).ker.subtype) := borel _
  let : BorelSpace
      (((leftStabilizer k r F.Carrier i).subgroupOf (leftStages k r F.Carrier i)).comap
        (leftPhiHaarRetraction k r (R := F.Carrier) i).ker.subtype) := ⟨rfl⟩
  exact leftPhiStagesHaarRatio_eq_one k r i

end Padic

end Langlands.Derivative.MirabolicProductMinus
