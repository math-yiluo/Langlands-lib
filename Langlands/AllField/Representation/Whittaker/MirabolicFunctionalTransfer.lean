import Langlands.Representation.Whittaker.MirabolicFunctionalTransfer
import Langlands.AllField.Group.GL.UpperUnipotentCompactContainmentProof
import Langlands.AllField.Representation.RankinSelberg.AnalyticStatement
/-! Functional spaces and exactness inputs for the actual mirabolic restriction. -/

noncomputable section

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker
open Langlands.AllField.Whittaker

universe uF uG uV

section Algebraic

open Langlands.GeneralLinear hiding UpperUnipotentCompactContainmentStatement upperUnipotentCompactContainment upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear

variable {F : Type uF} [CommRing F] {n : ℕ}
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

end Algebraic

end Langlands.AllField.Whittaker

namespace Langlands.AllField.GeneralLinear.Mirabolic
open Langlands.GeneralLinear.Mirabolic hiding upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear.Mirabolic
open Langlands.GeneralLinear hiding UpperUnipotentCompactContainmentStatement entry upperUnipotent upperUnipotentCompactContainment upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear

universe uF

/-- Compact containment transports through the actual unipotent group
identification, for the supplied field topology. -/
theorem upperUnipotent_isLimitOfCompactSubgroups 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ) :
    letI := T.topology
    Jacquet.Localization.IsLimitOfCompactSubgroups (upperUnipotent n F) := by
  let := T.topology
  let e := upperUnipotentContinuousEquiv (n := n) (F := F)
  intro C hC
  obtain ⟨K, hK, hCK⟩ := Langlands.AllField.GeneralLinear.upperUnipotent_isLimitOfCompactSubgroups F T (n + 1)
    (e '' C) (hC.image e.continuous)
  refine ⟨K.comap e.toMonoidHom, e.toHomeomorph.isCompact_preimage.mpr hK, ?_⟩
  intro u hu
  exact hCK (Set.mem_image_of_mem e hu)

end Langlands.AllField.GeneralLinear.Mirabolic

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker
open Langlands.AllField.Whittaker

open Langlands.GeneralLinear hiding UpperUnipotentCompactContainmentStatement upperUnipotentCompactContainment upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear

universe uF uV

end Langlands.AllField.Whittaker
