import Langlands.ClassFieldTheory.Local.QuadraticNormTraceStatement
import Langlands.ClassFieldTheory.Local.NYLL.RelativeIntegerStructureProof
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.RingTheory.NormTrace
import Mathlib.LinearAlgebra.FreeModule.PID

/-! Transfer the finite-free determinant expansion through the actual integer rings. -/

noncomputable section

namespace Langlands.LocalClassField

universe u v

/-- The actual relative field norm has an integral quadratic error. -/
theorem quadraticNormTrace : QuadraticNormTraceStatement.{u,v} := by
  intro p hp F E hFE hbase hfinite T S a y
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := S.topology
  let := S.valuativeRel
  let := S.localField
  let := T.relativeIntegerAlgebra S
  let := T.relativeIntegerFieldAlgebra (E := E)
  let := T.relativeIntegerFieldTower (E := E)
  let := T.relativeIntegerTower S
  obtain ⟨hclosure, hfiniteInt⟩ := NYLL.relativeIntegerStructure p F E T S
  let := hclosure
  let := hfiniteInt
  let : Module.IsTorsionFree T.Integers S.Integers :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (by
      intro x z hxz
      apply Subtype.ext
      apply (algebraMap F.Carrier E.Carrier).injective
      exact congrArg Subtype.val hxz)
  let : Module.Free T.Integers S.Integers := inferInstance
  let := IsIntegralClosure.isLocalization T.Integers F.Carrier E.Carrier S.Integers
  obtain ⟨r, hr⟩ := Algebra.norm_one_add_smul a y
  refine ⟨r, ?_⟩
  have hn := Algebra.norm_localization (Rₘ := F.Carrier) (Sₘ := E.Carrier)
    T.Integers (nonZeroDivisors T.Integers) (1 + a • y)
  have ht := Algebra.trace_localization (Rₘ := F.Carrier) (Sₘ := E.Carrier)
    T.Integers (nonZeroDivisors T.Integers) y
  have hr' := congrArg (algebraMap T.Integers F.Carrier) hr
  simp only [map_add, map_one, map_mul, map_pow] at hr'
  change (Algebra.norm T.Integers (1 + a • y) : F.Carrier) =
    1 + (Algebra.trace T.Integers S.Integers y : F.Carrier) * (a : F.Carrier) +
      (r : F.Carrier) * (a : F.Carrier) ^ 2 at hr'
  change Algebra.trace F.Carrier E.Carrier (y : E.Carrier) =
    (Algebra.trace T.Integers S.Integers y : F.Carrier) at ht
  change Algebra.norm F.Carrier
      (1 + algebraMap F.Carrier E.Carrier (a : F.Carrier) * (y : E.Carrier)) =
    (Algebra.norm T.Integers (1 + a • y) : F.Carrier) at hn
  rw [hn, hr', ← ht]
  ring

end Langlands.LocalClassField
