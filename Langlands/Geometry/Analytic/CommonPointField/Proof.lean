import Langlands.Geometry.Analytic.CommonPointField.Statement
import Langlands.Geometry.Analytic.CommonPointField.PointRealization
import Langlands.Geometry.Analytic.CommonPointField.Transport
import Langlands.Geometry.Analytic.ValuedField.CommonFieldFamily
import Langlands.Geometry.Analytic.ValuedField.CompleteAlgebraicClosure

/-! # A common complete algebraically closed analytic point field -/

noncomputable section

universe u v uL

namespace Langlands.Analytic.SaturatedAtlasPresentation

open AffinoidAtlasPresentation ValuedField PointFieldTransport

/-- One complete algebraically closed ultrametric coefficient field realizes
every point, in the precise independent universe of the published statement. -/
theorem commonAlgebraicallyClosedPointField :
    CommonAlgebraicallyClosedPointFieldStatement.{u, v, uL} := by
  intro K _ _ _ X
  obtain ⟨A, rfl⟩ := (localizedObjectEquiv (K := K)).surjective X
  let K' : Type (max u (v + 1) uL) := ULift.{max u (v + 1) uL} K
  let I : Type (max u (v + 1) uL) := ULift.{max u (v + 1) uL} A.presentation.space
  let E (i : I) : Type (max u (v + 1) uL) :=
    ULift.{max u (v + 1) uL} (PointField.Carrier A.presentation i.down)
  let (i : I) : NormedAlgebra K' (E i) :=
    liftBaseNormedAlgebra (F := K) (E i)
  let F := CommonFieldFamily K' E
  let e (x : A.presentation.space) : PointField.Carrier A.presentation x →+* F :=
    (CommonFieldFamily.embedding K' E (ULift.up x)).toAlgHom.toRingHom.comp
      (ULift.ringEquiv : E (ULift.up x) ≃+* PointField.Carrier A.presentation x).symm.toRingHom
  have he (x : A.presentation.space) (a : PointField.Carrier A.presentation x) :
      ‖e x a‖ = ‖a‖ := by
    exact CommonFieldFamily.norm_embedding K' E (ULift.up x) (ULift.up a)
  let L := CompleteAlgebraicClosure F
  let c : K →+* L :=
    (algebraMap F L).comp ((algebraMap K' F).comp
      (ULift.ringEquiv : K' ≃+* K).symm.toRingHom)
  have hc (k : K) : ‖c k‖ = ‖k‖ := by
    change ‖algebraMap F L (algebraMap K' F (ULift.up k))‖ = ‖k‖
    rw [norm_algebraMap', norm_algebraMap']
    rfl
  let : NormedAlgebra K L := {
    __ := c.toAlgebra
    norm_smul_le k a := by
      change ‖c k * a‖ ≤ ‖k‖ * ‖a‖
      rw [norm_mul, hc]
  }
  let f (x : A.presentation.space) : PointField.Carrier A.presentation x →ₐ[K] L := {
    toRingHom := (algebraMap F L).comp (e x)
    commutes' k := by
      change algebraMap F L
          (CommonFieldFamily.embedding K' E (ULift.up x)
            (ULift.up (algebraMap K (PointField.Carrier A.presentation x) k))) =
        algebraMap F L (algebraMap K' F (ULift.up k))
      exact congrArg (algebraMap F L)
        ((CommonFieldFamily.embedding K' E (ULift.up x)).toAlgHom.commutes (ULift.up k))
  }
  have hf (x : A.presentation.space) : Isometry (f x) := by
    apply AddMonoidHomClass.isometry_of_norm (f x)
    intro a
    change ‖algebraMap F L (e x a)‖ = ‖a‖
    rw [norm_algebraMap', he]
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  change Function.Surjective
    (fun p : FieldPoint L A.presentation => ULift.up p.point)
  intro x
  refine ⟨(PointField.fieldPoint A.presentation x.down).mapField (f x.down) (hf x.down), ?_⟩
  cases x
  rfl

end Langlands.Analytic.SaturatedAtlasPresentation
