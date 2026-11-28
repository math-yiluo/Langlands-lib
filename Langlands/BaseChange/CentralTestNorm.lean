import Langlands.ClassFieldTheory.Local.NormExistenceClosedSupport
import Langlands.Group.GL.Basic

/-!
# The norm on scalar centers for local base change

The lower subgroup is the scalar image of the field norm. The upper subgroup is
the full center, and the norm between them is continuous and surjective.
-/

noncomputable section

namespace Langlands

universe u v

namespace GeneralLinear

variable {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {n : ℕ}

/-- Identify the units of the coefficient ring with the full scalar center in
positive rank, with the topology induced from the general linear group. -/
def scalarCenterContinuousEquiv (hn : 0 < n) :
    Rˣ ≃ₜ* Subgroup.center (GeneralLinear n R) := by
  let e : Rˣ ≃* Subgroup.center (GeneralLinear n R) :=
    (MonoidHom.ofInjective (scalarEmbedding (R := R) hn).injective).trans
      (MulEquiv.subgroupCongr Matrix.GeneralLinearGroup.center_eq_range_scalar.symm)
  refine
    { e with
      continuous_toFun := (scalarContinuous (n := n)).continuous.subtype_mk _
      continuous_invFun := ?_ }
  let i : Fin n := ⟨0, hn⟩
  have he : (fun z => (e.symm z : R)) = fun z => z.val i i := by
    funext z
    have h := congrArg (fun w : Subgroup.center (GeneralLinear n R) => w.val i i)
      (e.apply_symm_apply z)
    change (scalar (n := n) (e.symm z)) i i = z.val i i at h
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using h
  have hc : Continuous (fun z => (e.symm z : R)) := by
    rw [he]
    exact (entry i i).continuous.comp continuous_subtype_val
  refine Units.continuous_iff.mpr ⟨hc, ?_⟩
  change Continuous (fun z => ((e.symm z)⁻¹ : Rˣ).val)
  have hinv : Continuous (fun z => (e.symm z⁻¹ : Rˣ).val) :=
    hc.comp continuous_inv
  simpa only [map_inv] using hinv

/-- The scalar-center equivalence sends a unit to its scalar matrix. -/
@[simp]
theorem scalarCenterContinuousEquiv_apply (hn : 0 < n) (a : Rˣ) :
    scalarCenterContinuousEquiv hn a = scalarToCenter a := rfl

/-- The scalar embedding in positive rank identifies the unit group with a
closed subgroup of the general linear group. -/
theorem isClosedEmbedding_scalar [T2Space R] (hn : 0 < n) :
    Topology.IsClosedEmbedding (scalar (n := n) (R := R)) := by
  have hc : IsClosed (Subgroup.center (GeneralLinear n R) : Set (GeneralLinear n R)) := by
    simpa only [Set.centralizer_univ, Subgroup.coe_center] using
      Set.isClosed_centralizer (Set.univ : Set (GeneralLinear n R))
  exact hc.isClosedEmbedding_subtypeVal.comp
    (scalarCenterContinuousEquiv hn).toHomeomorph.isClosedEmbedding

end GeneralLinear

namespace BaseChange

open LocalClassField

variable (n : ℕ)

/-- The subgroup of scalar matrices whose scalar lies in the actual norm image. -/
def scalarNormSubgroup (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] : Subgroup (GeneralLinear n F) :=
  (normSubgroup F E).map GeneralLinear.scalar

/-- Every scalar norm matrix is central in the lower general linear group. -/
theorem scalarNormSubgroup_le_center (F : Type u) (E : Type v) [Field F] [Field E]
    [Algebra F E] [FiniteDimensional F E] :
    scalarNormSubgroup n F E ≤ Subgroup.center (GeneralLinear n F) := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  exact Subgroup.map_le_range _ _

instance (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] : (scalarNormSubgroup n F E).Normal :=
  Subgroup.normal_of_le_center (scalarNormSubgroup_le_center n F E)

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} {E : PadicField.{v} p}
  [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
  [FiniteDimensional F.Carrier E.Carrier]
  (T : F.TopologicalData) (S : E.TopologicalData) {n}

include S in
/-- The scalar norm subgroup is closed for the supplied lower topology. -/
theorem isClosed_scalarNormSubgroup (hn : 0 < n) :
    letI := T.topology
    IsClosed (scalarNormSubgroup n F.Carrier E.Carrier : Set (GeneralLinear n F.Carrier)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  rw [scalarNormSubgroup, Subgroup.coe_map]
  exact (GeneralLinear.isClosedEmbedding_scalar hn).isClosedMap _
    (ClassFieldTheory.Local.isClosed_normSubgroup F E T S)

/-- The continuous scalar norm from the full upper center to the lower norm center. -/
def scalarCenterNorm (hn : 0 < n) :
    letI := T.topology
    letI := S.topology
    Subgroup.center (GeneralLinear n E.Carrier) →ₜ* scalarNormSubgroup n F.Carrier E.Carrier := by
  letI := T.topology
  letI := S.topology
  letI := S.valuativeRel
  letI := S.localField
  let e := GeneralLinear.scalarCenterContinuousEquiv (R := E.Carrier) hn
  let f := (GeneralLinear.scalar (n := n)).comp
    ((normUnits F.Carrier E.Carrier).comp e.symm.toMonoidHom)
  exact
    { f.codRestrict (scalarNormSubgroup n F.Carrier E.Carrier)
        (fun z => ⟨_, ⟨e.symm z, rfl⟩, rfl⟩) with
      continuous_toFun := (GeneralLinear.scalarContinuous.continuous.comp
        ((localNorm T S).continuous.comp e.symm.continuous)).subtype_mk _ }

/-- The scalar norm evaluates on a scalar matrix by applying the field norm. -/
@[simp]
theorem scalarCenterNorm_apply_scalar (hn : 0 < n) (a : E.Carrierˣ) :
    letI := T.topology
    letI := S.topology
    (scalarCenterNorm T S hn (GeneralLinear.scalarToCenter a)).val =
      GeneralLinear.scalar (n := n) (normUnits F.Carrier E.Carrier a) := by
  let := T.topology
  let := S.topology
  let := S.valuativeRel
  let := S.localField
  change GeneralLinear.scalar (normUnits F.Carrier E.Carrier
    ((GeneralLinear.scalarCenterContinuousEquiv hn).symm (GeneralLinear.scalarToCenter a))) = _
  rw [← GeneralLinear.scalarCenterContinuousEquiv_apply hn, ContinuousMulEquiv.symm_apply_apply]

/-- Every element of the lower scalar norm subgroup is the norm of an upper scalar. -/
theorem scalarCenterNorm_surjective (hn : 0 < n) :
    Function.Surjective (scalarCenterNorm T S hn) := by
  rintro ⟨g, a, ⟨b, rfl⟩, rfl⟩
  exact ⟨GeneralLinear.scalarToCenter b, Subtype.ext (scalarCenterNorm_apply_scalar T S hn b)⟩

end BaseChange
end Langlands
