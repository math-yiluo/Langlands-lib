import Langlands.GroupScheme.SymplecticInnerForm.TwistedAction
import Langlands.GroupScheme.SymplecticInnerForm.NormOneChart
import Langlands.GroupScheme.SimplyConnected.SymplecticInnerFormInvolutionStatement
import Langlands.GroupScheme.SymplecticMatrix.StandardComparison
import Langlands.GroupScheme.Rational.FiniteGaloisOverlapDiscrepancy
import Langlands.GroupScheme.LocalGroupIsoOverlap

/-! # Descent to the norm-one group of a symplectic involution -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.SymplecticInnerForm

open Langlands.CentralSimple
open SpecialLinearInnerForm (galoisValue pointScalars pointScalars_comp_algebraMap
  pointScalars_comp_ringTestMap chartAlong_congr)

variable {K : Type u} [Field K] {G : GroupScheme (Spec (CommRingCat.of K))}
  (d : QuasiSplitInnerForm G)
  {n : Type} [Fintype n] [DecidableEq n]
  (i : d.model ≅ SymplecticMatrix.groupScheme n (CommRingCat.of K))

/-- The descent chart has the standard alternating adjoint identity. -/
theorem descendedChartCompatibility
    (x : d.carrier ⊗[K] (twistedAction d i).fixed) :
    (twistedAction d i).descentEquiv ((descendedInvolution d i).baseChange d.carrier x) *
        Matrix.J n d.carrier =
      Matrix.J n d.carrier * ((twistedAction d i).descentEquiv x).transpose := by
  rw [descentEquiv_descendedInvolution, standardInvolution_mul_J]

variable [Nonempty n]

/-- The local isomorphisms from the model to the norm-one isometry group of the descended
involution, through matrix coordinates and the chart at each point of `Spec L`. -/
def chartLocalIso : LocalGroupIso d.model
    (normOneGroup (descendedInvolution d i)) (ringTest K d.carrier) where
  toFun s := (pointMatrix i _).trans
    (normOneChartPoints (twistedAction d i).descentEquiv (descendedChartCompatibility d i) s).symm
  naturality t s g := by
    change (normOneChartPoints (twistedAction d i).descentEquiv (descendedChartCompatibility d i) (t ≫ s)).symm
        (pointMatrix i _ (t ≫ g)) =
      t ≫ (normOneChartPoints (twistedAction d i).descentEquiv (descendedChartCompatibility d i) s).symm (pointMatrix i _ g)
    apply (normOneChartPoints (twistedAction d i).descentEquiv (descendedChartCompatibility d i) (t ≫ s)).injective
    rw [MulEquiv.apply_symm_apply, normOneChartPoints_naturality, MulEquiv.apply_symm_apply,
      pointMatrix_naturality]

theorem chartLocalIso_toFun {V : Over (Spec (CommRingCat.of K))}
    (s : V ⟶ ringTest K d.carrier) (g : V ⟶ d.model.X) :
    (chartLocalIso d i).toFun s g =
      (normOneChartPoints (twistedAction d i).descentEquiv (descendedChartCompatibility d i) s).symm (pointMatrix i _ g) :=
  rfl

/-- The Galois-pair form of the discrepancy of the chart local isomorphisms. -/
theorem chartLocalIso_galois (σ : d.carrier ≃ₐ[K] d.carrier)
    {V : Over (Spec (CommRingCat.of K))} (s : V ⟶ ringTest K d.carrier)
    (g : V ⟶ d.model.X) :
    (chartLocalIso d i).toFun s
        (d.isAdjointQuotient.innerAction.act (s ≫ galoisValue d σ) g) =
      (chartLocalIso d i).toFun (s ≫ ringTestMap K σ.toAlgHom) g := by
  obtain ⟨y, hy⟩ := (normOneChartPoints (twistedAction d i).descentEquiv (descendedChartCompatibility d i)
    (s ≫ ringTestMap K σ.toAlgHom)).surjective (pointMatrix i V g)
  rw [chartLocalIso_toFun, chartLocalIso_toFun, ← hy, MulEquiv.symm_apply_apply,
    MulEquiv.symm_apply_eq]
  apply Subtype.ext
  rw [pointMatrix_innerAction, ← hy, normOneChartPoints_val, normOneChartPoints_val,
    chartAlong_congr _ _ (pointScalars_comp_ringTestMap s σ)]
  exact extendMatrix_chartAlong_galois d i (pointScalars s) (pointScalars_comp_algebraMap s) σ
    _ _

/-- The chart local isomorphisms have the adjoint discrepancy cocycle of the inner form. -/
theorem chartLocalIso_hasDiscrepancy :
    (chartLocalIso d i).HasDiscrepancy d.isAdjointQuotient.innerAction d.cocycle := by
  rw [LocalGroupIso.hasDiscrepancy_iff_overlap]
  apply LocalGroupIso.hasOverlapDiscrepancy_of_galois
  intro σ V s g
  have h : Cocycle.galoisPair σ ≫ d.cocycle.overlap = galoisValue d σ := by
    rw [galoisValue, Cocycle.toFun_eq_lift_overlap]
    rfl
  rw [h]
  exact chartLocalIso_galois d i σ s g

/-- The local isomorphisms from `G` to the norm-one involution-isometry group. -/
def compareLocalIso : LocalGroupIso G
    (normOneGroup (descendedInvolution d i)) (ringTest K d.carrier) where
  toFun b := (d.localIso.toFun b).symm.trans ((chartLocalIso d i).toFun b)
  naturality t b g := by
    change (chartLocalIso d i).toFun (t ≫ b) ((d.localIso.toFun (t ≫ b)).symm (t ≫ g)) =
      t ≫ (chartLocalIso d i).toFun b ((d.localIso.toFun b).symm g)
    rw [← (chartLocalIso d i).naturality]
    congr 1
    exact d.localIso.symm.naturality t b g

/-- Having the same discrepancy, the two local isomorphisms differ by independent maps. -/
theorem compareLocalIso_isIndependent : (compareLocalIso d i).IsIndependent := by
  intro Z b c h
  change (chartLocalIso d i).toFun b ((d.localIso.toFun b).symm h) =
    (chartLocalIso d i).toFun c ((d.localIso.toFun c).symm h)
  obtain ⟨g, rfl⟩ := (d.localIso.toFun c).surjective h
  rw [MulEquiv.symm_apply_apply, ← d.hasDiscrepancy b c g, MulEquiv.symm_apply_apply]
  exact chartLocalIso_hasDiscrepancy d i b c g

/-- The inner form is isomorphic to the norm-one isometry group of the descended involution. -/
def normOneIso : G ≅ normOneGroup (descendedInvolution d i) := by
  obtain ⟨hsurj, hflat, hqc⟩ := fieldExtension_fpqc K d.carrier
  letI : Surjective (ringTest K d.carrier).hom := hsurj
  letI : Flat (ringTest K d.carrier).hom := hflat
  letI : QuasiCompact (ringTest K d.carrier).hom := hqc
  exact (compareLocalIso d i).descend (compareLocalIso_isIndependent d i)

end Langlands.GroupScheme.SymplecticInnerForm

namespace Langlands.GroupScheme

open SymplecticInnerForm

/-- A symplectic inner form is the norm-one isometry group of a descended involution. -/
theorem symplecticInnerFormInvolution : SymplecticInnerFormInvolutionStatement.{u} := by
  intro K _ G n d hn ⟨i⟩
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let j := i ≪≫ (SymplecticMatrix.comparisonIso K n).symm
  refine ⟨(twistedAction d j).fixed, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, ?_, descendedInvolution d j,
    hasStandardSymplecticSplitting d n j, ⟨normOneIso d j⟩⟩
  simpa using reducedDegree_twistedAction d j

end Langlands.GroupScheme
