import Langlands.GroupScheme.SimplyConnected.SpecialLinearInnerFormNormOneStatement
import Langlands.GroupScheme.SpecialLinearInnerForm.AdjointMatrix
import Langlands.GroupScheme.SpecialLinearInnerForm.GaloisDescent
import Langlands.GroupScheme.SpecialLinearInnerForm.NormOneChart
import Langlands.GroupScheme.Rational.FiniteGaloisOverlapDiscrepancy
import Langlands.GroupScheme.LocalGroupIsoOverlap

/-! # Inner forms of the special linear group are reduced-norm-one groups: proof -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.SpecialLinearInnerForm

open Langlands.CentralSimple

variable {K : Type u} [Field K] {G : GroupScheme (Spec (CommRingCat.of K))}
  (d : QuasiSplitInnerForm G)

/-- The Galois values `ξ(1, σ)` of the adjoint discrepancy cocycle on the splitting field. -/
def galoisValue (σ : d.carrier ≃ₐ[K] d.carrier) : ringTest K d.carrier ⟶ d.adjoint.X :=
  d.cocycle.toFun (𝟙 _) (ringTestMap K σ.toAlgHom)

theorem galoisValue_one : galoisValue d 1 = 1 := by
  have h : ringTestMap K (1 : d.carrier ≃ₐ[K] d.carrier).toAlgHom = 𝟙 _ :=
    ringTestMap_id K d.carrier
  rw [galoisValue, h, Cocycle.toFun_self]

/-- The Galois values form a crossed homomorphism. -/
theorem galoisValue_mul (σ τ : d.carrier ≃ₐ[K] d.carrier) :
    galoisValue d (σ * τ) =
      galoisValue d σ * (ringTestMap K σ.toAlgHom ≫ galoisValue d τ) := by
  have h : ringTestMap K (σ * τ).toAlgHom =
      ringTestMap K σ.toAlgHom ≫ ringTestMap K τ.toAlgHom := by
    rw [← ringTestMap_comp]
    rfl
  have hc := d.cocycle.cocycle (𝟙 _) (ringTestMap K σ.toAlgHom)
    (ringTestMap K σ.toAlgHom ≫ ringTestMap K τ.toAlgHom)
  have hn := d.cocycle.naturality (ringTestMap K σ.toAlgHom) (𝟙 _) (ringTestMap K τ.toAlgHom)
  rw [Category.comp_id] at hn
  rw [galoisValue, galoisValue, galoisValue, h]
  exact hc.trans (congrArg (fun z => d.cocycle.toFun (𝟙 _) (ringTestMap K σ.toAlgHom) * z) hn)

variable {m : Type} [Fintype m] [DecidableEq m]
  (i : d.model ≅ SpecialLinear.groupScheme m (CommRingCat.of K))

/-- The matrix algebra endomorphism by which the Galois value at `σ` acts. -/
abbrev galoisMatrixHom (σ : d.carrier ≃ₐ[K] d.carrier) :
    Matrix m m d.carrier →ₐ[d.carrier] Matrix m m d.carrier :=
  adjointMatrixHom d.isAdjointQuotient i (galoisValue d σ)

/-- The twisted Galois action on `M_m(L)`: apply `σ` to the entries, then act by the
Galois value `ξ(1, σ)` of the adjoint discrepancy cocycle. -/
def twistedAction : SemilinearGaloisAction K d.carrier (Matrix m m d.carrier) where
  act σ := (galoisMatrixHom d i σ).toRingHom.comp
    (σ : d.carrier →+* d.carrier).mapMatrix
  act_algebraMap σ l := by
    have h : (σ : d.carrier →+* d.carrier).mapMatrix
        (algebraMap d.carrier (Matrix m m d.carrier) l) =
          algebraMap d.carrier (Matrix m m d.carrier) (σ l) := by
      ext a b
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.algebraMap_matrix_apply]
      split_ifs <;> simp
    rw [RingHom.comp_apply, h]
    exact (galoisMatrixHom d i σ).commutes (σ l)
  act_one x := by
    change galoisMatrixHom d i 1 (x.map ((1 : d.carrier ≃ₐ[K] d.carrier) :
      d.carrier →+* d.carrier)) = x
    rw [galoisMatrixHom, galoisValue_one, adjointMatrixHom_one]
    rfl
  act_mul σ τ x := by
    change galoisMatrixHom d i (σ * τ) (x.map ((σ * τ : d.carrier ≃ₐ[K] d.carrier) :
        d.carrier →+* d.carrier)) =
      galoisMatrixHom d i σ ((galoisMatrixHom d i τ
        (x.map (τ : d.carrier →+* d.carrier))).map (σ : d.carrier →+* d.carrier))
    rw [galoisMatrixHom, galoisValue_mul, adjointMatrixHom_mul]
    congr 1
    have hn := adjointMatrixHom_naturality d.isAdjointQuotient i σ.toAlgHom
      (galoisValue d τ) (x.map (τ : d.carrier →+* d.carrier))
    refine Eq.trans ?_ hn.symm
    rw [Matrix.map_map]
    rfl

theorem twistedAction_act (σ : d.carrier ≃ₐ[K] d.carrier) (x : Matrix m m d.carrier) :
    (twistedAction d i).act σ x =
      galoisMatrixHom d i σ (x.map (σ : d.carrier →+* d.carrier)) :=
  rfl

instance : FiniteDimensional K (twistedAction d i).fixed :=
  (twistedAction d i).finiteDimensional_fixed

instance [Nonempty m] : Algebra.IsCentral K (twistedAction d i).fixed :=
  (twistedAction d i).isCentral_fixed

instance [Nonempty m] : IsSimpleRing (twistedAction d i).fixed :=
  (twistedAction d i).isSimpleRing_fixed

/-- Along any coefficient map `f`, the matrix action of `ξ(1, σ)` carries the chart along
`f ∘ σ` to the chart along `f`. -/
theorem extendMatrix_chartAlong_galois {R : Type u} [CommRing R] [Algebra K R]
    (f : d.carrier →+* R) (hf : f.comp (algebraMap K d.carrier) = algebraMap K R)
    (σ : d.carrier ≃ₐ[K] d.carrier)
    (hf' : (f.comp (σ : d.carrier →+* d.carrier)).comp (algebraMap K d.carrier) =
      algebraMap K R)
    (x : R ⊗[K] (twistedAction d i).fixed) :
    extendMatrix f (galoisMatrixHom d i σ).toLinearMap
        (chartAlong (twistedAction d i).descentEquiv (f.comp (σ : d.carrier →+* d.carrier))
          hf' x) =
      chartAlong (twistedAction d i).descentEquiv f hf x := by
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    rw [chartAlong_tmul, chartAlong_tmul, map_smul, SemilinearGaloisAction.descentEquiv_one_tmul]
    congr 1
    rw [RingHom.coe_comp, ← Matrix.map_map, extendMatrix_map]
    congr 1
    exact (twistedAction d i).act_fixed σ a
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

variable [Nonempty m]

/-- The local isomorphisms from the model to the reduced-norm-one group of the descended
algebra, through the matrix coordinates and the descent chart at each point of `Spec L`. -/
def chartLocalIso : LocalGroupIso d.model
    (CentralSimpleUnits.normOne K (twistedAction d i).fixed) (ringTest K d.carrier) where
  toFun s := (pointMatrix i _).trans
    (normOneChartPoints (twistedAction d i).descentEquiv s).symm
  naturality t s g := by
    change (normOneChartPoints (twistedAction d i).descentEquiv (t ≫ s)).symm
        (pointMatrix i _ (t ≫ g)) =
      t ≫ (normOneChartPoints (twistedAction d i).descentEquiv s).symm (pointMatrix i _ g)
    apply (normOneChartPoints (twistedAction d i).descentEquiv (t ≫ s)).injective
    rw [MulEquiv.apply_symm_apply, normOneChartPoints_naturality, MulEquiv.apply_symm_apply,
      pointMatrix_naturality]

theorem chartLocalIso_toFun {V : Over (Spec (CommRingCat.of K))}
    (s : V ⟶ ringTest K d.carrier) (g : V ⟶ d.model.X) :
    (chartLocalIso d i).toFun s g =
      (normOneChartPoints (twistedAction d i).descentEquiv s).symm (pointMatrix i _ g) :=
  rfl

/-- The Galois-pair form of the discrepancy of the chart local isomorphisms. -/
theorem chartLocalIso_galois (σ : d.carrier ≃ₐ[K] d.carrier)
    {V : Over (Spec (CommRingCat.of K))} (s : V ⟶ ringTest K d.carrier)
    (g : V ⟶ d.model.X) :
    (chartLocalIso d i).toFun s
        (d.isAdjointQuotient.innerAction.act (s ≫ galoisValue d σ) g) =
      (chartLocalIso d i).toFun (s ≫ ringTestMap K σ.toAlgHom) g := by
  obtain ⟨y, hy⟩ := (normOneChartPoints (twistedAction d i).descentEquiv
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

/-- The local isomorphisms from `G` to the reduced-norm-one group. -/
def compareLocalIso : LocalGroupIso G
    (CentralSimpleUnits.normOne K (twistedAction d i).fixed) (ringTest K d.carrier) where
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

/-- The inner form is isomorphic to the reduced-norm-one group of the descended algebra. -/
def normOneIso : G ≅ CentralSimpleUnits.normOne K (twistedAction d i).fixed := by
  obtain ⟨hsurj, hflat, hqc⟩ := fieldExtension_fpqc K d.carrier
  letI : Surjective (ringTest K d.carrier).hom := hsurj
  letI : Flat (ringTest K d.carrier).hom := hflat
  letI : QuasiCompact (ringTest K d.carrier).hom := hqc
  exact (compareLocalIso d i).descend (compareLocalIso_isIndependent d i)

end Langlands.GroupScheme.SpecialLinearInnerForm

namespace Langlands.GroupScheme

open SpecialLinearInnerForm

/-- Inner forms of `SL_{n+1}` are reduced-norm-one groups of central simple algebras of
reduced degree `n + 1`. -/
theorem specialLinearInnerFormNormOne : SpecialLinearInnerFormNormOneStatement.{u} := by
  intro K _ G n d ⟨i⟩
  refine ⟨(twistedAction d i).fixed, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, ?_, ⟨normOneIso d i⟩⟩
  exact (twistedAction d i).reducedDegree_fixed AlgEquiv.refl

end Langlands.GroupScheme
