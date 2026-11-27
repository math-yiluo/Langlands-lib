import Langlands.AlgebraicGeometry.FiniteEtale.GeometricGaloisFiberFunctorProof
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricFiberFiniteProof
import Langlands.AlgebraicGeometry.FiniteEtale.CoverPowerLift
import Langlands.AlgebraicGeometry.PointTopology.AffineWeilRestrictionRepresentability
import Mathlib.CategoryTheory.Galois.Decomposition
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.RingTheory.Etale.Field

/-! # A finite separable field extension splitting a geometric fibre -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.FiniteEtale

universe u

/-- All lifts in the given finite étale fibre are values of points over
one finite separable subextension of the geometric point's field. -/
def FiniteSeparableFiberSplitStatement : Prop :=
  ∀ (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    (Y : Cover (Spec (.of K))),
    ∃ E : IntermediateField K Ω, Module.Finite K E ∧ Algebra.IsSeparable K E ∧
      Function.Surjective (fun y : RingPoint K Y.obj E => ringTestMap K E.val ≫ y)

/-- A representing finite étale cover supplies all points in the fibre.
Its chosen point has a finite separable field of definition. -/
theorem finiteSeparableFiberSplit : FiniteSeparableFiberSplitStatement.{u} := by
  intro K Ω _ _ _ _ Y
  let s := Spec.algebraMap K Ω
  let hs (Z : Cover (Spec (.of K))) : Finite (Fiber s Z) := geometricFiberFinite s Z
  let hG := geometricGaloisFiberFunctor s hs
  let : GaloisCategory (Cover (Spec (.of K))) := Classical.choose hG
  let : PreGaloisCategory.FiberFunctor (fiberFunctor s hs) := Classical.choose_spec hG
  obtain ⟨Z, z, -, hz⟩ := CategoryTheory.PreGaloisCategory.exists_galois_representative
    (fiberFunctor s hs) Y
  have : IsAffine Z.obj.left := isAffine_of_isAffineHom Z.obj.hom
  let A := AffineCoordinateRing K Z.obj
  let i := affineSchemeOverIso K Z.obj
  have hfinite : IsFinite (Spec.algebraMap K A) := by
    rw [affineCoordinateSpecMap]
    infer_instance
  have hetale : Etale (Spec.algebraMap K A) := by
    rw [affineCoordinateSpecMap]
    infer_instance
  have : Module.Finite K A :=
    RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff _).mp hfinite)
  have : Algebra.Etale K A :=
    RingHom.etale_algebraMap.mp (HasRingHomProperty.Spec_iff.mp hetale)
  let zΩ : RingPoint K Z.obj Ω := z
  let a : A →ₐ[K] Ω := affineRingPointEquiv K A Ω (zΩ ≫ i.hom)
  have : Module.Finite K a.range :=
    Module.Finite.of_surjective a.rangeRestrict.toLinearMap a.rangeRestrict_surjective
  let E := Algebra.IsAlgebraic.toIntermediateField a.range
  have hE : Module.Finite K E := ‹Module.Finite K a.range›
  let aE : A →ₐ[K] E := a.rangeRestrict
  have hsep : Algebra.IsSeparable K E :=
    (Algebra.FormallyUnramified.iff_isSeparable K E).mp
      (Algebra.FormallyUnramified.of_surjective aE a.rangeRestrict_surjective)
  let zE : RingPoint K Z.obj E := ringTestMap K aE ≫ i.inv
  have hzE : ringTestMap K E.val ≫ zE = zΩ := by
    rw [show zE = ringTestMap K aE ≫ i.inv from rfl, ← Category.assoc, ← ringTestMap_comp]
    change ringTestMap K a ≫ i.inv = zΩ
    rw [ringTestMap_affineRingPointEquiv, Category.assoc, i.hom_inv_id, Category.comp_id]
  refine ⟨E, hE, hsep, fun y => ?_⟩
  obtain ⟨f, hf⟩ := hz.2 y
  exact ⟨zE ≫ f.hom, (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ f.hom) hzE).trans hf)⟩

/-- Under the pointed map from a finite separable splitting field, every
element acts trivially on the original finite étale fibre. -/
theorem splitFiber_fundamentalGroupMap_smul (K Ω : Type u) [Field K] [Field Ω]
    [Algebra K Ω] [IsAlgClosed Ω] (Y : Cover (Spec (.of K))) (E : IntermediateField K Ω)
    [Module.Finite K E] [Algebra.IsSeparable K E]
    (hE : Function.Surjective (fun y : RingPoint K Y.obj E => ringTestMap K E.val ≫ y))
    (g : FundamentalGroup (Spec.algebraMap E Ω) (geometricFiberFinite _)) (y : Fiber
      (Spec.algebraMap K Ω) Y) :
    fundamentalGroupMap (Spec.algebraMap K E) (Spec.algebraMap E Ω) (Spec.algebraMap K Ω)
      (by
        rw [Spec.algebraMap, Spec.algebraMap, Spec.algebraMap, ← Spec.map_comp,
          ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq])
      (geometricFiberFinite _) (geometricFiberFinite _) g • y = y := by
  let Z := fieldExtensionCover K E
  let x : Fiber (Spec.algebraMap K Ω) Z := ringTestMap K E.val
  let φ := fundamentalGroupMap Z.obj.hom x.left (Spec.algebraMap K Ω) (Over.w x)
    (geometricFiberFinite _) (geometricFiberFinite _)
  change φ g • y = y
  have hfix : φ g • x = x := by
    have hx : φ g ∈ φ.range := ⟨g, rfl⟩
    rw [show φ.range = MulAction.stabilizer _ x from
      range_fundamentalGroupMap (Spec.algebraMap K Ω) (geometricFiberFinite _) Z x
        (geometricFiberFinite _)] at hx
    exact hx
  obtain ⟨v, rfl⟩ := hE y
  let f : Z ⟶ Y := ObjectProperty.homMk v
  change (φ g) • (x ≫ f.hom) = x ≫ f.hom
  rw [smul_naturality, hfix]

end Langlands.AlgebraicGeometry.FiniteEtale
