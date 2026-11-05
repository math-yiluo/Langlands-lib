import Langlands.BruhatTits.RationalPoints.TorusDerivedSmoothAnnihilation
import Langlands.BruhatTits.RationalPoints.AdditiveSmoothAnnihilation
import Langlands.BruhatTits.RationalPoints.SmoothRealStructureStatement
import Langlands.GroupScheme.Rational.PositivePowerFactorizationStatement
import Langlands.GroupScheme.Derived.RepresentabilityProof
import Langlands.GroupScheme.Derived.SmoothnessProof
import Langlands.Representation.Plancherel.TorusNormKernelCompactnessProof

/-! # Conditional reduction of ambient smooth real annihilation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.RationalPoints

/-- The two remaining structural inputs imply the unchanged universal
ambient smooth-real annihilation statement. -/
theorem derivedSmoothRealAnnihilation_of_structure
    (hfactor : PositivePowerTorusAdditiveFactorizationStatement.{u})
    (href : RelativeRootReflectionExistenceStatement.{u}) :
    DerivedSmoothRealAnnihilationStatement.{u} := by
  intro F _ _ _ _ G hG
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  intro f hf x hx
  obtain ⟨D, d, hDAff, hDLft, hd⟩ := derivedSubgroupRepresentability F G
  let : IsAffineHom D.X.hom := hDAff
  let : LocallyOfFiniteType D.X.hom := hDLft
  let : Smooth D.X.hom := derivedSubgroupSmoothness F G D d hd hG.smooth
  rw [← hd.2, SubgroupFunctor.mem_range] at hx
  obtain ⟨y, hy⟩ := hx
  obtain ⟨m, hm, T, i, t, φ, hT, hi, hfact⟩ := hfactor F D y
  let : IsClosedImmersion i.hom.hom.left := hi
  let : IsAffineHom T.toGrp.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  let : LocallyOfFiniteType T.toGrp.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have hderived : SubgroupFunctor.range (i ≫ d) ≤ derivedSubgroup G := by
    rw [← hd.2, SubgroupFunctor.le_def]
    intro U z hz
    obtain ⟨w, hw⟩ := SubgroupFunctor.mem_range.mp hz
    apply SubgroupFunctor.mem_range.mpr
    refine ⟨w ≫ i.hom.hom, ?_⟩
    rw [Category.assoc, ← Grp.comp_hom_hom, hw]
  have ht : f (rationalPoints.map d (rationalPoints.map i t)) = 1 := by
    simpa only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc] using
      torusImage_eq_one_of_structure hG Langlands.Plancherel.torusNormKernelCompactness
        href (i ≫ d) hT
        (hi.comp hd.1) hderived f hf t
  have hu (z : rationalPoints (VectorGroup.groupScheme (CommRingCat.of F) 1)) :
      f (rationalPoints.map d (rationalPoints.map φ z)) = 1 := by
    simpa only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc] using
      vectorImage_eq_one 1 (φ ≫ d) f hf z
  have hpow : (f x) ^ m = 1 := by
    change rationalPoints.map d y = x at hy
    rw [← hy, ← map_pow, ← map_pow, hfact, map_mul, map_mul, ht, hu, one_mul]
  exact (isOfFinOrder_iff_eq_one _).mp
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, hpow⟩)

section DerivedPointKernelMap

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

local instance derivedSmoothReductionAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance derivedSmoothReductionAmbientTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

/-- The actual derived-point inclusion, with its values in the ambient open real
kernel under the factorization and reflection premises. -/
def derivedPointsToOpenRealKernel
    (hfactor : PositivePowerTorusAdditiveFactorizationStatement.{u})
    (href : RelativeRootReflectionExistenceStatement.{u})
    (hG : IsConnectedReductive G)
    (f : rationalPoints G →* Multiplicative ℝ)
    (hf : IsOpen (f.ker : Set (rationalPoints G))) :
    (derivedSubgroup G).carrier (Over.mk (𝟙 _)) →* f.ker :=
  Subgroup.inclusion
    (derivedSmoothRealAnnihilation_of_structure hfactor href F G hG f hf)

@[simp]
theorem derivedPointsToOpenRealKernel_coe
    (hfactor : PositivePowerTorusAdditiveFactorizationStatement.{u})
    (href : RelativeRootReflectionExistenceStatement.{u})
    (hG : IsConnectedReductive G)
    (f : rationalPoints G →* Multiplicative ℝ)
    (hf : IsOpen (f.ker : Set (rationalPoints G)))
    (x : (derivedSubgroup G).carrier (Over.mk (𝟙 _))) :
    (derivedPointsToOpenRealKernel hfactor href hG f hf x : rationalPoints G) = x := rfl

end DerivedPointKernelMap

end Langlands.BruhatTits.RationalPoints
