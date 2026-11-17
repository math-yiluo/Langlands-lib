import Langlands.GroupScheme.Reductive.RelativeRootScalingTorus
import Langlands.GroupScheme.Reductive.RootKernelCenter
import Langlands.GroupScheme.FppfQuotientUniqueness
import Langlands.GroupScheme.Torus.WeilRestrictionSplit
import Mathlib.RingTheory.Etale.Pi

/-! # The adjoint torus on an affine pinned split chart -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace splitTorus

variable (R : CommRingCat.{u}) {I J : Type u} [Fintype I] [Fintype J]

local instance : DecidableEq I := Classical.decEq _

/-- The monomial projection has the full kernel defined by its exponent relations. -/
theorem kernel_range_exponentTorusProjection (m : J → I → ℤ) :
    SubgroupFunctor.range (kernelι (exponentTorusProjection R m)) =
      SubgroupFunctor.range
        (Diagonalizable.exponentKernelHom R I (AddSubgroup.closure (Set.range m))) := by
  classical
  ext U t
  rw [mem_range_kernelι_iff, Diagonalizable.mem_range_exponentKernelHom_iff]
  constructor
  · intro ht n hn
    induction hn using AddSubgroup.closure_induction with
    | mem n hn =>
      obtain ⟨j, rfl⟩ := hn
      change (∏ i, pointsEquiv I U t i ^ m j i) = 1
      have h := congrArg (fun x => pointsEquiv J U x j) ht
      simpa only [exponentTorusProjection_points, map_one, Pi.one_apply] using h
    | zero => exact map_one _
    | add n n' hn hn' ih ih' =>
      change exponentValue I (pointsEquiv I U t) (.ofAdd n * .ofAdd n') = 1
      rw [map_mul, ih, ih', mul_one]
    | neg n hn ih =>
      change exponentValue I (pointsEquiv I U t) ((.ofAdd n)⁻¹) = 1
      rw [map_inv, ih, inv_one]
  · intro ht
    apply (pointsEquiv J U).injective
    funext j
    rw [exponentTorusProjection_points, map_one, Pi.one_apply]
    exact ht (m j) (AddSubgroup.subset_closure ⟨j, rfl⟩)

end splitTorus

namespace AffinePinnedModel

variable (M : AffinePinnedModel.{u})

local instance : DecidableEq M.coordinates := Classical.decEq _

/-- The simple-root split torus of a supplied affine pinned model. -/
abbrev adjointChartTorus : GroupScheme M.base :=
  splitTorus M.base M.basis.support

/-- Evaluation on the supplied simple roots, over the original base ring. -/
def adjointChartProjection :
    splitTorus M.base M.coordinates ⟶ M.adjointChartTorus :=
  splitTorus.exponentTorusProjection (CommRingCat.of M.ring)
    (fun a : M.basis.support => M.rootDatum.root a)

/-- Simple-root relations generate the entire integral root subgroup, without saturation. -/
theorem simpleRootExponentSpan :
    AddSubgroup.closure (Set.range (fun a : M.basis.support => M.rootDatum.root a)) =
      CoordinateRootDatum.rootExponentSpan M.rootDatum := by
  have hrange : Set.range (fun a : M.basis.support => M.rootDatum.root a) =
      M.rootDatum.root '' M.basis.support := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, a.property, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  rw [hrange, CoordinateRootDatum.rootExponentSpan,
    ← Submodule.span_int_eq_addSubgroupClosure,
    ← Submodule.span_int_eq_addSubgroupClosure, M.basis.span_int_root_support]

/-- The full central subgroup inside the supplied split torus is its root kernel. -/
theorem rootKernel_range_eq_center_comap :
    SubgroupFunctor.range
      (Diagonalizable.exponentKernelHom (CommRingCat.of M.ring) M.coordinates
        (CoordinateRootDatum.rootExponentSpan M.rootDatum)) =
      (center M.group).comap M.inclusion := by
  classical
  let c := Diagonalizable.exponentKernelHom (CommRingCat.of M.ring) M.coordinates
    (CoordinateRootDatum.rootExponentSpan M.rootDatum)
  have hc : SubgroupFunctor.range (c ≫ M.inclusion) = center M.group :=
    M.centerKernel_isSchemeTheoreticCenter.2
  let : IsClosedImmersion M.inclusion.hom.hom.left := M.closed
  let : Mono M.inclusion.hom.hom := Over.mono_of_mono_left _
  ext U t
  rw [SubgroupFunctor.mem_range, SubgroupFunctor.mem_comap, ← hc,
    SubgroupFunctor.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, by rw [Grp.comp_hom_hom, Category.assoc]⟩
  · rintro ⟨x, hx⟩
    refine ⟨x, (cancel_mono M.inclusion.hom.hom).mp ?_⟩
    simpa only [Grp.comp_hom_hom, Category.assoc] using hx

/-- The actual simple-root projection is the full fppf central quotient on the chart. -/
theorem adjointChartProjection_isFppfQuotient :
    RelativeRoot.IsFppfQuotient ((center M.group).comap M.inclusion)
      M.adjointChartProjection := by
  have hf := splitTorus.exponentTorusProjection_fppf (CommRingCat.of M.ring)
    (fun a : M.basis.support => M.rootDatum.root a)
    M.basis.linearIndepOn_root.linearIndependent
  refine ⟨hf.1, hf.2.1, hf.2.2, ?_⟩
  rw [adjointChartProjection, splitTorus.kernel_range_exponentTorusProjection,
    M.simpleRootExponentSpan, M.rootKernel_range_eq_center_comap]

/-- Any supplied full central quotient of the chart torus has the explicit split Weil model. -/
def adjointChartWeilIso (D : GroupScheme M.base)
    (q : splitTorus M.base M.coordinates ⟶ D)
    (hq : RelativeRoot.IsFppfQuotient ((center M.group).comap M.inclusion) q) :
    D ≅ WeilGm.groupScheme (CommRingCat.of M.ring)
      (M.basis.support → CommRingCat.of M.ring) :=
  FppfQuotientComparison.fppfIso hq M.adjointChartProjection_isFppfQuotient ≪≫
    (WeilGm.splitIso (CommRingCat.of M.ring) M.basis.support).symm

/-- The split coefficient algebra is finite, projective and étale, including empty support. -/
theorem adjointChartCoefficient_properties :
    Module.Finite M.ring (M.basis.support → M.ring) ∧
      Module.Projective M.ring (M.basis.support → M.ring) ∧
      Algebra.Etale M.ring (M.basis.support → M.ring) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

end AffinePinnedModel

end Langlands.GroupScheme
