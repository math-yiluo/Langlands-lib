import Langlands.GroupScheme.RelativeUnipotent.Basic
import Langlands.GroupScheme.Descent.ClosedSubgroups
import Langlands.GroupScheme.Descent.AffineFppfQuotient
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-! # Effective descent of one represented filtration step -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeUnipotent

open Descent

variable {B S : Scheme.{u}} (p : S ⟶ B) {H : GroupScheme B}
    {N Q : GroupScheme S} (i : N ⟶ (GroupScheme.baseChange p).obj H)
    (q : (GroupScheme.baseChange p).obj H ⟶ Q)

/-- An actual smooth closed filtration term and its actual affine fppf quotient,
with exact recovery of both supplied local maps. -/
structure FiltrationStepDescentData where
  kernel : GroupScheme B
  quotient : GroupScheme B
  inclusion : kernel ⟶ H
  projection : H ⟶ quotient
  kernel_affine : IsAffine kernel.X.left
  quotient_affine : IsAffine quotient.X.left
  isClosed : IsClosedSubgroup inclusion
  kernel_smooth : Smooth kernel.X.hom
  quotient_smooth : Smooth quotient.X.hom
  isNormal : (SubgroupFunctor.range inclusion).IsNormal
  isFppfQuotient : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range inclusion) projection
  kernelIso : (GroupScheme.baseChange p).obj kernel ≅ N
  kernel_recovery : (GroupScheme.baseChange p).map inclusion = kernelIso.hom ≫ i
  quotientIso : (GroupScheme.baseChange p).obj quotient ≅ Q
  quotient_recovery : (GroupScheme.baseChange p).map projection ≫ quotientIso.hom = q

private theorem smooth_of_baseChange_iso [Flat p] [Surjective p] [QuasiCompact p]
    (K : GroupScheme B) (L : GroupScheme S)
    (e : (GroupScheme.baseChange p).obj K ≅ L) (hs : Smooth L.X.hom) :
    Smooth K.X.hom := by
  let : Smooth L.X.hom := hs
  let : IsIso e.hom.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso e)).hom)
  have h : Smooth ((GroupScheme.baseChange p).obj K).X.hom := by
    rw [← Over.w e.hom.hom.hom]
    infer_instance
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (f := K.X.hom) (g := p) ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ h

variable [IsAffine B] [IsAffine S] [Flat p] [Surjective p]
    [IsAffine H.X.left] [IsAffine Q.X.left]

/-- Overlap invariance of the supplied smooth closed term effectively descends
both that term and its supplied smooth affine fppf quotient. -/
theorem nonempty_filtrationStepDescentData
    (hi : IsClosedSubgroup i) (hN : Smooth N.X.hom) (hQ : Smooth Q.X.hom)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    (h : SubgroupFunctor.range
        ((GroupScheme.baseChange (fst p)).map i ≫ (canonicalOverlap p H).hom) =
      SubgroupFunctor.range ((GroupScheme.baseChange (snd p)).map i)) :
    Nonempty (FiltrationStepDescentData p i q) := by
  obtain ⟨K, j, eK, hK, hj, heK⟩ := hi.exists_descent_of_overlap_range_eq p h
  let : IsAffine K.X.left := hK
  let : IsClosedImmersion j.hom.hom.left := hj
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  have hq' : RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range ((GroupScheme.baseChange p).map j)) q := by
    rw [heK, SubgroupFunctor.range_iso_comp]
    exact hq
  let : IsAffine ((GroupScheme.baseChange p).obj H).X.left := by
    change IsAffine (pullback H.X.hom p)
    infer_instance
  let : QuasiCompact q.hom.hom.left := inferInstance
  obtain ⟨V, r, hV, hr, eV, heV⟩ := exists_affine_fppfQuotient p j Q q hq'
  have hnormal : (SubgroupFunctor.range j).IsNormal := by
    rw [← hr.2.2.2]
    intro T g x _ hx
    rw [mem_range_kernelι_iff] at hx ⊢
    rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, hx,
      mul_one, mul_inv_cancel]
  exact ⟨⟨K, V, j, r, hK, hV, hj,
    smooth_of_baseChange_iso p K N eK hN,
    smooth_of_baseChange_iso p V Q eV hQ,
    hnormal, hr, eK, heK, eV, heV⟩⟩

/-- Choose the constructed filtration-step descent from overlap invariance;
no effective descent solution is supplied as a premise. -/
def filtrationStepDescentOfOverlap
    (hi : IsClosedSubgroup i) (hN : Smooth N.X.hom) (hQ : Smooth Q.X.hom)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    (h : SubgroupFunctor.range
        ((GroupScheme.baseChange (fst p)).map i ≫ (canonicalOverlap p H).hom) =
      SubgroupFunctor.range ((GroupScheme.baseChange (snd p)).map i)) :
    FiltrationStepDescentData p i q :=
  Classical.choice (nonempty_filtrationStepDescentData p i q hi hN hQ hq h)

omit [IsAffine B] [IsAffine S] [Flat p] [Surjective p]
    [IsAffine H.X.left] [IsAffine Q.X.left] in
/-- A descended step extends a series once its quotient has actual vector-bundle
charts and its kernel has the remaining series. -/
theorem FiltrationStepDescentData.hasVectorBundleSeries
    (D : FiltrationStepDescentData p i q) {n : ℕ}
    (hV : IsVectorBundleAdditive D.quotient) (hK : HasVectorBundleSeries n D.kernel) :
    HasVectorBundleSeries (n + 1) H :=
  ⟨D.kernel, D.quotient, D.inclusion, D.projection, D.isClosed, D.kernel_smooth,
    D.isNormal, D.isFppfQuotient, hV, hK⟩

end Langlands.GroupScheme.RelativeUnipotent
