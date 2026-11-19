import Langlands.GroupScheme.CocycleKernelTwist
import Langlands.GroupScheme.CocycleQuotientCorrection
import Langlands.GroupScheme.Rational.FiniteSeparableQuotientLifts
import Langlands.GroupScheme.Rational.NumberFieldHasseGaloisReduction

/-! # Kernel reduction for cocycles on finite separable covers -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory
open AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Cocycle

variable {k : Type u} [Field k] {G Q : GroupScheme (Spec (CommRingCat.of k))}

set_option backward.isDefEq.respectTransparency false in
private theorem exists_quotient_cochain_lift
    {L : Type u} [Field L] [Algebra k L] [FiniteDimensional k L] [Algebra.IsSeparable k L]
    (q : G ⟶ Q) [Smooth q.hom.hom.left] [Surjective q.hom.hom.left]
    (v : ringTest k L ⟶ Q.X) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra k E),
      FiniteDimensional k E ∧ Algebra.IsSeparable k E ∧
      ∃ (φ : L →ₐ[k] E) (g : ringTest k E ⟶ G.X),
        g ≫ q.hom.hom = ringTestMap k φ ≫ v := by
  let T : Over (Spec (CommRingCat.of L)) :=
    Over.mk (pullback.snd q.hom.hom.left v.left)
  let : Smooth T.hom := by
    change Smooth (pullback.snd q.hom.hom.left v.left)
    infer_instance
  let : Surjective T.hom := by
    change Surjective (pullback.snd q.hom.hom.left v.left)
    infer_instance
  let : Nonempty T.left := by
    obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of L)) := inferInstance
    obtain ⟨z, _⟩ := (inferInstance : Surjective T.hom).surj x
    exact ⟨z⟩
  obtain ⟨E, _, _, hfin, hsep, ⟨w⟩⟩ :=
    Langlands.AlgebraicGeometry.exists_finiteSeparable_point_of_smooth (F := L) T
  let : Algebra k E := ((algebraMap L E).comp (algebraMap k L)).toAlgebra
  let : IsScalarTower k L E := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional L E := hfin
  let : Algebra.IsSeparable L E := hsep
  let φ := IsScalarTower.toAlgHom k L E
  have hleft : w.left ≫ pullback.snd q.hom.hom.left v.left = (ringTestMap k φ).left :=
    Over.w w
  let g : ringTest k E ⟶ G.X := Over.homMk (w.left ≫ pullback.fst q.hom.hom.left v.left) (by
    rw [Category.assoc, ← Over.w q.hom.hom, pullback.condition_assoc,
      Over.w v, ← Category.assoc, hleft, Over.w (ringTestMap k φ)])
  refine ⟨E, inferInstance, inferInstance, FiniteDimensional.trans k L E,
    Algebra.IsSeparable.trans k L E, φ, g, ?_⟩
  apply Over.OverMorphism.ext
  change (w.left ≫ pullback.fst q.hom.hom.left v.left) ≫ q.hom.hom.left =
    (ringTestMap k φ).left ≫ v.left
  rw [Category.assoc, pullback.condition, ← Category.assoc, hleft]

/-- Triviality for all finite separable covers is detected by extension to `F`,
using the actual pullback of each cover. -/
def TrivialityReflectsFrom (G : GroupScheme (Spec (CommRingCat.of k)))
    (F : Type u) [Field F] [Algebra k F] : Prop :=
  ∀ (L : Type u) [Field L] [Algebra k L] [FiniteDimensional k L] [Algebra.IsSeparable k L]
    (ξ : Cocycle G (ringTest k L)),
    (ξ.baseChange (Spec.algebraMap k F) _
      ((Over.mapPullbackAdj (Spec.algebraMap k F)).counit.app (ringTest k L))).IsTrivial →
    ξ.IsTrivial

variable {F L : Type u} [Field F] [Algebra k F] [Field L] [Algebra k L]
    [FiniteDimensional k L] [Algebra.IsSeparable k L]

local notation "p" => Spec.algebraMap k F

/-- If every translate of the local group image contains a base quotient point
and the kernel detects triviality after scalar extension, a cocycle is trivial
once its quotient image and its scalar extension are both trivial. -/
theorem isTrivial_of_quotient_and_baseChange (q : G ⟶ Q)
    [Smooth q.hom.hom.left] [Surjective q.hom.hom.left]
    (hcoset : ∀ c : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶
        ((GroupScheme.baseChange p).obj Q).X,
      ∃ y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q.X,
        toUnit ((Over.map p).obj (Over.mk (𝟙 (Spec (CommRingCat.of F))))) ≫ y ∈
          quotientPointTranslate q p c)
    (hK : TrivialityReflectsFrom (kernel q) F)
    (ξ : Cocycle G (ringTest k L)) (hquot : (ξ.map q).IsTrivial)
    (hlocal : (ξ.baseChange p _
      ((Over.mapPullbackAdj p).counit.app (ringTest k L))).IsTrivial) :
    ξ.IsTrivial := by
  let U := ringTest k L
  let V := (Over.pullback p).obj U
  let r := (Over.mapPullbackAdj p).counit.app U
  let hp := fieldExtension_fpqc k L
  let : Surjective U.hom := hp.1
  let : Flat U.hom := hp.2.1
  let : QuasiCompact U.hom := hp.2.2
  let : EffectiveEpi V.hom := by
    change EffectiveEpi (pullback.snd U.hom p)
    infer_instance
  obtain ⟨v, f, hv, hf, hproj⟩ :=
    exists_compatible_quotient_trivializations q p r hcoset hquot hlocal
  obtain ⟨E, _, _, hfin, hsep, φ, g, hg⟩ := exists_quotient_cochain_lift q v
  let : FiniteDimensional k E := hfin
  let : Algebra.IsSeparable k E := hsep
  let s := ringTestMap k φ
  let U' := ringTest k E
  let V' := (Over.pullback p).obj U'
  let r' := (Over.mapPullbackAdj p).counit.app U'
  let s' := (Over.pullback p).map s
  let f' := s' ≫ f
  let qF := (GroupScheme.baseChange p).map q
  have hs : (Over.map p).map s' ≫ r = r' ≫ s :=
    (Over.mapPullbackAdj p).counit.naturality s
  have hquot' {Z : Over (Spec (CommRingCat.of k))} (a b : Z ⟶ U') :
      ((ξ.refine s).map q).toFun a b = (coboundary (g ≫ q.hom.hom)).toFun a b := by
    rw [hg]
    simpa only [map, refine_toFun, coboundary, Category.assoc, s] using hv (a ≫ s) (b ≫ s)
  have hf' {Z : Over (Spec (CommRingCat.of F))} (a b : Z ⟶ V') :
      ((ξ.refine s).baseChange p V' r').toFun a b = (coboundary f').toFun a b := by
    rw [baseChange_pullback_refine_toFun]
    simpa only [refine_toFun, coboundary, Category.assoc, f'] using hf (a ≫ s') (b ≫ s')
  have hproj' :
      baseChangePointsEquiv p Q V' (f' ≫ qF.hom.hom) = r' ≫ g ≫ q.hom.hom := by
    dsimp only [f', qF]
    rw [Category.assoc, baseChangePointsEquiv_naturality, hproj, ← Category.assoc, hs,
      Category.assoc, hg]
  have hbase := isTrivial_kernelTwist_baseChange (ξ.refine s) q g hquot' p V' r' f' hf' hproj'
  have h := isTrivial_of_kernelTwist (ξ.refine s) q g hquot'
    (hK E (kernelTwist (ξ.refine s) q g hquot') hbase)
  let : Algebra L E := φ.toRingHom.toAlgebra
  obtain ⟨hs₁, hs₂, hs₃⟩ := fieldExtension_fpqc L E
  let : Surjective s.left := hs₁
  let : Flat s.left := hs₂
  let : QuasiCompact s.left := hs₃
  exact (isTrivial_refine_iff ξ s).mp h

end Langlands.GroupScheme.Cocycle
