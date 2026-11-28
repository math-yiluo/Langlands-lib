import Langlands.GroupScheme.CocycleDescent
import Langlands.GroupScheme.CocycleBaseChangeTriviality
import Langlands.GroupScheme.Rational.NumberFieldHasseInflation
import Langlands.GroupScheme.Rational.NumberFieldHasseKernelReduction
import Langlands.GroupScheme.Rational.CentralTensorDefectShapiro
import Langlands.GroupScheme.Rational.NumberFieldInnerTypeAHasseReduction

/-! # Relative cocycle descent with local triviality -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Cocycle

set_option backward.isDefEq.respectTransparency false

variable {S : Scheme.{u}} {G : GroupScheme S} {U V : Over S}

private theorem isTrivial_baseChangePullback_refine (ξ : Cocycle G U) (r : V ⟶ U)
    {S' : Scheme.{u}} (b : S' ⟶ S) (h : (ξ.baseChangePullback b).IsTrivial) :
    ((ξ.refine r).baseChangePullback b).IsTrivial := by
  obtain ⟨g, hg⟩ := h.refine ((Over.pullback b).map r)
  refine ⟨g, fun a c => ?_⟩
  rw [show ((ξ.refine r).baseChangePullback b).toFun a c = _ from
    baseChange_pullback_refine_toFun ξ r b a c]
  exact hg a c

/-- A cocycle that becomes trivial under a base change has an equivalent
representative on that base change viewed as a cover. -/
private theorem exists_cohomologous_refine_of_baseChangePullback
    {S' : Scheme.{u}} (b : S' ⟶ S) (ξ : Cocycle G U)
    [QuasiCompact U.hom] [Flat U.hom] [Surjective U.hom]
    (h : (ξ.baseChangePullback b).IsTrivial) :
    ∃ ν : Cocycle G (Over.mk b),
      (ξ.refine (fst U (Over.mk b))).Cohomologous (ν.refine (snd U (Over.mk b))) := by
  let W := Over.mk b
  let Y := (Over.pullback b).obj U
  let r := (Over.mapPullbackAdj b).counit.app U
  let s : (Over.map b).obj Y ⟶ W := Over.homMk Y.hom
  let : QuasiCompact s.left := inferInstanceAs (QuasiCompact (pullback.snd U.hom b))
  let : Flat s.left := inferInstanceAs (Flat (pullback.snd U.hom b))
  let : Surjective s.left := inferInstanceAs (Surjective (pullback.snd U.hom b))
  obtain ⟨f, hf⟩ := ξ.exists_of_baseChange_isTrivial b Y r h
  obtain ⟨g, hg⟩ := ξ.exists_isTrivialOver r s f (fun a c hac =>
    hf a c (congrArg (fun t => t.left) hac))
  let p := fst U W
  let q := snd U W
  let : QuasiCompact q.left := inferInstanceAs (QuasiCompact (pullback.snd U.hom b))
  let : Flat q.left := inferInstanceAs (Flat (pullback.snd U.hom b))
  let : Surjective q.left := inferInstanceAs (Surjective (pullback.snd U.hom b))
  let ζ := (ξ.refine p).twist g
  obtain ⟨ν, hν⟩ := ζ.exists_refine_eq_of_comp_eq q (fun a c hac => by
    change (a ≫ g)⁻¹ * ξ.toFun (a ≫ p) (c ≫ p) * (c ≫ g) = 1
    rw [hg a c hac]
    group)
  exact ⟨ν, g, fun a c => hν a c⟩

/-- Over a number field, the cocycle representative on the new cover
retains local triviality at every completion. Its triviality also implies
triviality on the original cover. -/
theorem exists_locallyTrivial_of_baseChangePullback
    {F : Type u} [Field F] [NumberField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} {U : Over (Spec (CommRingCat.of F))}
    [QuasiCompact U.hom] [Flat U.hom] [Surjective U.hom]
    {S' : Scheme.{u}} (b : S' ⟶ Spec (CommRingCat.of F))
    [QuasiCompact b] [Flat b] [Surjective b]
    (ξ : Cocycle G U) (hξ : ξ.LocallyTrivial) (h : (ξ.baseChangePullback b).IsTrivial) :
    ∃ ν : Cocycle G (Over.mk b), ν.LocallyTrivial ∧ (ν.IsTrivial → ξ.IsTrivial) := by
  let W := Over.mk b
  let p := fst U W
  let q := snd U W
  let : QuasiCompact p.left := inferInstanceAs (QuasiCompact (pullback.fst U.hom b))
  let : Flat p.left := inferInstanceAs (Flat (pullback.fst U.hom b))
  let : Surjective p.left := inferInstanceAs (Surjective (pullback.fst U.hom b))
  let : QuasiCompact (U ⊗ W).hom := by
    change QuasiCompact (pullback.fst U.hom b ≫ U.hom)
    infer_instance
  let : Flat (U ⊗ W).hom := by
    change Flat (pullback.fst U.hom b ≫ U.hom)
    infer_instance
  let : Surjective (U ⊗ W).hom := by
    change Surjective (pullback.fst U.hom b ≫ U.hom)
    infer_instance
  obtain ⟨ν, hcomp⟩ := exists_cohomologous_refine_of_baseChangePullback b ξ h
  have hcomp : (ξ.refine p).Cohomologous (ν.refine q) := hcomp
  refine ⟨ν, ?_, fun ht => (isTrivial_refine_iff ξ p).mp
    (IsTrivial.of_cohomologous hcomp.symm (ht.refine q))⟩
  intro v
  let c := algebraBaseMap F (Global.placeCompletion F v)
  let R := (Over.pullback c).obj (U ⊗ W)
  let qv : R ⟶ (Over.pullback c).obj W := (Over.pullback c).map q
  let : QuasiCompact R.hom := inferInstanceAs (QuasiCompact (pullback.snd (U ⊗ W).hom c))
  let : Flat R.hom := inferInstanceAs (Flat (pullback.snd (U ⊗ W).hom c))
  let : Surjective R.hom := inferInstanceAs (Surjective (pullback.snd (U ⊗ W).hom c))
  have hv := isTrivial_baseChangePullback_refine ξ p c (hξ v)
  obtain ⟨f, hf⟩ := IsTrivial.of_cohomologous
    (hcomp.baseChange c R ((Over.mapPullbackAdj c).counit.app (U ⊗ W))) hv
  apply IsTrivial.of_refine_fpqcCover qv
  refine ⟨f, fun a d => ?_⟩
  rw [← baseChange_pullback_refine_toFun ν q c a d]
  exact hf a d

section FieldExtension

variable {F L K : Type u} [Field F] [NumberField F] [Field L] [Algebra F L]
  [FiniteDimensional F L] [Field K] [NumberField K] [Algebra F K]
  {G : GroupScheme (Spec (CommRingCat.of F))}

/-- A kernel result over an extension can be applied to a common field
refinement of the pulled-back cover, and reflects to the full pullback. -/
theorem isTrivial_baseChangePullback_of_numberFieldKernel
    (ξ : Cocycle G (GaloisCocycle.cover F L)) (hξ : ξ.LocallyTrivial)
    (h : ∀ (M : Type u) [Field M] [Algebra K M] [FiniteDimensional K M] [IsGalois K M],
      ∀ δ : Cocycle ((GroupScheme.baseChange (algebraBaseMap F K)).obj G)
        (GaloisCocycle.cover K M), δ.LocallyTrivial → δ.IsTrivial) :
    (ξ.baseChangePullback (algebraBaseMap F K)).IsTrivial := by
  obtain ⟨M, _, _, _, _, _, _, _, _⟩ := CentralSimpleUnits.exists_finiteGalois_over_baseChange F K L
  let δ := GaloisCocycle.scalarExtension (K := K) (M := M) ξ
  have hd : δ.LocallyTrivial := hξ.numberFieldBaseChange.refine GaloisCocycle.pullbackCoverPoint
  exact GaloisCocycle.isTrivial_baseChange_of_scalarExtension ξ (h M δ hd)

end FieldExtension

end Langlands.GroupScheme.Cocycle
