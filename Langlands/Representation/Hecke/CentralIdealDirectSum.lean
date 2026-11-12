import Langlands.Representation.Hecke.CentralIdempotentIdeal
import Langlands.Representation.Category.DecompositionCentralProjectors
import Mathlib.Algebra.DirectSum.Basic

/-! # Internal direct sum of the Hecke ideals of central projectors -/

noncomputable section

open CategoryTheory MeasureTheory
open scoped DirectSum

namespace Langlands.Hecke

universe u v w

variable {G : Type u} [Group G] [TopologicalSpace G] [T2Space G]
  [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
  (hl : IsSmooth (HarmonicAnalysis.GroupAction.leftTests (G := G)))
  {I : Type w} [DecidableEq I]
  (z : I → CatCenter (SmoothRep.{0,u,max u v} ℂ G))

omit [T2Space G] [LocallyCompactSpace G] [DecidableEq I] in
/-- Finite vectorwise reconstruction on the regular object transfers to the Hecke algebra. -/
theorem centralMultiplier_finite_sum
    (hsum : ∀ (V : SmoothRep.{0,u,max u v} ℂ G) (x : V),
      (Function.support fun i => SmoothRep.hom ((z i).app V) x).Finite ∧
        ∑ᶠ i, SmoothRep.hom ((z i).app V) x = x)
    (a : HeckeAlgebra μ) :
    (Function.support fun i => centralMultiplier μ hl (z i) a).Finite ∧
      ∑ᶠ i, centralMultiplier μ hl (z i) a = a := by
  classical
  let E : HeckeAlgebra μ ≃ₗ[ℂ] regularLift.{u,v} hl :=
    (HeckeAlgebra.toTestFunction μ).trans ULift.moduleEquiv.symm
  have hE (i : I) : E (centralMultiplier μ hl (z i) a) =
      SmoothRep.hom ((z i).app (regularLift.{u,v} hl)) (E a) := rfl
  obtain ⟨hs, hv⟩ := hsum (regularLift.{u,v} hl) (E a)
  have hs' : (Function.support fun i => centralMultiplier μ hl (z i) a).Finite := by
    apply hs.subset
    intro i hi
    change SmoothRep.hom ((z i).app (regularLift.{u,v} hl)) (E a) ≠ 0
    rw [← hE]
    exact fun h => hi (E.injective (h.trans (map_zero E).symm))
  refine ⟨hs', E.injective ?_⟩
  calc
    E (∑ᶠ i, centralMultiplier μ hl (z i) a) =
        ∑ᶠ i, E (centralMultiplier μ hl (z i) a) :=
      E.toAddMonoidHom.map_finsum hs'
    _ = E a := by simpa only [hE] using hv

/-- Orthogonal idempotent central multipliers with finite reconstruction give an internal sum. -/
theorem centralIdeals_isInternal
    (hz : ∀ i, IsIdempotentElem (z i))
    (horth : ∀ i j, i ≠ j → z i * z j = 0)
    (hsum : ∀ a : HeckeAlgebra μ,
      (Function.support fun i => centralMultiplier μ hl (z i) a).Finite ∧
        ∑ᶠ i, centralMultiplier μ hl (z i) a = a) :
    DirectSum.IsInternal fun i => (centralIdeal μ hl (z i)).toAddSubgroup := by
  classical
  let S := fun i => (centralIdeal μ hl (z i)).toAddSubgroup
  have hcoord (i : I) (x : ⨁ j, S j) :
      centralMultiplier μ hl (z i) (DirectSum.coeAddMonoidHom S x) = (x i : HeckeAlgebra μ) := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of j a =>
      rw [DirectSum.coeAddMonoidHom_of]
      by_cases hij : i = j
      · subst j
        rw [DirectSum.of_eq_same]
        exact a.property
      · rw [DirectSum.of_eq_of_ne _ _ _ hij]
        change centralMultiplier μ hl (z i) (a : HeckeAlgebra μ) = 0
        calc
          centralMultiplier μ hl (z i) (a : HeckeAlgebra μ) =
              centralMultiplier μ hl (z i) (centralMultiplier μ hl (z j) a) :=
            congrArg (centralMultiplier μ hl (z i)) a.property.symm
          _ = 0 := by rw [← centralMultiplier_mul, horth i j hij, centralMultiplier_zero]
    | add a b ha hb =>
      simp only [map_add, ha, hb, DirectSum.add_apply]
      rfl
  constructor
  · intro x y h
    apply DirectSum.ext
    intro i
    apply Subtype.ext
    rw [← hcoord i x, ← hcoord i y, h]
  · intro a
    obtain ⟨hs, ha⟩ := hsum a
    let f (i : I) : S i :=
      ⟨centralMultiplier μ hl (z i) a, centralMultiplier_idempotent μ hl (z i) (hz i) a⟩
    have hof (i : I) :
        DirectSum.coeAddMonoidHom S (DirectSum.of (fun j => S j) i (f i)) =
          centralMultiplier μ hl (z i) a :=
      DirectSum.coeAddMonoidHom_of S i (f i)
    refine ⟨∑ i ∈ hs.toFinset, DirectSum.of (fun j => S j) i (f i), ?_⟩
    change DirectSum.coeAddMonoidHom S _ = a
    simp only [map_sum, hof]
    rw [← finsum_eq_sum_of_support_subset _ (by simp)]
    exact ha

/-- The canonical additive equivalence from the external central-ideal sum to the Hecke algebra. -/
def centralIdealsAddEquiv
    (hz : ∀ i, IsIdempotentElem (z i))
    (horth : ∀ i j, i ≠ j → z i * z j = 0)
    (hsum : ∀ a : HeckeAlgebra μ,
      (Function.support fun i => centralMultiplier μ hl (z i) a).Finite ∧
        ∑ᶠ i, centralMultiplier μ hl (z i) a = a) :
    (⨁ i, (centralIdeal μ hl (z i)).toAddSubgroup) ≃+ HeckeAlgebra μ :=
  AddEquiv.ofBijective
    (DirectSum.coeAddMonoidHom (fun i => (centralIdeal μ hl (z i)).toAddSubgroup))
    (centralIdeals_isInternal μ hl z hz horth hsum)

@[simp] theorem centralIdealsAddEquiv_apply
    (hz : ∀ i, IsIdempotentElem (z i))
    (horth : ∀ i j, i ≠ j → z i * z j = 0)
    (hsum : ∀ a : HeckeAlgebra μ,
      (Function.support fun i => centralMultiplier μ hl (z i) a).Finite ∧
        ∑ᶠ i, centralMultiplier μ hl (z i) a = a)
    (x : ⨁ i, (centralIdeal μ hl (z i)).toAddSubgroup) :
    centralIdealsAddEquiv μ hl z hz horth hsum x =
      DirectSum.coeAddMonoidHom (fun i => (centralIdeal μ hl (z i)).toAddSubgroup) x := rfl

/-- Applied to the canonical projectors of an actual smooth category decomposition. -/
theorem decomposition_centralIdeals_isInternal
    {P : I → ObjectProperty (SmoothRep.{0,u,max u v} ℂ G)}
    (hP : Renard.IsCategoryDecomposition P) :
    DirectSum.IsInternal fun i =>
      (centralIdeal μ hl (SmoothRep.centralProjector hP i)).toAddSubgroup := by
  apply centralIdeals_isInternal μ hl (SmoothRep.centralProjector hP)
    (SmoothRep.centralProjector_idempotent hP) (SmoothRep.centralProjector_mul_of_ne hP)
  exact centralMultiplier_finite_sum μ hl (SmoothRep.centralProjector hP)
    (SmoothRep.centralProjector_finite_sum hP)

end Langlands.Hecke
