import Langlands.GroupScheme.AutomorphicAction.LocallyInnerTransport
import Langlands.GroupScheme.LocalGroupIsoBaseChangeEquivalence

/-! # Fppf reflection of local innerness -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

variable {S S' : Scheme.{u}} {G H : GroupScheme S}

/-- Local innerness after an fppf base change is local innerness on the base. -/
theorem IsFppfLocallyInner.of_baseChange {σ : G ≅ G}
    (b : S' ⟶ S) [Flat b] [Surjective b] [LocallyOfFinitePresentation b]
    (hσ : IsFppfLocallyInner ((GroupScheme.baseChange b).mapIso σ)) :
    IsFppfLocallyInner σ := by
  obtain ⟨V, hf, hs, hl, x, hx⟩ := hσ
  let : Flat V.hom := hf
  let : Surjective V.hom := hs
  let : LocallyOfFinitePresentation V.hom := hl
  let U : Over S := (Over.map b).obj V
  let y : U ⟶ G.X := baseChangePointsEquiv b G V x
  refine ⟨U, ?_, ?_, ?_, y, ?_⟩
  · change Flat (V.hom ≫ b)
    infer_instance
  · change Surjective (V.hom ≫ b)
    infer_instance
  · change LocallyOfFinitePresentation (V.hom ≫ b)
    infer_instance
  · intro W t g
    let a : W ⟶ Over.mk b := Over.homMk (t.left ≫ V.hom) (by
      change (t.left ≫ V.hom) ≫ b = W.hom
      simpa only [Category.assoc] using
        (show t.left ≫ (V.hom ≫ b) = W.hom from t.w))
    let r : LocalGroupIso.coverTest a ⟶ V := Over.homMk t.left rfl
    let z := (LocalGroupIso.coverPointsEquiv G a).symm g
    have he := congrArg (LocalGroupIso.coverPointsEquiv G a) (hx r z)
    simp only [AutomorphicAction.conjugation_act, Grp.id_hom_hom,
      Category.comp_id] at he ⊢
    rw [map_mul, map_mul, map_inv] at he
    change _ = LocalGroupIso.coverPointsEquiv G a
      (z ≫ ((GroupScheme.baseChange b).map σ.hom).hom.hom) at he
    have hc := LocalGroupIso.coverPointsEquiv_comp σ.hom a z
    change LocalGroupIso.coverPointsEquiv G a
      (z ≫ ((GroupScheme.baseChange b).map σ.hom).hom.hom) =
        LocalGroupIso.coverPointsEquiv G a z ≫ σ.hom.hom.hom at hc
    rw [hc] at he
    have hz : LocalGroupIso.coverPointsEquiv G a z = g :=
      (LocalGroupIso.coverPointsEquiv G a).apply_symm_apply g
    rw [hz] at he
    have hy : LocalGroupIso.coverPointsEquiv G a (r ≫ x) = t ≫ y := by
      apply Over.OverMorphism.ext
      change (t.left ≫ x.left) ≫ CategoryTheory.Limits.pullback.fst G.X.hom b =
        t.left ≫ (x.left ≫ CategoryTheory.Limits.pullback.fst G.X.hom b)
      exact Category.assoc _ _ _
    rw [hy] at he
    exact he

/-- An fppf cover detects the local-inner predicate. -/
theorem isFppfLocallyInner_baseChange_iff {σ : G ≅ G}
    (b : S' ⟶ S) [Flat b] [Surjective b] [LocallyOfFinitePresentation b] :
    IsFppfLocallyInner ((GroupScheme.baseChange b).mapIso σ) ↔
      IsFppfLocallyInner σ :=
  ⟨IsFppfLocallyInner.of_baseChange b, fun h => h.baseChange b⟩

/-- An fppf base change detects inner equivalence of actual comparisons. -/
theorem IsFppfInnerEquivalent.of_baseChange {e d : G ≅ H}
    (b : S' ⟶ S) [Flat b] [Surjective b] [LocallyOfFinitePresentation b]
    (h : IsFppfInnerEquivalent ((GroupScheme.baseChange b).mapIso e)
      ((GroupScheme.baseChange b).mapIso d)) : IsFppfInnerEquivalent e d := by
  apply IsFppfLocallyInner.of_baseChange b
  simpa only [IsFppfInnerEquivalent, Functor.mapIso_trans, Functor.mapIso_symm] using h

/-- Inner equivalence is an fppf-local property on the base. -/
theorem isFppfInnerEquivalent_baseChange_iff {e d : G ≅ H}
    (b : S' ⟶ S) [Flat b] [Surjective b] [LocallyOfFinitePresentation b] :
    IsFppfInnerEquivalent ((GroupScheme.baseChange b).mapIso e)
      ((GroupScheme.baseChange b).mapIso d) ↔ IsFppfInnerEquivalent e d :=
  ⟨IsFppfInnerEquivalent.of_baseChange b, fun h => h.baseChange b⟩

/-- Actual comparisons modulo fppf-local inner discrepancy. -/
def fppfInnerComparisonSetoid (G H : GroupScheme S) : Setoid (G ≅ H) where
  r := IsFppfInnerEquivalent
  iseqv := ⟨IsFppfInnerEquivalent.refl, IsFppfInnerEquivalent.symm,
    IsFppfInnerEquivalent.trans⟩

/-- The type of fppf-local-inner classes of actual comparisons. -/
def FppfInnerComparisonClass (G H : GroupScheme S) :=
  Quotient (fppfInnerComparisonSetoid G H)

namespace FppfInnerComparisonClass

/-- Arbitrary base change acts on local-inner classes of comparisons. -/
def baseChange (b : S' ⟶ S) :
    FppfInnerComparisonClass G H →
      FppfInnerComparisonClass ((GroupScheme.baseChange b).obj G)
        ((GroupScheme.baseChange b).obj H) :=
  Quotient.map ((GroupScheme.baseChange b).mapIso)
    (fun _ _ h => h.baseChange b)

/-- Classes of comparisons are separated for a single fppf cover. -/
theorem baseChange_injective (b : S' ⟶ S)
    [Flat b] [Surjective b] [LocallyOfFinitePresentation b] :
    Function.Injective (baseChange (G := G) (H := H) b) := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro e d h
  apply Quotient.sound
  exact IsFppfInnerEquivalent.of_baseChange b (Quotient.exact h)

end FppfInnerComparisonClass

end Langlands.GroupScheme
