import Langlands.Representation.Aubert.BundledJacquetQuotientDiagram
import Langlands.Representation.Aubert.BooleanIntervalComplex
import Langlands.Representation.Aubert.CorrectedWholeTargetEvaluation

/-! Signed assembly of the actual whole-target common coefficient comparisons. -/

noncomputable section

namespace Langlands.Aubert.CutComplex.BooleanInterval

universe uI uM uN

variable {ι : Type uI} [LinearOrder ι]
  (D : Diagram.{uI,uM} ι) (lower upper : Finset ι)
  (M : Type uN) [AddCommGroup M] [Module ℂ M]
  (e : ∀ s, Active lower upper s → D.Obj s ≃ₗ[ℂ] M)
  (hzero : ∀ s, ¬ Active lower upper s → Subsingleton (D.Obj s))

/-- Extend the actual active-coordinate equivalences by the unique equivalence
between zero modules off the interval. -/
def coordinateEquiv (s : Finset ι) :
    D.Obj s ≃ₗ[ℂ] (diagram lower upper M).Obj s := by
  classical
  by_cases hs : Active lower upper s
  · exact {
      toFun x _ := e s hs x
      invFun f := (e s hs).symm (f ⟨hs⟩)
      left_inv x := (e s hs).symm_apply_apply x
      right_inv f := by
        funext hp
        exact (e s hs).apply_symm_apply (f hp)
      map_add' x y := by
        funext hp
        exact map_add (e s hs) x y
      map_smul' a x := by
        funext hp
        exact map_smul (e s hs) a x }
  · letI := hzero s hs
    letI : IsEmpty (PLift (Active lower upper s)) := ⟨fun hp => hs hp.down⟩
    letI : Subsingleton ((diagram lower upper M).Obj s) := by
      change Subsingleton (PLift (Active lower upper s) → M)
      infer_instance
    exact LinearEquiv.ofSubsingleton _ _

theorem coordinateEquiv_apply (s : Finset ι) (hs : Active lower upper s)
    (x : D.Obj s) (hp : PLift (Active lower upper s)) :
    coordinateEquiv D lower upper M e hzero s x hp = e s hs x := by
  simp only [coordinateEquiv, dite_eq_left hs]
  rfl

/-- Constant actual maps on the interval give an equivalence of signed diagrams. -/
def equivalence
    (hnatural : ∀ {s t} (hst : s ⊆ t) (hs : Active lower upper s)
      (ht : Active lower upper t) (x : D.Obj s), e t ht (D.map hst x) = e s hs x) :
    Diagram.Equivalence D (diagram lower upper M) where
  obj := coordinateEquiv D lower upper M e hzero
  natural {s t} hst x := by
    classical
    funext ht
    change coordinateEquiv D lower upper M e hzero t (D.map hst x) ht =
      if hs : Active lower upper s then
        coordinateEquiv D lower upper M e hzero s x ⟨hs⟩ else 0
    by_cases hs : Active lower upper s
    · rw [dite_eq_left hs, coordinateEquiv_apply, coordinateEquiv_apply]
      exact hnatural hst hs ht.down x
    · rw [dite_eq_right hs]
      have hx : x = 0 := (hzero s hs).elim _ _
      rw [hx, map_zero, map_zero]
      rfl

end Langlands.Aubert.CutComplex.BooleanInterval

namespace Langlands.Aubert.ActualCutComplex

open GeneralLinear Geometric

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ}
  (A : letI := T.topology
    SmoothRep.{0,uF,uV} ℂ (GeneralLinear n F.Carrier))
  (C : BlockShape n) (θ : Set (Equiv.Perm (Fin n))) (w : Equiv.Perm (Fin n))
  (lower upper : Finset (Fin (n - 1))) (Q : BlockShape n)

/-- The actual geometric data needed to identify a support grade with a
constant coefficient interval. Each active coordinate retains its actual
intersection refinement; inactive coordinates are required to vanish. -/
structure WholeTargetIntervalData where
  support : ∀ s, CutComplex.BooleanInterval.Active lower upper s →
    w ∈ Support.weylSupport (shape s) C θ
  increasing : ∀ s, CutComplex.BooleanInterval.Active lower upper s →
    TypeASolomon.SourceIncreasing (shape s) w
  refinement : ∀ s, CutComplex.BooleanInterval.Active lower upper s →
    BlockRefinement (shape s)
  isIntersection : ∀ s hs,
    IsIntersectionRefinement (F := F.Carrier) (shape s) C w (refinement s hs)
  flatten_eq : ∀ s hs, (shape s).flatten (refinement s hs) = Q
  whole : ∀ s, CutComplex.BooleanInterval.Active lower upper s →
    blockWeyl C ⊓ (blockWeyl (shape s)).comap (MulAut.conj w⁻¹).toMonoidHom = blockWeyl C
  zero : ∀ s, ¬ CutComplex.BooleanInterval.Active lower upper s →
    Subsingleton ((bundledSupportQuotientDiagram T A C (θ \ {w}) θ).Obj s)

variable
  (hθ : ∀ v ∈ θ, ∀ z, Support.inversionLength v < Support.inversionLength z → z ∈ θ)
  (hLower : ∀ v ∈ θ \ {w}, ∀ z,
    Support.inversionLength v < Support.inversionLength z → z ∈ θ \ {w})
  (data : WholeTargetIntervalData T A C θ w lower upper Q)

/-- Assemble the actual whole-target graded comparison on the active cuts.
The coefficient is the same actual flattened Jacquet quotient at every cut. -/
def wholeTargetIntervalEquivalence :
    CutComplex.Diagram.Equivalence
      (bundledSupportQuotientDiagram T A C (θ \ {w}) θ)
      (CutComplex.BooleanInterval.diagram lower upper (Q.JacquetModule A.obj.ρ)) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := T.fieldT2
  letI := T.generalLinearLocallyCompactSpace n
  let e := fun s hs => Support.correctedWholeTargetCommonEquiv T A (shape s) C w θ
    hθ hLower (data.support s hs) (data.increasing s hs)
    Q (data.refinement s hs) (data.isIntersection s hs) (data.flatten_eq s hs)
    (data.whole s hs)
  apply CutComplex.BooleanInterval.equivalence
    (bundledSupportQuotientDiagram T A C (θ \ {w}) θ) lower upper
    (Q.JacquetModule A.obj.ρ) e data.zero
  intro s t hst hs ht x
  change e t ht
    ((Support.cutSupportQuotientMap T A C (B := shape s) (D := shape t)
      (by simpa using hst) (θ \ {w}) θ).hom x) = e s hs x
  exact Support.correctedWholeTargetCommonEquiv_cutMap T A (shape s) C w θ
    hθ hLower (data.support s hs) (data.increasing s hs)
    Q (data.refinement s hs) (data.isIntersection s hs) (data.flatten_eq s hs)
    (data.whole s hs) (shape t) (data.refinement t ht) (data.isIntersection t ht)
    (data.flatten_eq t ht) (by simpa using hst) (data.increasing t ht) (data.whole t ht) x

/-- The signed homogeneous geometric comparison with the common coefficient. -/
def wholeTargetIntervalDegreeEquiv (k : ℕ) :
    (bundledSupportQuotientDiagram T A C (θ \ {w}) θ).Degree k ≃ₗ[ℂ]
      (CutComplex.BooleanInterval.diagram lower upper (Q.JacquetModule A.obj.ρ)).Degree k :=
  (wholeTargetIntervalEquivalence T A C θ w lower upper Q hθ hLower data).degreeEquiv k

/-- Every exterior insertion sign is retained in the actual geometric square. -/
theorem wholeTargetIntervalDegreeEquiv_differential (k : ℕ)
    (x : (bundledSupportQuotientDiagram T A C (θ \ {w}) θ).Degree k) :
    wholeTargetIntervalDegreeEquiv T A C θ w lower upper Q hθ hLower data (k + 1)
        ((bundledSupportQuotientDiagram T A C (θ \ {w}) θ).degreeDifferential k x) =
      (CutComplex.BooleanInterval.diagram lower upper (Q.JacquetModule A.obj.ρ)).degreeDifferential k
        (wholeTargetIntervalDegreeEquiv T A C θ w lower upper Q hθ hLower data k x) :=
  (wholeTargetIntervalEquivalence T A C θ w lower upper Q hθ hLower data).degreeEquiv_differential k x

end Langlands.Aubert.ActualCutComplex
