import Langlands.GroupScheme.Derived.SemisimplePerfectStatement
import Langlands.GroupScheme.Derived.BaseChangeElementary
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.GroupScheme.Absolute.AlgebraicClosureBaseChange
import Langlands.GroupScheme.Reductive.FiniteCenterBaseChange

/-! # Descent and algebraic-closure reduction for perfectness -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Perfectness of the full derived subgroup functor descends along an fpqc
base change, without a representability hypothesis. -/
theorem derivedSubgroup_eq_top_of_baseChange
    {S S' : Scheme.{u}} (b : S' ⟶ S)
    [QuasiCompact b] [Flat b] [Surjective b] (G : GroupScheme S)
    (h : derivedSubgroup ((GroupScheme.baseChange b).obj G) = ⊤) :
    derivedSubgroup G = ⊤ := by
  apply SubgroupFunctor.ext
  intro T
  change (derivedSubgroup G).carrier T = ⊤
  apply top_unique
  intro x hx H i hi hcomm
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  have hbound : (⊤ : SubgroupFunctor ((GroupScheme.baseChange b).obj G)) ≤
      (derivedSubgroup G).baseChange b := by
    rw [← h]
    exact derivedSubgroup_baseChange_le b
  have hiBound := hbound.trans
    (SubgroupFunctor.baseChange_mono b (derivedSubgroup_le_range i hi hcomm))
  apply SubgroupFunctor.le_range_of_baseChange_le b
    (F := (⊤ : SubgroupFunctor G)) i ?_ T hx
  simpa only [SubgroupFunctor.top_baseChange] using hiBound

/-- Perfectness descends along an arbitrary extension of fields. -/
theorem derivedSubgroup_eq_top_of_fieldExtension
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    (h : derivedSubgroup
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G) = ⊤) :
    derivedSubgroup G = ⊤ := by
  obtain ⟨hSurj, hFlat, hQc⟩ := fieldExtension_fpqc k K
  let := hSurj
  let := hFlat
  let := hQc
  exact derivedSubgroup_eq_top_of_baseChange _ G h

/-- Semisimplicity is preserved by extension to an algebraic closure. -/
theorem IsSemisimple.baseChange_toAlgebraicClosure
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsSemisimple G) :
    IsSemisimple ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G) :=
  ⟨hG.isConnectedReductive.baseChange_toAlgebraicClosure,
    hG.hasFiniteCenter.baseChange _⟩

/-- The remaining perfectness obligation over algebraically closed fields.
This is a proposition, not an assumed structural theorem. -/
def AlgebraicallyClosedSemisimplePerfectStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k))),
    IsSemisimple G → derivedSubgroup G = ⊤

/-- The algebraically closed case implies the full arbitrary-field statement. -/
theorem semisimplePerfect_of_algebraicallyClosed
    (h : AlgebraicallyClosedSemisimplePerfectStatement.{u}) :
    SemisimplePerfectStatement.{u} := by
  intro k _ G hG
  apply derivedSubgroup_eq_top_of_fieldExtension k (AlgebraicClosure k) G
  exact h (AlgebraicClosure k) _
    hG.baseChange_toAlgebraicClosure

end Langlands.GroupScheme
