import Langlands.AllFieldBZ.Representation.Induction.ProductDualReversalProof
import Langlands.AllFieldBZ.Representation.Classification.IrreducibleProductFiniteLengthProof
import Langlands.Representation.Classification.TwoFactorProductConstituentCommutativityProof

/-! Actual constituent matching after reversing an all-field normalized product. -/

noncomputable section

set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Aubert.LocalFieldGraded

open GeneralLinear
open AllFieldBZ.LocalFieldPackage.TopologicalData
open AllFieldBZ.Parabolic (nonempty_inverseTranspose_contragredient productDualReversal)
open Classification.TwoFactorCommutativity

universe uF uV

variable {K : AllFieldBZ.LocalFieldPackage.{uF}} (T : K.TopologicalData)

private theorem admissible_of_irreducible {n : ℕ} :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n K.Carrier)),
      A.IsIrreducible → A.IsAdmissible :=
  fun A hA => (AllFieldBZ.CuspidalSupport.cuspidalEmbedding K T n A hA).1

private theorem sameFactors_dual_inverseTranspose {n : ℕ} (hn : 0 < n)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear n K.Carrier) V) :
    letI := T.topology
    IsSmooth ρ → ∀ {m : ℕ} (s : ObjectRepFiltration (Rep.of ρ) m), s.HasSimpleFactors →
    letI := T.generalLinearTopologicalGroup n
    HaveSameJordanHolderFactors (Rep.of (smoothContragredient ρ))
      (Rep.of (ρ.comp (inverseTranspose n K.Carrier).toMonoidHom)) := by
  let := T.topology
  intro hρ m s hs
  let := T.generalLinearTopologicalGroup n
  let θ := (inverseTranspose n K.Carrier).toMonoidHom
  have hθ : Function.Surjective θ := (inverseTranspose n K.Carrier).surjective
  have hcof := GeneralLinear.compactOpen_cofinal_allFieldBZ K T n
  have hdual (j : Fin m) : Nonempty (((dualSeries s).gradedRepresentation j).ρ.Equiv
      ((s.gradedRepresentation j.rev).ρ.comp θ)) := by
    obtain ⟨a⟩ := dualSeries_graded hcof hρ s j
    let X := s.gradedRepresentation j.rev
    have hsm : IsSmooth X.ρ :=
      isSmooth_quotientRep hρ (s.subrepresentation j.rev.castSucc) (s.subrepresentation j.rev.succ)
    obtain ⟨b⟩ := nonempty_inverseTranspose_contragredient T hn X.ρ
      (admissible_of_irreducible T (SmoothRep.of X.ρ hsm) (hs j.rev)) (hs j.rev)
    exact ⟨a.trans b.symm⟩
  refine ⟨m, dualSeries s, s.comp θ, fun j => ?_, fun j => ?_, Fin.revPerm, fun j => ?_⟩
  · obtain ⟨a⟩ := hdual j
    exact (isIrreducible_iff_of_equiv a).mpr
      ((CuspidalSupport.isIrreducible_comp_iff _ θ hθ).mpr (hs j.rev))
  · exact (CuspidalSupport.isIrreducible_comp_iff _ θ hθ).mpr (hs j)
  · obtain ⟨a⟩ := hdual j
    exact ⟨a.trans (s.compGradedEquiv θ j.rev).symm⟩

/-- Reversing the ordered blocks of a normalized product of irreducible
smooth factors preserves its actual composition factors with multiplicities. -/
theorem sameFactors_reverseProduct {n : ℕ} (hn : 0 < n) (D : BlockShape n) :
    letI := T.topology
    ∀ (A : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (D.size i) K.Carrier)),
      (∀ i, (A i).IsIrreducible) →
      HaveSameJordanHolderFactors
        ((normalizedProductInductionFunctor T D).obj A).obj
        ((normalizedProductInductionFunctor T D.reverse).obj (fun i => A i.rev)).obj := by
  let := T.topology
  intro A hA
  let := T.generalLinearTopologicalGroup n
  let θ := inverseTranspose n K.Carrier
  let σ := fun i => (A i).representation
  let τ := fun i : Fin D.reverse.length => (A i.rev).representation
  let X := normalizedProductInduced T D σ
  let Y := normalizedProductInduced T D.reverse τ
  change HaveSameJordanHolderFactors (Rep.of X) (Rep.of Y)
  obtain ⟨E⟩ := productDualReversal T n D A hA
  have hY : IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear n K.Carrier)) Y.asModule :=
    AllFieldBZ.Classification.irreducibleProductFiniteLength K T n hn D.reverse
      (fun i => A i.rev) (fun i => hA i.rev)
  obtain ⟨c, h₀, h₁⟩ := isFiniteLength_iff_exists_compositionSeries.mp hY
  obtain ⟨s, hs⟩ := LengthCriterionProof.hasCompositionSeriesLength_of_compositionSeries
    (A := Rep.of Y) c h₀ h₁
  have hdual := sameFactors_dual_inverseTranspose T hn Y
    (isSmooth_normalizedProductInduced T D.reverse τ) s hs
  have hcomp : HaveSameJordanHolderFactors (Rep.of (X.comp θ.toMonoidHom))
      (Rep.of (Y.comp θ.toMonoidHom)) :=
    haveSameJordanHolderFactors_transport hdual (Parabolic.equivSymm E) (Representation.Equiv.refl _)
  exact haveSameJordanHolderFactors_of_comp θ hcomp

end Langlands.Aubert.LocalFieldGraded
