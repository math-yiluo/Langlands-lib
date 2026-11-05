import Langlands.Representation.Parabolic.FlattenedTensorOccurrences
import Langlands.Representation.Aubert.General.CuspidalInductionExclusion
import Langlands.Representation.Aubert.General.CuspidalityTransport
import Langlands.Representation.Tensor.SmoothSubquotients
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Actual cuspidal remainder splittings under group equivalences -/

noncomputable section

open CategoryTheory Limits

namespace Langlands.SmoothRep

universe uG uH uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H]

/-- The same-carrier smooth pullback and inverse pullback form an actual
equivalence of categories. -/
def pullbackEquivalence (e : H ≃ₜ* G) :
    SmoothRep.{0, uG, uV} ℂ G ≌ SmoothRep.{0, uH, uV} ℂ H where
  functor := pullbackFunctor e
  inverse := pullbackFunctor e.symm
  unitIso := NatIso.ofComponents (fun A => (pullbackSymmIso e A).symm)
    (fun _ => by ext; rfl)
  counitIso := NatIso.ofComponents (fun A => pullbackSymmIso e.symm A)
    (fun _ => by ext; rfl)
  functor_unitIso_comp _ := by ext; rfl

end Langlands.SmoothRep

namespace Langlands.Aubert.General

universe uG uV uK uK'

variable {G H : Type uG} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]
  [LocallyCompactSpace G] [LocallyCompactSpace H]
  [NonarchimedeanGroup G] [NonarchimedeanGroup H]
  {κ : Type uK} {κ' : Type uK'}
  {P M U : κ → Subgroup G} {P' M' U' : κ' → Subgroup H}
  {h : ∀ k, IsSemidirectDecomposition (P k) (M k) (U k)}
  {h' : ∀ k, IsSemidirectDecomposition (P' k) (M' k) (U' k)}
  {hU : ∀ k, IsClosed (U k : Set G)}
  {hU' : ∀ k, IsClosed (U' k : Set H)}

/-- A comparison of the exact cuspidality predicates transports the actual
binary coproduct and its exclusion property, including arbitrary nonzero
subquotients of the remainder. -/
theorem HasCuspidalRemainderSplitting.pullback
    (e : H ≃ₜ* G)
    (hcusp : ∀ A : SmoothRep.{0, uG, uV} ℂ G,
      IsCuspidalFor P' M' U' h' hU' (SmoothRep.pullback e A) ↔
        IsCuspidalFor P M U h hU A)
    {A : SmoothRep.{0, uG, uV} ℂ G}
    (hsplit : HasCuspidalRemainderSplitting P M U h hU A) :
    HasCuspidalRemainderSplitting P' M' U' h' hU' (SmoothRep.pullback e A) := by
  obtain ⟨Y, j, hC, hR, ⟨hc⟩⟩ := hsplit
  refine ⟨(fun b => SmoothRep.pullback e (Y b)),
    (fun b => (SmoothRep.pullbackFunctor e).map (j b)), (hcusp _).mpr hC, ?_, ?_⟩
  · intro D hD hDQ hDc
    have hDQ' : SmoothRep.IsSubquotient (SmoothRep.pullback e.symm D) (Y false) :=
      (hDQ.pullback e.symm).of_iso_right (SmoothRep.pullbackSymmIso e _)
    have hDc' : IsCuspidalFor P M U h hU (SmoothRep.pullback e.symm D) :=
      (hcusp _).mp (hDc.of_iso (SmoothRep.pullbackSymmIso e.symm D))
    exact hR _ hD hDQ' hDc'
  · let : (SmoothRep.pullbackFunctor e).IsEquivalence :=
      (SmoothRep.pullbackEquivalence e).isEquivalence_functor
    exact ⟨isColimitCofanMkObjOfIsColimit (SmoothRep.pullbackFunctor e) Y j hc⟩

end Langlands.Aubert.General
