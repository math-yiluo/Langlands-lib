import Langlands.Representation.Category.FrobeniusChainAdjunction
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Opposites

/-! # Limits of dual diagrams from the Frobenius chain -/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe uG uV uM uW uJ vJ

namespace Langlands.SmoothRep

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type uM} [Group M] [TopologicalSpace M] [IsTopologicalGroup M]
  {L : SmoothRep.{0, uM, uW} ℂ M ⥤ SmoothRep.{0, uG, uV} ℂ G}
  {R r : SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uM, uW} ℂ M}

/-- The Frobenius chain takes the dual of any colimit cocone to a limit cone
after applying `R`. No unit-factorization condition is used. -/
def frobeniusChainDualLimit (F : r ⊣ L)
    (C : L.op ⋙ contragredientFunctor.{0, uG, uV} ≅
      contragredientFunctor.{0, uM, uW} ⋙ L)
    (Ψ : contragredientFunctor.{0, uG, uV} ⋙ R ≅
      r.op ⋙ contragredientFunctor.{0, uM, uW})
    {J : Type uJ} [Category.{vJ} J]
    {K : J ⥤ SmoothRep.{0, uG, uV} ℂ G} {c : Cocone K}
    (hc : IsColimit c) :
    IsLimit (R.mapCone (contragredientFunctor.mapCone c.op)) := by
  letI := (frobeniusChainAdjunction F C Ψ).isRightAdjoint
  exact isLimitOfPreserves (contragredientFunctor ⋙ R) hc.op

/-- With the source limit supplied, `R` preserves the limit of every diagram
obtained by applying the smooth contragredient to a diagram in the opposite
category. In particular this applies to products of smooth contragredients. -/
theorem preservesLimit_contragredient_of_frobeniusChain (F : r ⊣ L)
    (C : L.op ⋙ contragredientFunctor.{0, uG, uV} ≅
      contragredientFunctor.{0, uM, uW} ⋙ L)
    (Ψ : contragredientFunctor.{0, uG, uV} ⋙ R ≅
      r.op ⋙ contragredientFunctor.{0, uM, uW})
    {J : Type uJ} [Category.{vJ} J]
    (K : J ⥤ (SmoothRep.{0, uG, uV} ℂ G)ᵒᵖ) [HasLimit K] :
    PreservesLimit (K ⋙ contragredientFunctor) R := by
  let := (contragredientAdjunction.{0, uG, uV} (R := ℂ) (G := G)).isRightAdjoint
  let := (frobeniusChainAdjunction F C Ψ).isRightAdjoint
  exact preservesLimit_of_preserves_limit_cone
    (isLimitOfPreserves contragredientFunctor (limit.isLimit K))
    (isLimitOfPreserves (contragredientFunctor ⋙ R) (limit.isLimit K))

end Langlands.SmoothRep
