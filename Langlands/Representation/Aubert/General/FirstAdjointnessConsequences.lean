import Langlands.Representation.Aubert.General.FirstAdjointness
import Mathlib.RepresentationTheory.Irreducible

/-!
# Nonvanishing consequences of actual normalized first adjointness

A nonzero map into normalized induction has a nonzero adjoint from the actual
Jacquet module. With a simple inducing representation that adjoint is
surjective; if its source is also simple it is an actual equivalence.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Aubert.General.FirstAdjointness

universe uG uV uW

open CategoryTheory SmoothRep
open Jacquet.Localization

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
variable {P M U : Subgroup G}
variable (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hδ : IsUnimodularModulus U hU)
variable (A : SmoothRep.{0, uG, uV} ℂ G) (σ : SmoothRep.{0, uG, uW} ℂ M)

/-- The actual first-adjointness map is natural in the smooth source. -/
theorem equiv_comp {B : SmoothRep.{0, uG, uV} ℂ G} (f : B ⟶ A)
    (F : A.representation.IntertwiningMap
      ((normalizedInductionFunctor h hU).obj σ).representation) :
    equiv h hU hδ B σ (F.comp (hom f)) =
      (equiv h hU hδ A σ F).comp (hom ((jacquetFunctor h hU).map f)) := by
  apply Representation.IntertwiningMap.ext
  apply Jacquet.Localization.hom_ext
  ext v
  rfl

/-- The actual first-adjointness map is natural in the inducing representation. -/
theorem equiv_inducedMap {τ : SmoothRep.{0, uG, uW} ℂ M} (c : σ ⟶ τ)
    (F : A.representation.IntertwiningMap
      ((normalizedInductionFunctor h hU).obj σ).representation) :
    equiv h hU hδ A τ
        ((hom ((normalizedInductionFunctor h hU).map c)).comp F) =
      (hom c).comp (equiv h hU hδ A σ F) := by
  apply Representation.IntertwiningMap.ext
  apply Jacquet.Localization.hom_ext
  ext v
  rfl

/-- A nonzero map into actual normalized induction has a nonzero adjoint. -/
theorem equiv_ne_zero
    (F : A.representation.IntertwiningMap
      ((normalizedInductionFunctor h hU).obj σ).representation) (hF : F ≠ 0) :
    equiv h hU hδ A σ F ≠ 0 := by
  intro he
  apply hF
  apply (equiv h hU hδ A σ).injective
  simpa using he

include hδ in
/-- Any smooth representation mapping nontrivially into actual induction has a
nontrivial actual normalized Jacquet module. -/
theorem nontrivial_jacquet_of_map_ne_zero
    (F : A.representation.IntertwiningMap
      ((normalizedInductionFunctor h hU).obj σ).representation) (hF : F ≠ 0) :
    Nontrivial ((jacquetFunctor h hU).obj A) := by
  by_contra hn
  have : Subsingleton ((jacquetFunctor h hU).obj A) :=
    not_nontrivial_iff_subsingleton.mp hn
  apply equiv_ne_zero h hU hδ A σ F hF
  ext q
  rw [Subsingleton.elim q 0, map_zero, map_zero]

/-- If the inducing representation is irreducible, the adjoint of every
nonzero map into induction is an actual surjection. -/
theorem equiv_surjective
    (hσ : σ.IsIrreducible)
    (F : A.representation.IntertwiningMap
      ((normalizedInductionFunctor h hU).obj σ).representation) (hF : F ≠ 0) :
    Function.Surjective (equiv h hU hδ A σ F) := by
  let := hσ
  exact (Representation.IsIrreducible.surjective_or_eq_zero
    (equiv h hU hδ A σ F)).resolve_right (equiv_ne_zero h hU hδ A σ F hF)

/-- The quotient map onto a simple inducing representation, with its actual
surjectivity witness. Its value is the descended evaluation map. -/
def quotientMapOfNonzero
    (hσ : σ.IsIrreducible)
    (F : A.representation.IntertwiningMap
      ((normalizedInductionFunctor h hU).obj σ).representation) (hF : F ≠ 0) :
    { f : ((jacquetFunctor h hU).obj A).representation.IntertwiningMap σ.representation //
      Function.Surjective f } :=
  ⟨equiv h hU hδ A σ F, equiv_surjective h hU hδ A σ hσ F hF⟩

/-- With simple source Jacquet module as well, the adjoint is an actual
representation equivalence, including when the carrier universes differ. -/
def equivalenceOfIrreducibleJacquet
    (hA : ((jacquetFunctor h hU).obj A).IsIrreducible)
    (hσ : σ.IsIrreducible)
    (F : A.representation.IntertwiningMap
      ((normalizedInductionFunctor h hU).obj σ).representation) (hF : F ≠ 0) :
    ((jacquetFunctor h hU).obj A).representation.Equiv σ.representation := by
  letI := hA
  letI := hσ
  exact (equiv h hU hδ A σ F).ofBijective
    ((Representation.IsIrreducible.bijective_or_eq_zero
      (equiv h hU hδ A σ F)).resolve_right (equiv_ne_zero h hU hδ A σ F hF))

include hδ in
/-- In particular every nontrivial subobject of actual induction has nonzero
actual normalized Jacquet module. -/
theorem nontrivial_jacquet_of_injective [Nontrivial A]
    (F : A.representation.IntertwiningMap
      ((normalizedInductionFunctor h hU).obj σ).representation)
    (hF : Function.Injective F) :
    Nontrivial ((jacquetFunctor h hU).obj A) := by
  apply nontrivial_jacquet_of_map_ne_zero h hU hδ A σ F
  intro he
  obtain ⟨v, hv⟩ := exists_ne (0 : A)
  apply hv
  apply hF
  rw [he]
  rfl

end Langlands.Aubert.General.FirstAdjointness
