import Langlands.Cohomology.SiteCech.FiniteCoverCechLifting
import Langlands.Cohomology.SiteCech.FiniteCechSystem
import Langlands.Cohomology.SiteCech.CoverExactnessStatement
import Mathlib.Algebra.Homology.SingleHomology

/-! # Finite test systems from actual finite-cover Čech complexes -/

noncomputable section

namespace Langlands.Cohomology.SiteCech

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u v w a

section Augmentations

variable {D : Type u} [Category.{v} D] [Abelian D]
variable (P : ChainComplex D ℕ) {X : D}
variable (ε : P ⟶ (ChainComplex.single₀ D).obj X)

/-- The zero component of a chain augmentation annihilates the first boundary. -/
theorem chainAugmentation_zero : P.d 1 0 ≫ ε.f 0 = 0 :=
  ((ChainComplex.toSingle₀Equiv P X) ε).property

/-- A quasi-isomorphic augmentation is exact and epimorphic at degree zero. -/
theorem chainAugmentation_exact_epi [QuasiIso ε] :
    (ShortComplex.mk (P.d 1 0) (ε.f 0) (chainAugmentation_zero P ε)).Exact ∧
      Epi (ε.f 0) := by
  have h : QuasiIsoAt ε 0 := inferInstance
  rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros'] at h
  · exact h
  all_goals (simp <;> rfl)

/-- A quasi-isomorphic augmentation forces exactness in every positive degree. -/
theorem chainAugmentation_positive_exact [QuasiIso ε] (n : ℕ) :
    P.ExactAt (n + 1) :=
  (quasiIsoAt_iff_exactAt' ε (n + 1)
    (ChainComplex.exactAt_succ_single_obj X n)).1 inferInstance

end Augmentations

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable {ι : Type a} (B : ι → C) [LocallySmall.{w} C]

/-- The finite-cover presheaf arrow is locally surjective. -/
theorem FiniteBasisCover.presheafArrow_isLocallySurjective
    {U : C} (c : FiniteBasisCover J B U) :
    Presheaf.IsLocallySurjective J (c.presheafArrow J B).hom :=
  (J.ofArrows_mem_iff_isLocallySurjective_sigmaDesc_shrinkYoneda_map c.arrow).1 c.covering

/-- A finite basis-representable presentation of every actual presheaf nerve term. -/
structure FiniteBasisCover.CechPresentation {U : C} (c : FiniteBasisCover J B U) where
  size : ℕ → ℕ
  index : ∀ n, Fin (size n) → ι
  iso : ∀ n, (c.presheafArrow J B).cechNerve.obj (op ⦋n⦌) ≅
    ∐ (fun j => shrinkYoneda.{w}.obj (B (index n j)))

variable (R : Type w) [CommRing R] [HasSheafify J (ModuleCat.{w} R)]

/-- Free sheaves transport a supplied finite presheaf presentation to a chain term. -/
def FiniteBasisCover.CechPresentation.freeTermIso
    {U : C} {c : FiniteBasisCover J B U}
    (p : c.CechPresentation J B) (n : ℕ) :
    (freeCechChainComplex J R (c.presheafArrow J B)).X n ≅
      ∐ (fun j => (freeSheafFunctor J R).obj
        (shrinkYoneda.{w}.obj (B (p.index n j)))) :=
  (freeSheafFunctor J R).mapIso (p.iso n) ≪≫
    PreservesCoproduct.iso (freeSheafFunctor J R)
      (fun j => shrinkYoneda.{w}.obj (B (p.index n j)))

variable [J.WEqualsLocallyBijective (ModuleCat.{w} R)]

/-- Actual finite-cover free Čech complexes form a finite test system once full
augmented exactness and finite presentations of every nerve term are supplied. -/
def finiteBasisCoverCechSystem
    (hB : HasFiniteBasisCoverRefinements J B)
    (hE : FreeCechCoverExactnessStatement C J R)
    (p : ∀ i (c : FiniteBasisCover J B (B i)), c.CechPresentation J B) :
    FiniteCechSystem (fun i =>
      (freeSheafFunctor J R).obj (shrinkYoneda.{w}.obj (B i))) where
  Cover i := FiniteBasisCover J B (B i)
  complex _ c := freeCechChainComplex J R (c.presheafArrow J B)
  augmentation _ c := (freeCechAugmentation J R (c.presheafArrow J B)).f 0
  augmentation_zero _ c := chainAugmentation_zero _ _
  augmentation_epi _ c := by
    have := hE _ (c.presheafArrow_isLocallySurjective J B)
    exact (chainAugmentation_exact_epi _ _).2
  augmentation_exact _ c := by
    have := hE _ (c.presheafArrow_isLocallySurjective J B)
    exact (chainAugmentation_exact_epi _ _).1
  positive_exact _ c n := by
    have := hE _ (c.presheafArrow_isLocallySurjective J B)
    exact chainAugmentation_positive_exact _
      (freeCechAugmentation J R (c.presheafArrow J B)) n
  termSize i c := (p i c).size
  termIndex i c := (p i c).index
  termIso i c n := (p i c).freeTermIso J B R n
  local_lift S hS i s := exists_finiteBasisCover_cech_lift J B R hB S hS i s

end Langlands.Cohomology.SiteCech
