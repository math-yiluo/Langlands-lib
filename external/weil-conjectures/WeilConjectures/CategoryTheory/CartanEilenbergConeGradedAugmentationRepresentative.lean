/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CartanEilenbergPresentation
public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-! # Differential of retained representatives in the cone filtration

Source: Stacks Project, Homology, Tags 012X and 0133, column filtration and
canonical augmentation; retained-summand calculation of the parent node.
-/

@[expose] public section

universe uA vA
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false in
/-- The graded differential of the lifted K summand is the column augmentation.
Source: Stacks Project, Homology, Tags 0133 and 012X, canonical augmentation and
second filtration; parent normalized-differential proof, K-term calculation.
(blueprint: lem-sp-cartan-eilenberg-cone-graded-augmentation-representative).

Proof: hm and hmm' identify m=p-1 and m'=p. Use chain compatibility of the
quotient projection and cancel the monic filtration inclusion to compute the
differential of l. The cone formula gives the augmentation to the right summand
minus d_K to the left summand in degree p. By haug and hl', the augmentation
is the inclusion of (a.f p).f 0 followed by l'. The remaining left summand has
complex index p+1, hence its image belongs to step p+1 by the first summand
of hF. Factor through that step, then through its inclusion into step p;
monicity identifies this with the difference just computed. The quotient kills
this factorization by the cokernel relation. No below-bound vanishing is needed. -/
theorem cartanEilenberg_cone_graded_augmentation_representative
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    (K : CochainComplex A ℤ)
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (a : ((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      K ⟶ I)
    (b : ℤ)
    (aug : K ⟶ (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).total
      (ComplexShape.up ℤ))
    (haug : ∀ n : ℤ, aug.f n = (a.f n).f 0 ≫
      (HomologicalComplex.extendXIso
        (((𝟭 A).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X n))
        ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv ≫
      (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotal
        (ComplexShape.up ℤ) 0 n n (zero_add n))
    (F : DecreasingFiltration (CochainComplex.mappingCone aug))
    (hF : ∀ p n : ℤ, F.complexStep p n =
        (if p ≤ n + 1 then imageSubobject
          ((CochainComplex.mappingCone.inl aug).v (n + 1) n (by omega)) else ⊥) ⊔
        (Finset.Icc (max b p) n).sup (fun s ↦ imageSubobject
          ((((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotalOrZero
            (ComplexShape.up ℤ) (n - s) s n ≫
              (CochainComplex.mappingCone.inr aug).f n)))
    (p m m' : ℤ) (hm : m + 1 = p) (hmm' : m + 1 = m')
    (l : K.X p ⟶ (F.step p : CochainComplex A ℤ).X m)
    (l' : (I.X p).X 0 ⟶ (F.step p : CochainComplex A ℤ).X m')
    (hl : l ≫ (F.step p).arrow.f m =
      (K.XIsoOfEq hm.symm).hom ≫
        (CochainComplex.mappingCone.inl aug).v (m + 1) m (by omega))
    (hl' : l' ≫ (F.step p).arrow.f m' =
      (HomologicalComplex.extendXIso
        (((𝟭 A).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X p))
        ComplexShape.embeddingUpNat (i := 0) (i' := m' - p)
        (by change (0 : ℤ) = m' - p; omega)).inv ≫
      (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotal
        (ComplexShape.up ℤ) (m' - p) p m' (by change (m' - p) + p = m'; omega) ≫
      (CochainComplex.mappingCone.inr aug).f m') :
    l ≫ (F.complexQuotientπ p (p + 1) (by omega)).f m ≫
        (F.gradedPiece p).d m m' =
      (a.f p).f 0 ≫ l' ≫ (F.complexQuotientπ p (p + 1) (by omega)).f m' := by
  subst m'
  subst p
  let q := F.complexQuotientπ (m + 1) (m + 1 + 1) (by omega)
  let inc := Subobject.ofLE (F.step (m + 1 + 1)) (F.step (m + 1))
    (F.antitone_step (by omega))
  let u := (CochainComplex.mappingCone.inl aug).v (m + 1 + 1) (m + 1) (by omega)
  have hu : imageSubobject u ≤ F.complexStep (m + 1 + 1) (m + 1) := by
    rw [hF, ite_eq_left (by omega)]
    exact le_sup_left
  have hmono : Mono ((F.step (m + 1 + 1)).arrow.f (m + 1)) := inferInstance
  have hu' : imageSubobject u ≤ Subobject.mk
      ((F.step (m + 1 + 1)).arrow.f (m + 1)) := by
    simpa only [DecreasingFiltration.complexStep, imageSubobject_mono] using hu
  let t := factorThruImageSubobject u ≫
    Subobject.ofLEMk _ ((F.step (m + 1 + 1)).arrow.f (m + 1)) hu'
  have ht : t ≫ (F.step (m + 1 + 1)).arrow.f (m + 1) = u := by
    dsimp only [t]
    rw [Category.assoc, Subobject.ofLEMk_comp, imageSubobject_arrow_comp]
  have hi : inc.f (m + 1) ≫ (F.step (m + 1)).arrow.f (m + 1) =
      (F.step (m + 1 + 1)).arrow.f (m + 1) :=
    congrArg (fun f ↦ f.f (m + 1)) (Subobject.ofLE_arrow
      (F.antitone_step (show m + 1 ≤ m + 1 + 1 by omega)))
  have hiq : inc.f (m + 1) ≫ q.f (m + 1) = 0 :=
    congrArg (fun f ↦ f.f (m + 1)) (cokernel.condition inc)
  have hl0 : l ≫ (F.step (m + 1)).arrow.f m =
      (CochainComplex.mappingCone.inl aug).v (m + 1) m (by omega) := by
    simpa using hl
  dsimp [CartanEilenbergPresentation.mappedFunctor] at hl'
  have haug' : (a.f (m + 1)).f 0 ≫ l' ≫
      (F.step (m + 1)).arrow.f (m + 1) =
      aug.f (m + 1) ≫ (CochainComplex.mappingCone.inr aug).f (m + 1) := by
    rw [hl', haug]
    simp only [Category.assoc]
    congr! <;> simp only [Int.sub_self]
  let α : K.X (m + 1) ⟶ (I.X (m + 1)).X 0 := (a.f (m + 1)).f 0
  have hd : l ≫ (F.step (m + 1) : CochainComplex A ℤ).d m (m + 1) =
      α ≫ l' -
        K.d (m + 1) (m + 1 + 1) ≫ t ≫ inc.f (m + 1) := by
    apply (cancel_mono ((F.step (m + 1)).arrow.f (m + 1))).1
    rw [Preadditive.sub_comp]
    simp only [Category.assoc, hi, ht]
    change α ≫ l' ≫ (F.step (m + 1)).arrow.f (m + 1) = _ at haug'
    rw [haug', ← (F.step (m + 1)).arrow.comm, ← Category.assoc, hl0]
    exact CochainComplex.mappingCone.inl_v_d aug (m + 1) m (m + 1 + 1)
      (by omega) (by omega)
  change l ≫ q.f m ≫ (F.gradedPiece (m + 1)).d m (m + 1) = _
  change l ≫ q.f m ≫ (F.complexQuotient (m + 1) (m + 1 + 1) _).d m (m + 1) =
    α ≫ l' ≫ q.f (m + 1)
  rw [q.comm, ← Category.assoc, hd, Preadditive.sub_comp]
  simp only [Category.assoc, hiq, comp_zero, sub_zero]


end CategoryTheory.Functor
