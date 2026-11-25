/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.FiniteEtaleNoetherianClopenAssemblyPiece
import WeilConjectures.AlgebraicGeometry.FiniteEtaleNoetherianClopenAssemblyAppend

/-! The reduced Noetherian induction core for generic affine properties. -/

@[expose] public section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Reduced-case Noetherian induction for the generic affine property.
Source: Stacks Project, Tags 01OZ and 01J3.
(blueprint: lem-a1-finite-etale-noetherian-clopen-assembly-core).

The proof is decomposed into two strict subarguments: one chooses an affine open in an
irreducible component and produces the strict closed complement, and the other appends
the resulting reduced generic stratum to a finite stratification of that complement.
Noetherian induction combines those two subarguments. The inductive claim is that every
closed subset admits such a finite stratification with support exactly that subset. The
base case is the empty closed subset, represented by the zero-index stratification. In
the step, the generic-piece lemma supplies an integral affine open with strict closed
complement; the induction hypothesis stratifies that complement, and the append lemma
adds the generic piece.
-/
theorem exists_reduced_stratification_of_integral_affine_generic_reduced
    (Y : Scheme.{u}) [IsLocallyNoetherian Y] [CompactSpace Y] [IsReduced Y]
    (P : (B : Scheme.{u}) → (B ⟶ Y) → Prop)
    (hgeneric : ∀ (B : Scheme.{u}) [IsIntegral B] [IsNoetherian B] [IsAffine B]
      (t : B ⟶ Y), IsImmersion t →
      ∃ U : B.Opens, Nonempty U ∧ P U.toScheme (U.ι ≫ t)) :
    ∃ T : FiniteLocallyClosedStratification Y,
      (∀ a : Fin T.n, IsReduced (T.domain a)) ∧
      ∀ a : Fin T.n, P (T.domain a) (T.immersion a) := by
  classical
  letI : IsNoetherian Y := {}
  have hPartial : ∀ T : TopologicalSpace.Closeds Y,
      Nonempty (ReducedFiniteLocallyClosedStratificationOn Y P T) := by
    intro T
    refine (wellFounded_lt (α := TopologicalSpace.Closeds Y)).induction
      (C := fun T => Nonempty (ReducedFiniteLocallyClosedStratificationOn Y P T)) T ?_
    intro T ih
    by_cases hT : (T : Set Y) = ∅
    · refine ⟨{
        n := 0
        stratum := Fin.elim0
        isLocallyClosed_stratum := by intro a; exact Fin.elim0 a
        pairwise_disjoint_stratum := by
          intro a
          exact Fin.elim0 a
        domain := Fin.elim0
        immersion := by intro a; exact Fin.elim0 a
        isImmersion := by intro a; exact Fin.elim0 a
        range_immersion := by intro a; exact Fin.elim0 a
        isReduced := by intro a; exact Fin.elim0 a
        property := by intro a; exact Fin.elim0 a
        support := by simpa [hT]
        subset := by intro a; exact Fin.elim0 a }⟩
    · obtain ⟨q⟩ :=
        exists_integral_affine_generic_piece_avoiding_components Y P hgeneric T hT
      let T' : TopologicalSpace.Closeds Y :=
        ⟨(T : Set Y) \ Set.range (q.W.ι ≫ q.j), q.complement_closed⟩
      have hlt : T' < T := q.strict_complement
      obtain ⟨S⟩ := ih T' hlt
      letI : IsIntegral q.B := q.isIntegral
      letI : IsImmersion q.j := q.isImmersion
      letI : Nonempty q.W := q.nonempty
      letI : IsIntegral q.W.toScheme := isIntegral_of_isOpenImmersion q.W.ι
      have hUred : IsReduced q.W.toScheme := by
        exact isReduced_of_isIntegral q.W.toScheme
      have hdisj :
          Disjoint (Set.range (q.W.ι ≫ q.j)) (T' : Set Y) := by
        apply Set.disjoint_left.mpr
        intro y hyj hyT
        exact hyT.2 hyj
      have hcover :
          Set.range (q.W.ι ≫ q.j) ∪ (T' : Set Y) = (T : Set Y) := by
        rw [show (T' : Set Y) = (T : Set Y) \ Set.range (q.W.ι ≫ q.j) by rfl]
        exact Set.union_sdiff_cancel q.range_subset
      obtain ⟨R⟩ :=
        append_reduced_stratum_to_complement Y P T T' q.W.toScheme
          (q.W.ι ≫ q.j) S hUred hdisj hcover q.property
      exact ⟨R⟩
  obtain ⟨S⟩ := hPartial (⊤ : TopologicalSpace.Closeds Y)
  let R : FiniteLocallyClosedStratification Y :=
    { n := S.n
      stratum := S.stratum
      isLocallyClosed_stratum := S.isLocallyClosed_stratum
      iUnion_stratum_eq_univ := by simpa using S.support
      pairwise_disjoint_stratum := S.pairwise_disjoint_stratum
      domain := S.domain
      immersion := S.immersion
      isImmersion := S.isImmersion
      range_immersion := S.range_immersion }
  exact ⟨R, S.isReduced, S.property⟩

end AlgebraicGeometry.Scheme
