/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Presentation.DiagonalTowerTracePresentations
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import WeilConjectures.AlgebraicGeometry.ProEtale.Replete
import all WeilConjectures.CategoryTheory.Finite.FiniteTowerLimitOrthogonality

/-! # Local descent for completed coefficient lines

Source: Stacks Tags 099L, 099M and 091Q, and the diagonal trace proof,
paragraph (1).
(blueprint: lem-sfb-diagonal-completed-line-complete-aux).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

private theorem completedForget_preservesSheafification (S : Scheme.{u}) :
    (Scheme.ProEt.topology S).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}) := by
  have : EssentiallySmall.{u + 1} S.ProEt := essentiallySmallSelf.{0} _
  constructor
  intro P Q f hf
  change (Scheme.ProEt.topology S).W
    (Functor.whiskerRight f (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}))
  have hi : Presheaf.IsLocallyInjective (Scheme.ProEt.topology S) f := hf.isLocallyInjective
  have hs : Presheaf.IsLocallySurjective (Scheme.ProEt.topology S) f := hf.isLocallySurjective
  apply ((Scheme.ProEt.topology S).W_iff_isLocallyBijective _).mpr
  constructor
  · exact ⟨fun x y h ↦ Presheaf.equalizerSieve_mem (Scheme.ProEt.topology S) f x y h⟩
  · exact ⟨fun x ↦ Presheaf.imageSieve_mem (Scheme.ProEt.topology S) f x⟩

private theorem finiteCoefficient_difference (l : ℕ) [Fact l.Prime]
    (S : Scheme.{u}) (n : ℕ) :
    IsIso ((sequenceDifference (Sheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1}) l).app
      ((sheafCompose (Scheme.ProEt.topology S)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
          (Scheme.purTwistFiniteRing S l n))) := by
  have := completedForget_preservesSheafification S
  let J := Scheme.ProEt.topology S
  let R := CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1))))
  let A := (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}).obj R
  let F := constantSheaf J AddCommGrpCat.{u + 1}
  have hz : l ^ (n + 1) • 𝟙 A = 0 := by
    ext x
    apply ULift.ext
    change l ^ (n + 1) • x.down = 0
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  have hF : l ^ (n + 1) • 𝟙 (F.obj A) = 0 := by
    rw [← F.map_id, ← F.map_nsmul, hz, F.map_zero]
  let e := (constantCommuteCompose J
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).app R
  exact sequenceDifference_iso l e (sequenceDifference_nilpotent l (F.obj A) (n + 1) hF)

private noncomputable instance completedForget_preservesLimits (S : Scheme.{u})
    {D : Type} [SmallCategory D] :
    PreservesLimitsOfShape D
      (sheafCompose (Scheme.ProEt.topology S)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})) := by
  let J := Scheme.ProEt.topology S
  let H := forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
    forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}
  have : PreservesLimitsOfShape D
      (sheafCompose J H ⋙ sheafToPresheaf J AddCommGrpCat.{u + 1}) :=
    preservesLimitsOfShape_of_natIso
      (Iso.refl (sheafToPresheaf J CommRingCat.{u + 1} ⋙
        (Functor.whiskeringRight _ _ _).obj H))
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf J _)

private theorem completedCoefficient_difference (l : ℕ) [Fact l.Prime] (S : Scheme.{u}) :
    IsIso ((sequenceDifference (Sheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1}) l).app
      ((sheafCompose (Scheme.ProEt.topology S)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
          (Scheme.purTwistZlCompletion S l))) := by
  let H := sheafCompose (Scheme.ProEt.topology S)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})
  let T := Scheme.purTwistZlTower S l
  let e := preservesLimitIso H T
  apply sequenceDifference_iso l e
  apply sequenceDifference_limit (T ⋙ H) l
  intro n
  exact finiteCoefficient_difference l S n.unop

/--
The local-to-global part of completeness for a completed coefficient line.

Source: blueprint latest, `sk-prop-diagonal-tower-trace.proof.md`, paragraph (1),
and Stacks Tags 099L, 099M and 091Q.

Proof: on each member of the displayed pro-etale cover, identify the line with the
regular completed coefficient module. The quotient tower of that regular module is
surjective on the weakly contractible basis, hence its derived inverse limit agrees
with its ordinary limit. The principal-ideal orthogonal criterion gives vanishing
of maps from every complex on which `l` acts invertibly. Exact restriction to the
constant coefficient category and descent for a sheaf cover transport this vanishing
to the globally displayed line. The empty site is included vacuously.
(blueprint: lem-sfb-diagonal-completed-line-complete-aux).
-/
theorem diagonalCompletedLine_complete_of_cover (l : ℕ) [Fact l.Prime] (S : Scheme.{u})
    [IsNoetherian S] [DiagonalTraceLocalizations l S]
    (L : DiagonalCompleted l S)
    (hcover : ∀ U : S.ProEt, ∃ s : Sieve U, s ∈ (Scheme.ProEt.topology S) U ∧
      ∀ (V : S.ProEt) (f : V ⟶ U), s f →
        Nonempty (L.over V ≅
          (SheafOfModules.unit
            (Scheme.purTwistRing S (Scheme.purTwistZlCompletion S l))).over V)) :
    ∀ V : DerivedCategory (DiagonalMod l S), IsIso (l • 𝟙 V) →
      Subsingleton (V ⟶ (diagonalCompletedUnderlying l S).obj
        ((DerivedCategory.singleFunctor (DiagonalCompleted l S) 0).obj L)) := by
  let J := Scheme.ProEt.topology S
  let R := Scheme.purTwistRing S (Scheme.purTwistZlCompletion S l)
  let B := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
    (Scheme.purTwistZlCompletion S l)
  let M := (diagonalCompletedRestriction l S).obj L
  have hB : IsIso ((sequenceDifference (Sheaf J AddCommGrpCat.{u + 1}) l).app B) :=
    completedCoefficient_difference l S
  have hM : IsIso ((sequenceDifference (DiagonalMod l S) l).app M) := by
    apply Sheaf.isIso_of_isIso_app_of_mem J
    intro U
    obtain ⟨s, hs, hlocal⟩ := hcover U
    refine ⟨s, hs, ?_⟩
    intro V f hf
    obtain ⟨e⟩ := hlocal V f hf
    let E : DiagonalMod l S ⥤ AddCommGrpCat.{u + 1} :=
      sheafToPresheaf J (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) ⋙
        (evaluation _ _).obj (op V) ⋙
          forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) AddCommGrpCat.{u + 1}
    let EB : Sheaf J AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
      sheafToPresheaf J AddCommGrpCat.{u + 1} ⋙ (evaluation _ _).obj (op V)
    have hBg : IsIso ((sequenceDifference AddCommGrpCat.{u + 1} l).app (EB.obj B)) :=
      (sequenceDifference_map_isIso_iff EB l B).mp (by have := hB; infer_instance)
    let T := SheafOfModules.evaluation.{u + 1} (R.over V) (op (Over.mk (𝟙 V))) ⋙
      forget₂ (ModuleCat.{u + 1} ((R.over V).obj.obj (op (Over.mk (𝟙 V)))))
        AddCommGrpCat.{u + 1}
    let e' : E.obj M ≅ EB.obj B := T.mapIso e
    have hMg : IsIso ((sequenceDifference AddCommGrpCat.{u + 1} l).app (E.obj M)) :=
      sequenceDifference_iso l e' hBg
    have hm : IsIso (E.map ((sequenceDifference (DiagonalMod l S) l).app M)) :=
      (sequenceDifference_map_isIso_iff E l M).mpr hMg
    have : IsIso
        ((forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) AddCommGrpCat.{u + 1}).map
          (((sequenceDifference (DiagonalMod l S) l).app M).hom.app (op V))) := hm
    exact isIso_of_reflects_iso _
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) AddCommGrpCat.{u + 1})
  have : PreservesLimitsOfShape (Discrete ℕ)
      ((CochainComplex.singleFunctors (DiagonalMod l S)).functor 0) :=
    inferInstanceAs (PreservesLimitsOfShape _
      (HomologicalComplex.single (DiagonalMod l S) (.up ℤ) 0))
  have : PreservesLimitsOfShape (Discrete ℕ)
      (DerivedCategory.singleFunctor (DiagonalMod l S) 0) :=
    preservesLimitsOfShape_of_natIso
      (DerivedCategory.singleFunctorIsoCompQ (DiagonalMod l S) 0).symm
  let e := ((diagonalCompletedRestriction l S).mapDerivedCategorySingleFunctor 0).app L
  intro V hV
  have := hV
  have h := sequenceDifference_orthogonal
    (DerivedCategory.singleFunctor (DiagonalMod l S) 0) l M hM V
  exact ⟨fun f g ↦ (cancel_mono e.hom).mp (h.elim (f ≫ e.hom) (g ≫ e.hom))⟩

end AlgebraicGeometry.ProEtale.DiagonalTrace
