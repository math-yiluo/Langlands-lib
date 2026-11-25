/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.AlgebraicGeometry.IntegralLfpLocalTorsionCharts
import all WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf

/-! # A uniform torsion bound and finite quotient charts -/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private lemma finiteRefinement (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (U : Scheme.Cover.{u} Scheme.proetalePrecoverage X) :
    ∃ V : Scheme.Cover.{u} Scheme.proetalePrecoverage X,
      Finite V.I₀ ∧ Nonempty (V.toPreZeroHypercover.Hom U.toPreZeroHypercover) := by
  obtain ⟨V, f, hV, _⟩ := QuasiCompactCover.exists_hom U.forgetQc
  let : Finite V.cover.I₀ := hV
  let (i : V.cover.I₀) : AlgebraicGeometry.QuasiCompact (V.cover.f i) := inferInstance
  let : QuasiCompactCover V.cover.toPreZeroHypercover := .of_finite
  let W := Scheme.Cover.ofQuasiCompactCover V.cover
  exact ⟨W, hV, ⟨f⟩⟩

private noncomputable def setPullbackCompIso {X Y Z : Scheme.{u}}
    (f : Z ⟶ Y) (g : Y ⟶ X) :
    Scheme.proEtaleSheafInverseImage (f ≫ g) (Type (u + 1)) ≅
      Scheme.proEtaleSheafInverseImage g (Type (u + 1)) ⋙
        Scheme.proEtaleSheafInverseImage f (Type (u + 1)) := by
  let a := (Scheme.proEtaleSheafAdjunction g (Type (u + 1))).comp
    (Scheme.proEtaleSheafAdjunction f (Type (u + 1)))
  let e := Functor.sheafPushforwardContinuousComp'
    (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f g).symm
    (Type (u + 1)) (Scheme.ProEt.topology X) (Scheme.ProEt.topology Y)
      (Scheme.ProEt.topology Z)
  exact (Scheme.proEtaleSheafAdjunction (f ≫ g) (Type (u + 1))).leftAdjointUniq
    (a.ofNatIsoRight e)

/-- A sufficiently high scalar power has locally free image. Its quotient has a
finite locally constant underlying sheaf of sets.

Source: Bhatt--Scholze, Definition 6.8.10, Proposition 6.8.11(3), and the
continuous Smith invariant argument in the parent integral resolution node.

Proof: choose the local charts and their eventual bounds. The base is noetherian,
hence compact and quasi-separated. Quasi-compact refinement gives a finite affine
cover refining the chart cover. Its arrows are quasi-compact, so it is again a
pro-etale cover. Take the maximum of the finitely many local bounds. The image
charts pull back as finite free modules. For the quotient charts, inverse image
commutes with composition and preserves constant sheaves: both comparisons follow
from the corresponding adjunctions. Pull back the finite constant set charts
along the refinement. This proves both assertions for one common exponent and
one common cover. Empty finite families have maximum zero. No definitions choose
witnesses of an unproved existence statement.
-/
theorem integral_lfp_finite_quotient_charts
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (CondensedRing.integralCoeff ℓ E) X))
    (hP : IsLocallyFinitelyPresented
      (condensedRingObj (CondensedRing.integralCoeff ℓ E) X) P) :
    ∃ N : ℕ,
      (∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ s : C.I₀,
        Mod.IsFree ((upperStar Ab.{u + 1} (C.f s)).obj
          (condensedRingObj (CondensedRing.integralCoeff ℓ E) X))
          (((upperStar Ab.{u + 1} (C.f s)).mapMod _).obj
            (image ((ℓ ^ N) • 𝟙 P)))) ∧
      (∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ s : C.I₀,
        ∃ n : ℕ, Nonempty
          ((Scheme.proEtaleSheafInverseImage (C.f s) (Type (u + 1))).obj
            ((Mod.forget _ ⋙ sheafCompose (Scheme.ProEt.topology X)
              (forget Ab.{u + 1})).obj (cokernel ((ℓ ^ N) • 𝟙 P))) ≅
            (constantSheaf (Scheme.ProEt.topology (C.X s)) (Type (u + 1))).obj
              (ULift.{u + 1} (Fin n)))) := by
  classical
  obtain ⟨C, hC⟩ := integral_lfp_local_torsion_charts X ℓ E P hP
  choose bound hbound using hC
  obtain ⟨V, hV, ⟨r⟩⟩ := finiteRefinement X C
  let : Finite V.I₀ := hV
  let : Fintype V.I₀ := Fintype.ofFinite _
  let N := Finset.univ.sup (fun j : V.I₀ ↦ bound (r.s₀ j))
  have hN (j : V.I₀) : bound (r.s₀ j) ≤ N :=
    Finset.le_sup (f := fun j : V.I₀ ↦ bound (r.s₀ j)) (Finset.mem_univ j)
  refine ⟨N, ⟨V, fun j ↦ ?_⟩, ⟨V, fun j ↦ ?_⟩⟩
  · rw [← r.w₀ j]
    exact (free_pullback_comp_iff (r.h₀ j) (C.f (r.s₀ j)) _).mpr
      (free_pullback (r.h₀ j) (hbound (r.s₀ j) N (hN j)).1)
  · obtain ⟨n, ⟨e⟩⟩ := (hbound (r.s₀ j) N (hN j)).2
    refine ⟨n, ⟨?_⟩⟩
    rw [← r.w₀ j]
    exact (setPullbackCompIso (r.h₀ j) (C.f (r.s₀ j))).app _ ≪≫
      (Scheme.proEtaleSheafInverseImage (r.h₀ j) (Type (u + 1))).mapIso e ≪≫
      (Functor.sheafPullbackConstruction.sheafPullbackIso (Scheme.proEtaleBaseChange (r.h₀ j))
        (Type (u + 1)) (Scheme.ProEt.topology _) (Scheme.ProEt.topology _)).symm.app _ ≪≫
      ((Scheme.proEtaleBaseChange (r.h₀ j)).constantSheafsheafPullbackIso (Type (u + 1))
        (Scheme.ProEt.topology _) (Scheme.ProEt.topology _) terminalIsTerminal
        (terminalIsTerminal.isTerminalObj _)).app _

end AlgebraicGeometry.ProEtale
