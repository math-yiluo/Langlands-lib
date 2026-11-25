/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Internal.InternalPerfectReductionHomData

public import WeilConjectures.NumberTheory.Padics.IntegralScalarTowers
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Connected.Clopen
public import WeilConjectures.AlgebraicGeometry.InternalPerfectOrdinaryHomCohomology
public import WeilConjectures.AlgebraicGeometry.InternalPerfectReductionHomotopyComparison

/-! # Actual internal endomorphism reductions and scalar quotient cohomology

## References

* Stacks Project, Tags 09C5, 08JH and 06YQ
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Derived endomorphisms of the actual internal reductions are the locally constant
sections of the zeroth cohomology of the quotient algebraic Hom complex, naturally in
all quotient arrows. -/
theorem internalPerfectEndomorphism_homComparison
    (X : Scheme.{u}) (W : X.ProEt) (_hAffine : IsAffine W.left)
    (_hweak : (Scheme.ProEt.topology X).IsWeaklyContractible.{u + 1} W)
    (P : CochainComplex (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (a b : ℤ) (_ha : P.IsStrictlyGE a) (_hb : P.IsStrictlyLE b)
    (_hfree : ∀ i : ℤ, Module.Finite (Padic.coefficientExtensionIntegers l E) (P.X i) ∧
      Module.Free (Padic.coefficientExtensionIntegers l E) (P.X i)) :
    ∃ e : ∀ n : ℕ,
      (internalReductionHomTower l E W.left
        (internalPerfectScalarModel l E W.left P)
        (internalPerfectScalarModel l E W.left P)).obj (op n) ≃
      LocallyConstant (ConnectedComponents W.left)
        ((Padic.scalarQuotient (Padic.coefficientExtensionUniformizer l E)
          (CochainComplex.moduleHomComplex P P) (n + 1)).homology 0),
      ∀ (n m : ℕ) (h : n ≤ m) (x : (internalReductionHomTower l E W.left
        (internalPerfectScalarModel l E W.left P)
        (internalPerfectScalarModel l E W.left P)).obj (op m)),
        e n ((internalReductionHomTower l E W.left
          (internalPerfectScalarModel l E W.left P)
          (internalPerfectScalarModel l E W.left P)).map (homOfLE h).op x) =
        LocallyConstant.map
          (HomologicalComplex.homologyMap
            (Padic.scalarQuotientTransition (Padic.coefficientExtensionUniformizer l E)
              (CochainComplex.moduleHomComplex P P) (m + 1) (n + 1)
              (Nat.succ_le_succ h)) 0) (e m x) := by
  classical
  let e₀ : ∀ n : ℕ,
      (internalReductionHomTower l E W.left
        (internalPerfectScalarModel l E W.left P)
        (internalPerfectScalarModel l E W.left P)).obj (op n) ≃
      internalPerfectOrdinaryHom l E W.left P n :=
    internalPerfectReductionHomEquiv l E X W _hweak P a b _ha _hb _hfree
  have he₀ := internalPerfectReduction_homotopyComparison l E X W
    _hAffine _hweak P a b _ha _hb _hfree
  obtain ⟨e₁, he₁⟩ := internalPerfectOrdinary_homCohomology l E X W
    _hAffine _hweak P a b _ha _hb _hfree
  let e := fun n : ℕ ↦ (e₀ n).trans (e₁ n)
  have he (n : ℕ) (x : (internalReductionHomTower l E W.left
      (internalPerfectScalarModel l E W.left P)
      (internalPerfectScalarModel l E W.left P)).obj (op (n + 1))) :
      e n ((internalReductionHomTower l E W.left
        (internalPerfectScalarModel l E W.left P)
        (internalPerfectScalarModel l E W.left P)).map (homOfLE (Nat.le_succ n)).op x) =
      LocallyConstant.map
        (HomologicalComplex.homologyMap
          (Padic.scalarQuotientTransition (Padic.coefficientExtensionUniformizer l E)
            (CochainComplex.moduleHomComplex P P) (n + 2) (n + 1)
            (Nat.succ_le_succ (Nat.le_succ n))) 0) (e (n + 1) x) := by
    exact (congrArg (e₁ n) (he₀ n x)).trans (he₁ n (e₀ (n + 1) x))
  refine ⟨e, ?_⟩
  intro n m h x
  induction m, h using Nat.le_induction with
  | base =>
    have htrid :
        Padic.scalarQuotientTransition
            (Padic.coefficientExtensionUniformizer l E)
            (CochainComplex.moduleHomComplex P P) (n + 1) (n + 1)
            (Nat.succ_le_succ (Nat.le_refl n)) = 𝟙 _ := by
      apply (cancel_epi (cokernel.π
        ((Padic.coefficientExtensionUniformizer l E) ^ (n + 1) •
          𝟙 (CochainComplex.moduleHomComplex P P)))).1
      rw [Padic.scalarQuotientTransition, cokernel.π_desc]
      exact (Category.comp_id _).symm
    have hmap : (homOfLE (Nat.le_refl n)).op = (𝟙 (op n : ℕᵒᵖ)) :=
      Subsingleton.elim _ _
    rw [hmap]
    have htower := (internalReductionHomTower l E W.left
      (internalPerfectScalarModel l E W.left P)
      (internalPerfectScalarModel l E W.left P)).map_id (op n)
    rw [htower]
    change (e n) x = LocallyConstant.map _ ((e n) x)
    rw [htrid, HomologicalComplex.homologyMap_id]
    rfl
  | succ m hnm ih =>
    have hf : (homOfLE (hnm.trans (Nat.le_succ m))).op =
        (homOfLE (Nat.le_succ m)).op ≫ (homOfLE hnm).op := Subsingleton.elim _ _
    rw [hf, Functor.map_comp, types_comp_apply, ih]
    erw [he m x]
    have htr :
        Padic.scalarQuotientTransition
            (Padic.coefficientExtensionUniformizer l E)
            (CochainComplex.moduleHomComplex P P) (m + 2) (n + 1)
            (Nat.succ_le_succ (hnm.trans (Nat.le_succ m))) =
          Padic.scalarQuotientTransition
            (Padic.coefficientExtensionUniformizer l E)
            (CochainComplex.moduleHomComplex P P) (m + 2) (m + 1)
            (by omega) ≫
          Padic.scalarQuotientTransition
            (Padic.coefficientExtensionUniformizer l E)
            (CochainComplex.moduleHomComplex P P) (m + 1) (n + 1)
            (by omega) := by
      apply (cancel_epi (cokernel.π
        ((Padic.coefficientExtensionUniformizer l E) ^ (m + 2) •
          𝟙 (CochainComplex.moduleHomComplex P P)))).1
      simp [Padic.scalarQuotientTransition]
    rw [htr, HomologicalComplex.homologyMap_comp]
    ext y
    simp only [LocallyConstant.map_apply, Function.comp_apply, ModuleCat.comp_apply]

end AlgebraicGeometry.ProEtale
