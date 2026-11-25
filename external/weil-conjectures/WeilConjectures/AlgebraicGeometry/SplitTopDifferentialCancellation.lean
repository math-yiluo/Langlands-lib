/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Homotopy
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import WeilConjectures.AlgebraicGeometry.SplitTopDifferentialCancellationProperties
import WeilConjectures.AlgebraicGeometry.SplitTopDifferentialCancellationHomotopy

/-! # Cancelling one split top differential of a sheaf complex

Source: Stacks Project, Tag 068V, explicit split cancellation in the bounded
finite-projective specialization; the identity-pair argument of Tag 00MT.
(blueprint: lem-pc-split-top-differential-cancellation)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

private theorem truncLE_term_retract (S : Scheme.{u}) (B : CochainComplex S.Modules ℤ)
    (m : ℕ) (hsplit : IsSplitEpi (B.d (m : ℤ) (m + 1 : ℕ))) (n : ℤ) :
    Nonempty (Retract ((B.truncLE m).X n) (B.X n)) := by
  classical
  by_cases hlt : n < (m : ℤ)
  · exact ⟨(B.truncLEXIso m n hlt).retract⟩
  by_cases heq : n = (m : ℤ)
  · subst n
    let := hsplit
    let δ := B.d (m : ℤ) (m + 1 : ℕ)
    let p : B.X (m : ℤ) ⟶ B.X (m : ℤ) := 𝟙 _ - δ ≫ section_ δ
    have hp : p ≫ δ = 0 := by
      simp [p, Category.assoc]
    let r := B.liftCycles p (m + 1 : ℕ) (by simp) hp
    have hi : B.iCycles (m : ℤ) ≫ r = 𝟙 _ := by
      apply (cancel_mono (B.iCycles (m : ℤ))).1
      dsimp [r]
      rw [Category.assoc, B.liftCycles_i]
      dsimp [p, δ]
      simp [Preadditive.comp_sub, ← Category.assoc]
    exact ⟨(B.truncLEXIsoCycles m).retract.trans
      { i := B.iCycles (m : ℤ), r := r, retract := hi }⟩
  · have hz := (B.truncLE m).isZero_of_isStrictlyLE m n (by omega)
    exact ⟨{ i := 0, r := 0, retract := hz.eq_of_src _ _ }⟩

/-- One split top differential can be removed without changing homotopy type.

Source: Stacks Project, Tag 068V, explicit split cancellation; Tag 00MT,
contractible identity-pair argument.
(blueprint: lem-pc-split-top-differential-cancellation).

Proof: Let δ = B.d m (m+1) and choose a section σ with σ ≫ δ = 𝟙. Replace the term
in degree m by ker δ, retain the terms below m, and put zero in every degree above
m. Factor the incoming differential through ker δ using d squared = 0. These
maps define a cochain complex D. The inclusion ker δ into B.X m and the identity
in lower degrees define D to B. The endomorphism 𝟙 - δ ≫ σ factors through ker δ
and defines the reverse chain map, zero above m and identity below m. The two
chain-map equations at the changed degrees follow from d squared = 0 and σ ≫ δ = 𝟙.
Their composite on D is the identity. On B, the difference from the identity is
the boundary of the homotopy whose only nonzero component is σ from degree m+1
to degree m. Above m+1 all terms of B are zero by the support hypothesis, so this
homotopy proves the identity in every degree. Thus D is homotopy equivalent to B.
The kernel is a direct summand of B.X m; direct summands preserve flatness,
quasi-coherence and finite presentation (the latter by local finite presentations,
or equivalently the finite-projective criterion on affine opens). Other terms
are unchanged or zero. Since m is natural, replacing the degree m term and
removing higher degrees retains the lower bound zero. The case m = 0 removes
degree one and introduces no negative term; zero terms and the empty scheme
satisfy the same identities. No residue vanishing or affineness is required. -/
theorem exists_split_top_differential_cancellation (S : Scheme.{u})
    (B : CochainComplex S.Modules ℤ) (m : ℕ)
    (hBge : B.IsStrictlyGE 0) (hBle : B.IsStrictlyLE (m + 1 : ℕ))
    (hBflat : ∀ n : ℤ, (B.X n).IsFlatOver (𝟙 S))
    (hBqc : ∀ n : ℤ, (B.X n).IsQuasicoherent)
    (hBfp : ∀ n : ℤ, (B.X n).IsFinitePresentation)
    (hsplit : IsSplitEpi (B.d (m : ℤ) (m + 1 : ℕ))) :
    ∃ D : CochainComplex S.Modules ℤ,
      D.IsStrictlyGE 0 ∧ D.IsStrictlyLE m ∧
      (∀ n : ℤ, (D.X n).IsFlatOver (𝟙 S)) ∧
      (∀ n : ℤ, (D.X n).IsQuasicoherent) ∧
      (∀ n : ℤ, (D.X n).IsFinitePresentation) ∧
      Nonempty (HomotopyEquiv D B) := by
  let D := B.truncLE m
  let := hBge
  have hprops : ∀ n : ℤ, (D.X n).IsFlatOver (𝟙 S) ∧
      (D.X n).IsQuasicoherent ∧ (D.X n).IsFinitePresentation := by
    intro n
    obtain ⟨r⟩ := truncLE_term_retract S B m hsplit n
    exact split_top_differential_cancellation_properties S (D.X n) (B.X n) r
      (hBflat n) (hBqc n) (hBfp n)
  exact ⟨D, inferInstance, inferInstance, fun n ↦ (hprops n).1,
    fun n ↦ (hprops n).2.1, fun n ↦ (hprops n).2.2,
    split_top_differential_cancellation_homotopy S B m hBle hsplit⟩

end AlgebraicGeometry.Scheme.Modules
