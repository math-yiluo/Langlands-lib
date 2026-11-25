/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Homotopy
import WeilConjectures.AlgebraicGeometry.AffineResidueEpiSplitting
import WeilConjectures.AlgebraicGeometry.SplitTopDifferentialCancellation
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic

/-! # Shortening an affine finite-presentation flat complex

Source: Stacks Project, Tags 068V and 08EB, with explicit split cancellation.
(blueprint: lem-pc-affine-finite-presentation-flat-shortening-construction)
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- Cancel the excess top terms of a bounded affine finite-presentation flat complex,
retaining finite presentation and a chain homotopy equivalence to the input.
Source: Stacks Project, Tag 068V (bounded-projective residue criterion), with the
explicit split cancellation argument; affine identification as in Tag 08EB.
(blueprint: lem-pc-affine-finite-presentation-flat-shortening-construction).

Proof: Transport S along its canonical isomorphism to Spec A, A = Γ(S, ⊤).
The affine tilde/global-sections equivalence identifies the quasi-coherent terms
with finitely presented flat A-modules, hence finite projectives. Evaluation is
exact on quasi-coherent modules and takes the complex to a complex P supported
in [0,b]; ordinary residue pullback identifies with tensor with κ(p).
For the current top degree m > d, H^m(P ⊗ κ(p)) is the cokernel of the preceding
differential tensored with κ(p). Its vanishing at every prime implies the finite
cokernel has zero localization everywhere by local Nakayama, hence is zero.
Thus the differential onto the projective P^m splits. Its kernel is a finite
projective direct summand of P^(m-1). Replace P^(m-1) by that kernel and P^m by
zero. The preceding differential lands in the kernel by the complex relation.
The discarded pair is an identity-differential contractible complex; projection
and inclusion, together with its contraction, give a chain homotopy equivalence.
Repeat finitely many times until the top degree is at most d. Every replacement
term remains finite projective, and m-1 ≥ 0 preserves nonnegative support.
Associate sheaves and transport back to S. These additive functors preserve the
homotopies. The resulting terms are flat, quasi-coherent and finitely presented.
If b ≤ d take D = B with the identity equivalence. Over the zero ring every
quasi-coherent term is zero; the same argument gives the zero complex. -/
theorem affine_finitePresentation_flat_shortening_construction (S : Scheme.{u})
    (hS : IsAffine S) (B : CochainComplex S.Modules ℤ) (b d : ℕ)
    (hBge : B.IsStrictlyGE 0) (hBle : B.IsStrictlyLE b)
    (hBflat : ∀ n : ℤ, (B.X n).IsFlatOver (𝟙 S))
    (hBqc : ∀ n : ℤ, (B.X n).IsQuasicoherent)
    (hBfp : ∀ n : ℤ, (B.X n).IsFinitePresentation)
    (hvan : ∀ (s : S) (q : ℕ), d < q →
      IsZero ((((Modules.pullback (S.fromSpecResidueField s)).mapHomologicalComplex _).obj
        B).homology q)) :
    ∃ D : CochainComplex S.Modules ℤ,
      D.IsStrictlyGE 0 ∧ D.IsStrictlyLE d ∧
      (∀ n : ℤ, (D.X n).IsFlatOver (𝟙 S)) ∧
      (∀ n : ℤ, (D.X n).IsQuasicoherent) ∧
      (∀ n : ℤ, (D.X n).IsFinitePresentation) ∧
      Nonempty (HomotopyEquiv D B) := by
  induction b generalizing B with
  | zero =>
    exact ⟨B, hBge, B.isStrictlyLE_of_le 0 d (by omega),
      hBflat, hBqc, hBfp, ⟨HomotopyEquiv.refl B⟩⟩
  | succ b ih =>
    by_cases hbd : b + 1 ≤ d
    · exact ⟨B, hBge, B.isStrictlyLE_of_le (b + 1 : ℕ) d (by omega),
        hBflat, hBqc, hBfp, ⟨HomotopyEquiv.refl B⟩⟩
    · have hsplit : IsSplitEpi (B.d (b : ℤ) (b + 1 : ℕ)) := by
        apply affine_isSplitEpi_of_residue_epi S hS (B.X b) (B.X (b + 1 : ℕ))
          (B.d (b : ℤ) (b + 1 : ℕ)) (hBqc b) (hBqc (b + 1 : ℕ))
          (hBflat (b + 1 : ℕ)) (hBfp (b + 1 : ℕ))
        intro s
        let F := Modules.pullback (S.fromSpecResidueField s)
        let C : CochainComplex (Spec (S.residueField s)).Modules ℤ :=
          (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj B
        have hC : C.IsStrictlyLE (b + 1 : ℕ) := inferInstance
        have hex : C.ExactAt (b + 1 : ℕ) :=
          (C.exactAt_iff_isZero_homology _).mpr (hvan s (b + 1) (by omega))
        have hs : (C.sc' (b : ℤ) (b + 1 : ℕ) ((b : ℤ) + 2)).Exact :=
          (C.exactAt_iff' (b : ℤ) (b + 1 : ℕ) ((b : ℤ) + 2)
            (by simp) (by simp; omega)).mp hex
        exact hs.epi_f ((C.isZero_of_isStrictlyLE (b + 1 : ℕ)
          ((b : ℤ) + 2) (by omega)).eq_of_tgt _ _)
      obtain ⟨B', hB'ge, hB'le, hB'flat, hB'qc, hB'fp, ⟨e⟩⟩ :=
        exists_split_top_differential_cancellation S B b hBge hBle
          hBflat hBqc hBfp hsplit
      have hvan' : ∀ (s : S) (q : ℕ), d < q →
          IsZero ((((Modules.pullback (S.fromSpecResidueField s)).mapHomologicalComplex _).obj
            B').homology q) := by
        intro s q hq
        exact (hvan s q hq).of_iso
          (((Modules.pullback (S.fromSpecResidueField s)).mapHomotopyEquiv e).toHomologyIso q)
      obtain ⟨D, hDge, hDle, hDflat, hDqc, hDfp, ⟨e'⟩⟩ :=
        ih B' hB'ge hB'le hB'flat hB'qc hB'fp hvan'
      exact ⟨D, hDge, hDle, hDflat, hDqc, hDfp, ⟨e'.trans e⟩⟩

end AlgebraicGeometry.Scheme.Modules
