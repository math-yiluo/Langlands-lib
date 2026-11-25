/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.ChowLemma
import WeilConjectures.AlgebraicGeometry.ProjectiveSpaceFiniteCoordinates
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Chow's lemma over a quasi-compact quasi-separated base

Source: Stacks Project, Lemma Tag 0202 (blueprint: `lem-weil-pbc-chow-finite-type`).

## Main statements

* `exists_chow_finite_type` states Chow's lemma for a separated finite type
  morphism over a quasi-compact quasi-separated scheme.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- Chow's lemma for a separated morphism of finite type over a quasi-compact
quasi-separated base (Stacks Project, Tag 0202; (blueprint:
theorem-chow-s-lemma-projective-form--3)): there are `n`, a proper surjective `π : X' ⟶ X` and an
immersion `j : X' ⟶ ℙⁿ_S` over `S`.

Proof sketch: by Stacks 01ZJ, `f` factors as a closed immersion `i : X ⟶ Y` followed by a
separated morphism `g : Y ⟶ S` of finite presentation; a solution for `g` pulls back along `i`
to one for `f` (proper, surjective and closed immersions are stable under base change). Write
`S` as a limit of Noetherian schemes `S_j` of finite type over `ℤ` with affine transition maps
(01ZA), descend `g` to a finitely presented `g_j : Y_j ⟶ S_j` (01ZM), separated for large `j`
(01ZQ), apply Chow's lemma over the Noetherian `S_j` (0200), and base change the resulting
proper surjective `π_j` and immersion `ι : Y'_j ⟶ ℙⁿ_{S_j}` back to `S`, using
`ℙⁿ_{S_j} ×_{S_j} S ≅ ℙⁿ_S`. -/
theorem exists_chow_finite_type {S X : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (n : ℕ) (X' : Scheme.{u}) (π : X' ⟶ X)
      (j : X' ⟶ ProjectiveSpace (ULift.{u} (Fin (n + 1))) S),
      IsProper π ∧ Surjective π ∧ IsImmersion j ∧
        j ≫ ProjectiveSpace (ULift.{u} (Fin (n + 1))) S ↘ S = π ≫ f := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨Y, i, g, hi, hgfp, hgqc, hgsep, hif⟩ :=
    f.exists_isClosedImmersion_isSeparated_locallyOfFinitePresentation
  obtain ⟨A⟩ := S.nonempty_noetherianApproximation
  obtain ⟨a, Y₀, g₀, hg₀fp, hg₀qc, hg₀sep, h, H⟩ :=
    Scheme.exists_isPullback_of_finitePresentation_of_isSeparated A.isLimit g
  let π₀ := ChowModification.modificationMap g₀
  let j₀ := ChowModification.toProjectiveSpace g₀
  have H' : IsPullback (pullback.fst π₀ h) (pullback.snd π₀ h ≫ g)
      (j₀ ≫ ℙ(ChowModification.index g₀; A.D.obj a) ↘ A.D.obj a) (A.π.app a) := by
    rw [ChowModification.toProjectiveSpace_over]
    exact (IsPullback.of_hasPullback π₀ h).paste_vert H
  have hw : (pullback.snd π₀ h ≫ g) ≫ A.π.app a =
      (pullback.fst π₀ h ≫ j₀) ≫
        ℙ(ChowModification.index g₀; A.D.obj a) ↘ A.D.obj a :=
    H'.w.symm.trans (by simp)
  let jY := ProjectiveSpace.liftBaseChange _ _ hw
  have : IsImmersion jY :=
    MorphismProperty.of_isPullback (ProjectiveSpace.isPullback_liftBaseChange _ H' hw)
      inferInstance
  let π := pullback.snd (pullback.snd π₀ h) i
  let j := pullback.fst (pullback.snd π₀ h) i ≫ jY
  have hj : IsImmersion j := inferInstance
  have hπ : IsProper π := inferInstance
  have hπs : Surjective π := inferInstance
  have hjover : j ≫ ℙ(ChowModification.index g₀; S) ↘ S = π ≫ f := by
    simp only [j, π, jY, Category.assoc, ProjectiveSpace.liftBaseChange_over]
    rw [pullback.condition_assoc, hif]
  obtain ⟨n, k, hk, hkover⟩ :=
    ProjectiveSpace.exists_isClosedImmersion_finite_coordinates (ChowModification.index g₀) S
  refine ⟨n, pullback (pullback.snd π₀ h) i, π, j ≫ k,
    hπ, hπs, inferInstance, ?_⟩
  rw [Category.assoc, hkover, hjover]

end AlgebraicGeometry
