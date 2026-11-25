/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.FiniteFreeComplex
public import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Exactness of a finite free complex from its fibres

Let `P` be a bounded complex of finite free `𝒪_Y`-modules and `q` an integer. If at every point
`y` of `Y` the fibre `P ⊗ κ(y)` is exact in degree `q`, then `P` is exact in degree `q`
(`IsFiniteFreeComplex.isZero_homology_of_isZero_homology_pullback`):
exactness of the fibre is a rank condition on the matrices of the differentials, under which
they split near `y` (`AlgebraicGeometry.Scheme.exists_opens_split_of_rank_add_eq`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

open SheafOfModules

variable {Y : Scheme.{u}}

/-- **Ranks at a field point from exactness.** Let `P` be a complex of free `𝒪_Y`-modules of
finite rank, with matrices `C` of the differentials, and `g : Z ⟶ Y` a morphism from a scheme with
a field of global sections and a point whose only open neighbourhood is `Z` (for instance the
spectrum of a field). If `g^* P` is exact in degree `q`, then
`rank C_{q-1}(g) + rank C_q(g) = rank P^q`. -/
theorem rank_add_rank_eq_card_of_isZero_homology_pullback {Z : Scheme.{u}}
    (hZ : IsField Γ(Z, ⊤)) {z : Z} (hz : ∀ W : Z.Opens, z ∈ W → W = ⊤) (g : Z ⟶ Y)
    (P : CochainComplex Y.Modules ℤ) {ι : ℤ → Type u} [∀ n, Fintype (ι n)]
    [∀ n, DecidableEq (ι n)] (e : ∀ n, P.X n ≅ free (R := Y.ringCatSheaf) (ι n)) (q : ℤ)
    (h : IsZero ((((Modules.pullback g).mapHomologicalComplex _).obj P).homology q)) :
    ((freeMatrix ((e (q - 1)).inv ≫ P.d (q - 1) q ≫ (e q).hom)).map g.appTop).rank +
      ((freeMatrix ((e q).inv ≫ P.d q (q + 1) ≫ (e (q + 1)).hom)).map g.appTop).rank =
        Fintype.card (ι q) := by
  let E (n : ℤ) := (Modules.pullback g).mapIso (e n) ≪≫ pullbackFreeIso g (ι n)
  set Q := ((Modules.pullback g).mapHomologicalComplex _).obj P
  have hm (n m : ℤ) : freeMatrix ((E n).inv ≫ Q.d n m ≫ (E m).hom) =
      (freeMatrix ((e n).inv ≫ P.d n m ≫ (e m).hom)).map g.appTop :=
    freeMatrix_pullback_d g P (e n) (e m)
  let := hZ.toField
  rw [← hm, ← hm]
  refine Matrix.rank_add_rank_eq_card_of_exact _ _ ?_ fun v hv ↦ ?_
  · rw [← freeMatrix_comp]
    simp
  · obtain ⟨V, hV⟩ := exists_freeMatrix_mul_eq_of_isZero_homology E hz q h PUnit
      (Matrix.replicateCol PUnit v) (by rw [← Matrix.replicateCol_mulVec, hv]; ext; simp)
    refine ⟨fun j ↦ V j PUnit.unit, funext fun i ↦ ?_⟩
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using
      congrFun (congrFun hV i) PUnit.unit

/-- **A finite free complex with exact fibres is exact.** Let `P` be a bounded complex of finite
free `𝒪_Y`-modules and `q` an integer. If every point `y` of `Y` is the image of a field point
`g : Spec K ⟶ Y` such that `g^* P` is exact in degree `q`, then `P` is exact in degree `q`. -/
theorem IsFiniteFreeComplex.isZero_homology_of_isZero_homology_pullback
    {P : CochainComplex Y.Modules ℤ} {d : ℕ} (hP : IsFiniteFreeComplex P d) (q : ℤ)
    (h : ∀ y : Y, ∃ (R : CommRingCat.{u}) (_ : IsField R) (g : Spec R ⟶ Y) (x : Spec R),
      g x = y ∧ IsZero ((((Modules.pullback g).mapHomologicalComplex _).obj P).homology q)) :
    IsZero (P.homology q) := by
  classical
  obtain ⟨rk, -, ⟨e⟩⟩ := hP.exists_iso_free_of_rank_eq_zero
  set C : ∀ n m : ℤ, Matrix (ULift.{u} (Fin (rk m))) (ULift.{u} (Fin (rk n))) Γ(Y, ⊤) :=
    fun n m ↦ freeMatrix ((e n).inv ≫ P.d n m ≫ (e m).hom) with hCdef
  have hC (n m l : ℤ) : C m l * C n m = 0 := by
    simp only [hCdef]
    rw [← freeMatrix_comp]
    simp
  -- the rank condition in degree `q` at every point
  have hrank (y : Y) : ((C (q - 1) q).map (Y.fromSpecResidueField y).appTop).rank +
      ((C q (q + 1)).map (Y.fromSpecResidueField y).appTop).rank =
        Fintype.card (ULift.{u} (Fin (rk q))) := by
    obtain ⟨R, hR, g, x, hgx, hg⟩ := h y
    have hx (W : (Spec R).Opens) (hW : x ∈ W) : W = ⊤ := by
      let := hR.toField
      have : Subsingleton (Spec R) := inferInstanceAs (Subsingleton (PrimeSpectrum R))
      refine eq_top_iff.2 fun x' _ ↦ ?_
      rwa [Subsingleton.elim x' x]
    obtain ⟨p⟩ : Nonempty (Spec (Y.residueField y)) := inferInstance
    rw [rank_map_appTop_eq_of_base_eq (isField_Γ_Spec_residueField y) (isField_Γ_Spec hR) _ g p x
        (by rw [Scheme.fromSpecResidueField_apply, hgx]),
      rank_map_appTop_eq_of_base_eq (isField_Γ_Spec_residueField y) (isField_Γ_Spec hR) _ g p x
        (by rw [Scheme.fromSpecResidueField_apply, hgx])]
    exact rank_add_rank_eq_card_of_isZero_homology_pullback (isField_Γ_Spec hR) hx g P e q hg
  -- near every point the complex splits in degree `q`
  choose W hyW hW using fun y ↦ Scheme.exists_opens_split_of_rank_add_eq _ _ (hC _ _ _) y
    (hrank y)
  have hWtop : ⨆ y, W y = ⊤ :=
    eq_top_iff.2 fun y _ ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨y, hyW y⟩
  refine isZero_of_iSup_eq_top _ W hWtop fun y ↦ ?_
  set j := (W y).ι
  obtain ⟨L₁, M₁, L₁', M₁', L₂, M₂, L₂', M₂', s₁, s₂, s⟩ := hW y j (by rw [Opens.range_ι])
  obtain ⟨I, Pm, σ, τ, h₁, h₂, h₃, h₄⟩ :=
    (Matrix.hasSplitHomology_of_add_eq_one (k := Fin 0) s₁ s₂ s).of_equiv Equiv.ulift.symm
  let E (n : ℤ) := (Modules.pullback j).mapIso (e n) ≪≫ pullbackFreeIso j (ULift.{u} (Fin (rk n)))
  obtain ⟨φ⟩ := nonempty_homology_iso_free_of_split
    (((Modules.pullback j).mapHomologicalComplex _).obj P) q (E (q - 1)) (E q) (E (q + 1))
    σ τ I Pm h₁ (by rw [freeMatrix_pullback_d]; exact h₂) (by rw [freeMatrix_pullback_d]; exact h₃)
    (by rw [freeMatrix_pullback_d, freeMatrix_pullback_d]; exact h₄)
  exact (isZero_free_of_isEmpty _).of_iso ((restrictFunctorIsoPullback j).app _ ≪≫
    ((P.sc q).mapHomologyIso (Modules.pullback j)).symm ≪≫ φ)

end AlgebraicGeometry.Scheme.Modules
