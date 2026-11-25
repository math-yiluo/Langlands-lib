/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.Modules.FreeComplex

/-! # Openness of the finite free residue locus

Source: blueprint lemma-coherent-base-change-invertible-sheaves--3, proof steps 1--3.
(blueprint: lem-pc-finite-free-residue-locus-open)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

private theorem exists_residue_rank_le {Y : Scheme.{u}}
    {m n : Type u} [Finite m] [Fintype n] (A : Matrix m n Γ(Y, ⊤)) (y : Y) :
    ∃ V : Y.Opens, y ∈ V ∧ ∀ z ∈ V,
      (A.map (Y.fromSpecResidueField y).appTop).rank ≤
        (A.map (Y.fromSpecResidueField z).appTop).rank := by
  let g := Y.fromSpecResidueField y
  have hΓ := isField_Γ_Spec (Field.toIsField (Y.residueField y))
  obtain ⟨x⟩ : Nonempty (Spec (Y.residueField y)) := inferInstance
  have hx : g.base x = y := (Scheme.range_fromSpecResidueField y).subset ⟨x, rfl⟩
  obtain ⟨a, b, hab⟩ := (le_rank_map_appTop_iff hΓ g x A _).mp le_rfl
  refine ⟨Y.basicOpen (A.submatrix a b).det, by simpa [hx] using hab, ?_⟩
  intro z hz
  obtain ⟨xz⟩ : Nonempty (Spec (Y.residueField z)) := inferInstance
  apply (le_rank_map_appTop_iff (isField_Γ_Spec (Field.toIsField (Y.residueField z)))
    (Y.fromSpecResidueField z) xz A _).mpr
  refine ⟨a, b, ?_⟩
  have hxz : (Y.fromSpecResidueField z).base xz = z :=
    (Scheme.range_fromSpecResidueField z).subset ⟨xz, rfl⟩
  simpa only [hxz] using hz

/-- The points where a bounded nonnegative finite free complex has residue cohomology
concentrated in degree i with rank r form an open set.

Source: blueprint lemma-coherent-base-change-invertible-sheaves--3, proof steps 1--3.
(blueprint: lem-pc-finite-free-residue-locus-open).

Proof: choose bases of the finite free terms. At a field-valued point write β(q) for
cohomology dimension and ρ(q) for the rank of the outgoing differential. Rank-nullity
gives β(q) + ρ(q) + ρ(q-1) = rank(P.X q). A maximal nonzero minor of each differential
remains nonzero on a basic open, so differential ranks cannot decrease nearby. This
also gives the existing upper-semicontinuity bound for β(q).
At a point of the indicated locus choose the finitely many upper-semicontinuity
neighbourhoods for q = 0,...,d; outside this interval the terms and homology vanish.
Thus cohomology outside i stays zero on their intersection. Also choose basic opens
on which the four differential ranks in degrees i-2,...,i+1 cannot decrease.
The displayed rank-nullity identities in degrees i-1 and i+1, whose original β is
zero, force each of their differential ranks to remain equal to its original value.
The identity in degree i now forces β(i) to remain r. Finite-dimensional modules on
the spectrum of a field are zero exactly when dimension is zero and are locally free
of rank r exactly when dimension is r. The resulting finite intersection is an open
neighbourhood contained in the locus. Negative degrees in this argument are handled
by the lower support bound, including i = 0; the upper support bound handles i > d.
No point is chosen when the scheme is empty. -/
theorem isOpen_finiteFree_residue_locus
    {Y : Scheme.{u}} (P : CochainComplex Y.Modules ℤ) (d : ℕ)
    (hge : P.IsStrictlyGE 0) (hle : P.IsStrictlyLE d)
    (hfree : ∀ n : ℤ, ∃ s : ℕ, Nonempty
      (P.X n ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s))))
    (i r : ℕ) :
    IsOpen {y : Y | ((∀ q : ℕ, q ≠ i → IsZero
          ((((Modules.pullback (Y.fromSpecResidueField y)).mapHomologicalComplex _).obj
            P).homology q)) ∧
        ((((Modules.pullback (Y.fromSpecResidueField y)).mapHomologicalComplex _).obj
          P).homology i).IsFiniteLocallyFreeOfRank r)} := by
  classical
  let β (y : Y) (q : ℤ) := Module.finrank (Y.residueField y)
    ((moduleSpecΓFunctor (R := Y.residueField y)).obj
      ((((Modules.pullback (Y.fromSpecResidueField y)).mapHomologicalComplex _).obj P).homology q))
  have hfin (y : Y) (q : ℤ) := finite_moduleSpecΓFunctor_obj_homology_pullback
    hfree (Field.toIsField (Y.residueField y)) (Y.fromSpecResidueField y) q
  have hz (y : Y) (q : ℤ) (hq : q < 0 ∨ (d : ℤ) < q) : β y q = 0 := by
    apply (isZero_iff_finrank_moduleSpecΓFunctor_obj_eq_zero
      (Field.toIsField (Y.residueField y)) _).mp
    have hX : IsZero (P.X q) := by
      rcases hq with hq | hq
      · have := hge
        exact P.isZero_of_isStrictlyGE 0 q
      · have := hle
        exact P.isZero_of_isStrictlyLE d q
    exact ShortComplex.isZero_homology_of_isZero_X₂ _
      ((Modules.pullback (Y.fromSpecResidueField y)).map_isZero hX)
  have hfree' := hfree
  choose ranks he using hfree'
  let e (n : ℤ) := (he n).some
  let A (n : ℤ) := freeMatrix
    ((e n).inv ≫ P.d n (n + 1) ≫ (e (n + 1)).hom)
  let ρ (y : Y) (n : ℤ) := (A n |>.map (Y.fromSpecResidueField y).appTop).rank
  have hform (y : Y) (n : ℤ) : β y n + ρ y n + ρ y (n - 1) = ranks n := by
    have hh : n - 1 + 1 = n := by omega
    dsimp only [β, ρ, A]
    rw [hh]
    exact finrank_homology_pullback_add_rank_add_rank e
      (Field.toIsField (Y.residueField y)) (Y.fromSpecResidueField y) n
  apply isOpen_iff_forall_mem_open.mpr
  intro y hy
  have hyzero (q : ℤ) (hq : q ≠ (i : ℤ)) : β y q = 0 := by
    by_cases hqneg : q < 0
    · exact hz y q (Or.inl hqneg)
    · have hnat : (q.toNat : ℤ) = q := Int.toNat_of_nonneg (by omega)
      have hn : q.toNat ≠ i := by omega
      have h := (isZero_iff_finrank_moduleSpecΓFunctor_obj_eq_zero
        (Field.toIsField (Y.residueField y)) _).mp (hy.1 q.toNat hn)
      change β y (q.toNat : ℤ) = 0 at h
      rwa [hnat] at h
  have hyi : β y i = r := (isFiniteLocallyFreeOfRank_iff_finrank_moduleSpecΓFunctor_obj
    (Field.toIsField (Y.residueField y)) _ r).mp hy.2
  have hV (q : Fin (d + 1)) : ∃ V : Y.Opens, y ∈ V ∧ ∀ z ∈ V, β z q ≤ β y q := by
    obtain ⟨V, hyV, hV⟩ := exists_finrank_homology_pullback_le hfree (q : ℤ)
      (Field.toIsField (Y.residueField y)) (Y.fromSpecResidueField y)
    refine ⟨V, ?_, fun z hzV ↦ hV (Field.toIsField (Y.residueField z))
      (Y.fromSpecResidueField z) ?_⟩
    · obtain ⟨x⟩ : Nonempty (Spec (Y.residueField y)) := inferInstance
      have hx : (Y.fromSpecResidueField y).base x = y :=
        (Scheme.range_fromSpecResidueField y).subset ⟨x, rfl⟩
      simpa only [SetLike.mem_coe, hx] using hyV ⟨x, rfl⟩
    · rw [Scheme.range_fromSpecResidueField]
      simpa using hzV
  choose V hyV hV using hV
  have hW (q : Fin 4) : ∃ W : Y.Opens, y ∈ W ∧ ∀ z ∈ W,
      ρ y ((i : ℤ) + q - 2) ≤ ρ z ((i : ℤ) + q - 2) :=
    exists_residue_rank_le (A ((i : ℤ) + q - 2)) y
  choose W hyW hW using hW
  let O : Y.Opens := (⨅ q, V q) ⊓ (⨅ q, W q)
  refine ⟨O, ?_, O.isOpen, ?_⟩
  · intro z hzO
    have hv : ∀ q, z ∈ V q := by
      simpa only [← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf,
        Set.mem_iInter] using hzO.1
    have hw : ∀ q, z ∈ W q := by
      simpa only [← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf,
        Set.mem_iInter] using hzO.2
    have hl0 : ρ y ((i : ℤ) - 2) ≤ ρ z ((i : ℤ) - 2) := by
      simpa using hW (0 : Fin 4) z (hw _)
    have hl1 : ρ y ((i : ℤ) - 1) ≤ ρ z ((i : ℤ) - 1) := by
      convert hW (1 : Fin 4) z (hw _) using 1 <;> congr 1 <;> norm_num <;> omega
    have hl2 : ρ y i ≤ ρ z i := by
      simpa using hW (2 : Fin 4) z (hw _)
    have hl3 : ρ y ((i : ℤ) + 1) ≤ ρ z ((i : ℤ) + 1) := by
      convert hW (3 : Fin 4) z (hw _) using 1 <;> congr 1 <;> norm_num <;> omega
    have hf0 := hform y ((i : ℤ) - 1)
    have hf1 := hform z ((i : ℤ) - 1)
    have hf2 := hform y ((i : ℤ) + 1)
    have hf3 := hform z ((i : ℤ) + 1)
    have hf4 := hform y i
    have hf5 := hform z i
    have hzero0 := hyzero ((i : ℤ) - 1) (by omega)
    have hzero1 := hyzero ((i : ℤ) + 1) (by omega)
    have hzi : β z i = r := by
      have hm : (i : ℤ) - 1 - 1 = i - 2 := by omega
      have hp : (i : ℤ) + 1 - 1 = i := by omega
      rw [hm] at hf0 hf1
      rw [hp] at hf2 hf3
      omega
    constructor
    · intro q hq
      apply (isZero_iff_finrank_moduleSpecΓFunctor_obj_eq_zero
        (Field.toIsField (Y.residueField z)) _).mpr
      by_cases hqd : d < q
      · exact hz z q (Or.inr (by omega))
      · have hb := hV ⟨q, by omega⟩ z (hv _)
        have hzero := hyzero q (by omega)
        change β z q = 0
        simpa only [Fin.val_mk, hzero, Nat.le_zero] using hb
    · exact (isFiniteLocallyFreeOfRank_iff_finrank_moduleSpecΓFunctor_obj
        (Field.toIsField (Y.residueField z)) _ r).mpr hzi
  · change y ∈ ((⨅ q, V q) ⊓ (⨅ q, W q) : Y.Opens)
    simpa only [← SetLike.mem_coe, TopologicalSpace.Opens.coe_inf, Set.mem_inter_iff,
      TopologicalSpace.Opens.coe_iInf, Set.mem_iInter] using And.intro hyV hyW

end AlgebraicGeometry.Scheme.Modules
