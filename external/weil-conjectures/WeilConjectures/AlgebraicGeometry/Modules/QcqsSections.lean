/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Sections of quasi-coherent modules over basic opens of qcqs opens

Let `M` be a quasi-coherent `𝒪_X`-module, `U` an open of `X` and `f ∈ Γ(X, U)`. We extend the
affine statements `exists_map_eq_pow_smul_of_isAffineOpen` and
`exists_pow_smul_eq_zero_of_isAffineOpen` to quasi-compact (resp. quasi-compact and
quasi-separated) opens `U`, by covering `U` with finitely many affine opens and gluing.
This is the module version of `AlgebraicGeometry.exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated`
(Stacks `01P7`).

## Main statements

- `AlgebraicGeometry.Scheme.Modules.exists_pow_smul_eq_zero_of_isCompact`: for `U`
  quasi-compact, a section over `U` vanishing on `D(f)` is killed by a power of `f`.
- `AlgebraicGeometry.Scheme.Modules.exists_map_eq_pow_smul_of_isCompact_of_isQuasiSeparated`:
  for `U` quasi-compact and quasi-separated, every section over `D(f)` becomes the restriction of
  a section over `U` after multiplication by a power of `f`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- A quasi-compact open is a finite union of affine opens. -/
lemma exists_finite_isAffineOpen_iSup_eq {U : X.Opens} (hU : IsCompact (U : Set X)) :
    ∃ (ι : Type u) (_ : Finite ι) (V : ι → X.Opens), (∀ i, IsAffineOpen (V i)) ∧ iSup V = U := by
  obtain ⟨s, hs', hs⟩ := isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp
    ⟨hU, U.2⟩
  refine ⟨s, hs'.to_subtype, fun i ↦ i.1.1, fun i ↦ i.1.2, ?_⟩
  ext1
  simpa using hs.symm

private lemma map_map_homOfLE (M : X.Modules) {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V)
    (x : Γ(M, U)) :
    M.presheaf.map (homOfLE h₂).op (M.presheaf.map (homOfLE h₁).op x) =
      M.presheaf.map (homOfLE (h₂.trans h₁)).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

private lemma map_map_homOfLE' {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V)
    (x : Γ(X, U)) :
    X.presheaf.map (homOfLE h₂).op (X.presheaf.map (homOfLE h₁).op x) =
      X.presheaf.map (homOfLE (h₂.trans h₁)).op x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

variable (M : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M]

/-- Let `M` be quasi-coherent, `U` a quasi-compact open and `f ∈ Γ(X, U)`. A section of `M` over
`U` whose restriction to `D(f)` vanishes is killed by a power of `f`. -/
theorem exists_pow_smul_eq_zero_of_isCompact {U : X.Opens} (hU : IsCompact (U : Set X))
    (f : Γ(X, U)) (t : Γ(M, U)) (ht : M.presheaf.map (homOfLE (X.basicOpen_le f)).op t = 0) :
    ∃ n : ℕ, f ^ n • t = 0 := by
  obtain ⟨ι, _, V, hV, hVU⟩ := exists_finite_isAffineOpen_iSup_eq hU
  have := Fintype.ofFinite ι
  have hle (i : ι) : V i ≤ U := hVU ▸ le_iSup V i
  have h (i : ι) : ∃ n : ℕ, (X.presheaf.map (homOfLE (hle i)).op f) ^ n •
      M.presheaf.map (homOfLE (hle i)).op t = 0 := by
    refine exists_pow_smul_eq_zero_of_isAffineOpen M (hV i) _ _ ?_
    have hD : X.basicOpen (X.presheaf.map (homOfLE (hle i)).op f) ≤ X.basicOpen f := by
      rw [X.basicOpen_res]
      exact inf_le_right
    rw [map_map_homOfLE, ← map_map_homOfLE M (X.basicOpen_le f) hD, ht, map_zero]
  choose n hn using h
  refine ⟨Finset.univ.sup n, ?_⟩
  let 𝓕 : TopCat.Sheaf Ab X := ⟨M.presheaf, M.isSheaf⟩
  refine 𝓕.eq_of_locally_eq' V U (fun i ↦ homOfLE (hle i)) hVU.ge _ _ fun i ↦ ?_
  change M.presheaf.map _ _ = M.presheaf.map _ _
  rw [map_smul, map_zero, map_pow, ← Nat.sub_add_cancel
    (Finset.le_sup (Finset.mem_univ i) : n i ≤ Finset.univ.sup n), pow_add, mul_smul, hn,
    smul_zero]

/-- Let `M` be quasi-coherent, `U` a quasi-compact and quasi-separated open and `f ∈ Γ(X, U)`.
Every section of `M` over `D(f)` becomes the restriction of a section over `U` after
multiplication by a power of `f`. -/
theorem exists_map_eq_pow_smul_of_isCompact_of_isQuasiSeparated {U : X.Opens}
    (hU : IsCompact (U : Set X)) (hU' : IsQuasiSeparated (U : Set X)) (f : Γ(X, U))
    (s : Γ(M, X.basicOpen f)) :
    ∃ (n : ℕ) (t : Γ(M, U)), M.presheaf.map (homOfLE (X.basicOpen_le f)).op t =
      X.presheaf.map (homOfLE (X.basicOpen_le f)).op f ^ n • s := by
  obtain ⟨ι, _, V, hV, hVU⟩ := exists_finite_isAffineOpen_iSup_eq hU
  have := Fintype.ofFinite ι
  have hle (i : ι) : V i ≤ U := hVU ▸ le_iSup V i
  let fi (i : ι) : Γ(X, V i) := X.presheaf.map (homOfLE (hle i)).op f
  have hD (i : ι) : X.basicOpen (fi i) = V i ⊓ X.basicOpen f := X.basicOpen_res _ _
  have hDf (i : ι) : X.basicOpen (fi i) ≤ X.basicOpen f := (hD i).le.trans inf_le_right
  have hDU (i : ι) : X.basicOpen (fi i) ≤ U := (X.basicOpen_le _).trans (hle i)
  -- restrictions of `f` to the `D(fᵢ)`
  have hfi (i : ι) : X.presheaf.map (homOfLE (X.basicOpen_le (fi i))).op (fi i) =
      X.presheaf.map (homOfLE (hDU i)).op f := map_map_homOfLE' _ _ _
  have hf (i : ι) : X.presheaf.map (homOfLE (hDf i)).op
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f) =
      X.presheaf.map (homOfLE (hDU i)).op f := map_map_homOfLE' _ _ _
  -- Step 1: lift on each affine `V i`.
  have hlift (i : ι) := exists_map_eq_pow_smul_of_isAffineOpen M (hV i) (fi i)
    (M.presheaf.map (homOfLE (hDf i)).op s)
  choose n t ht using hlift
  let N := Finset.univ.sup n
  have hnN (i : ι) : n i ≤ N := Finset.le_sup (Finset.mem_univ i)
  let t' (i : ι) : Γ(M, V i) := fi i ^ (N - n i) • t i
  have ht' (i : ι) : M.presheaf.map (homOfLE (X.basicOpen_le (fi i))).op (t' i) =
      X.presheaf.map (homOfLE (hDU i)).op f ^ N • M.presheaf.map (homOfLE (hDf i)).op s := by
    rw [map_smul, ht, smul_smul, map_pow, ← pow_add, hfi, Nat.sub_add_cancel (hnN i)]
  -- Step 2: on the overlaps, the `t' i` agree after multiplication by a power of `f`.
  have hover (i j : ι) : ∃ m : ℕ,
      X.presheaf.map (homOfLE (inf_le_left.trans (hle i) : V i ⊓ V j ≤ U)).op f ^ m •
        (M.presheaf.map (homOfLE inf_le_left).op (t' i) -
          M.presheaf.map (homOfLE inf_le_right).op (t' j)) = 0 := by
    have hc : IsCompact ((V i ⊓ V j : X.Opens) : Set X) :=
      hU' _ _ (hle i) (V i).2 (hV i).isCompact (hle j) (V j).2 (hV j).isCompact
    refine exists_pow_smul_eq_zero_of_isCompact M hc _ _ ?_
    set g := X.presheaf.map (homOfLE (inf_le_left.trans (hle i) : V i ⊓ V j ≤ U)).op f
    have hg : X.basicOpen g = (V i ⊓ V j) ⊓ X.basicOpen f := X.basicOpen_res _ _
    have hgi : X.basicOpen g ≤ X.basicOpen (fi i) := by
      rw [hg, hD]
      exact inf_le_inf_right _ inf_le_left
    have hgj : X.basicOpen g ≤ X.basicOpen (fi j) := by
      rw [hg, hD]
      exact inf_le_inf_right _ inf_le_right
    have hgf : X.basicOpen g ≤ X.basicOpen f := hg.le.trans inf_le_right
    have key (k : ι) (hgk : X.basicOpen g ≤ X.basicOpen (fi k)) :
        M.presheaf.map (homOfLE (hgk.trans (X.basicOpen_le _))).op (t' k) =
          X.presheaf.map (homOfLE (hgf.trans (X.basicOpen_le f))).op f ^ N •
            M.presheaf.map (homOfLE hgf).op s := by
      rw [← map_map_homOfLE M (X.basicOpen_le _) hgk, ht', map_smul, map_pow,
        map_map_homOfLE', map_map_homOfLE]
    rw [map_sub, map_map_homOfLE, map_map_homOfLE, key i hgi, key j hgj, sub_self]
  choose m hm using hover
  let m' := Finset.univ.sup fun p : ι × ι ↦ m p.1 p.2
  have hmm (i j : ι) : m i j ≤ m' :=
    Finset.le_sup (f := fun p : ι × ι ↦ m p.1 p.2) (Finset.mem_univ (i, j))
  let u (i : ι) : Γ(M, V i) := fi i ^ m' • t' i
  let 𝓕 : TopCat.Sheaf Ab X := ⟨M.presheaf, M.isSheaf⟩
  have hcompat : TopCat.Presheaf.IsCompatible 𝓕.1 V u := by
    intro i j
    rw [← sub_eq_zero]
    change M.presheaf.map (homOfLE inf_le_left).op (u i) -
      M.presheaf.map (homOfLE inf_le_right).op (u j) = 0
    simp only [u, fi, map_smul, map_pow, map_map_homOfLE']
    rw [← smul_sub, ← Nat.sub_add_cancel (hmm i j), pow_add, mul_smul, hm, smul_zero]
  obtain ⟨t₀, ht₀, -⟩ := 𝓕.existsUnique_gluing' V U (fun i ↦ homOfLE (hle i)) hVU.ge u hcompat
  refine ⟨N + m', t₀, ?_⟩
  have hcov : X.basicOpen f ≤ ⨆ i, X.basicOpen (fi i) := by
    intro x hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp
      (show x ∈ iSup V by rw [hVU]; exact X.basicOpen_le f hx)
    exact Opens.mem_iSup.mpr ⟨i, by rw [hD]; exact ⟨hi, hx⟩⟩
  refine 𝓕.eq_of_locally_eq' (fun i ↦ X.basicOpen (fi i)) (X.basicOpen f)
    (fun i ↦ homOfLE (hDf i)) hcov _ _ fun i ↦ ?_
  change M.presheaf.map _ _ = M.presheaf.map _ _
  have hu : M.presheaf.map (homOfLE (hle i)).op t₀ = u i := ht₀ i
  rw [map_map_homOfLE, ← map_map_homOfLE M (hle i) (X.basicOpen_le (fi i)), hu, map_smul,
    map_pow, hfi, ht', map_smul, map_pow, hf, smul_smul, ← pow_add, add_comm m']

/-- A variant of `exists_pow_smul_eq_zero_of_isCompact` for an open `O` equal to `D(f)`. -/
theorem exists_pow_smul_eq_zero_of_isCompact_of_basicOpen_eq {U O : X.Opens}
    (hU : IsCompact (U : Set X)) (f : Γ(X, U)) (hO : X.basicOpen f = O) (hOU : O ≤ U)
    (t : Γ(M, U)) (ht : M.presheaf.map (homOfLE hOU).op t = 0) :
    ∃ n : ℕ, f ^ n • t = 0 := by
  subst hO
  exact exists_pow_smul_eq_zero_of_isCompact M hU f t ht

/-- A variant of `exists_map_eq_pow_smul_of_isCompact_of_isQuasiSeparated` for an open `O` equal
to `D(f)`. -/
theorem exists_map_eq_pow_smul_of_isCompact_of_isQuasiSeparated_of_basicOpen_eq {U O : X.Opens}
    (hU : IsCompact (U : Set X)) (hU' : IsQuasiSeparated (U : Set X)) (f : Γ(X, U))
    (hO : X.basicOpen f = O) (hOU : O ≤ U) (s : Γ(M, O)) :
    ∃ (n : ℕ) (t : Γ(M, U)), M.presheaf.map (homOfLE hOU).op t =
      X.presheaf.map (homOfLE hOU).op f ^ n • s := by
  subst hO
  exact exists_map_eq_pow_smul_of_isCompact_of_isQuasiSeparated M hU hU' f s

end AlgebraicGeometry.Scheme.Modules
