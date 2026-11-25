/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
public import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.SectionNonvanishingZeroLocus

/-! # Restriction-zero sections are killed by a power of an invertible section

Source: Stacks Project, Properties, Lemma 01PW (lemma-invert-s-sections), injectivity.
(blueprint: lem-sc-p1-section-restriction-s-torsion)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- A section vanishing on the nonvanishing open of an invertible section is
annihilated by a tensor power of that section.

Source: Stacks Project, Properties, Lemma 01PW (lemma-invert-s-sections), part (1).
(blueprint: lem-sc-p1-section-restriction-s-torsion)

Proof:
1. By quasi-compactness and local rank-one freeness, choose a finite affine cover
   trivializing `L` (def-weil-pbc-quasi-compact-scheme, def-sc-invertible-module).
   Write `s = f_i e_i` in each trivialization. Nonzero residue-field value is equivalent
   to `f_i` lying outside the point's prime, so `X_s` meets the chart in `D(f_i)`
   (def-weil-residue-field).
2. Quasi-coherence identifies the restricted `F` with the tilde of its section module
   (pqf-def-coherent, lem-weil-pbc-affine-tilde-gamma-adjunction).
   Restriction to `D(f_i)` is localization
   (lem-weil-pbc-spec-module-tilde-sections). Since `t` vanishes there, the localization
   kernel criterion gives `f_i ^ n_i * t_i = 0` for some natural `n_i`
   (def-weil-pbc-module-localization).
3. Take the maximum of the finitely many `n_i` (zero for the empty cover). Multiplication
   by the corresponding tensor power of `s` vanishes on every chart, since in the local
   basis it is multiplication by `f_i ^ m` (def-sc-invertible-module).
   The sheaf property then makes the global tensor-product section zero.
-/
theorem section_restriction_s_torsion
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (L F : X.Modules) [L.IsInvertible] [F.IsQuasicoherent]
    (s : Γ(L, ⊤)) (t : Γ(F, ⊤))
    (X_s : X.Opens) (hXs : (X_s : Set X) = nonvanishingLocus L s)
    (hzero : F.presheaf.map (homOfLE (show X_s ≤ ⊤ from le_top)).op t = 0) :
    ∃ m : ℕ, tmulSection t (tensorPowSectionOne (homOfGlobalSection L s) m ⊤) = 0 := by
  classical
  have : SheafOfModules.IsInvertible.{u, u, u} L :=
    IsInvertible.sheafOfModules_isInvertible L
  let σ := homOfGlobalSection L s
  have hcov (x : X) : ∃ V : X.affineOpens, x ∈ V.1 ∧
      ∃ e : Γ(L, V.1), IsFreeGenerator e := by
    obtain ⟨V, hx, -, he⟩ := exists_isFreeGenerator L (x := x) (W := ⊤) trivial
    exact ⟨V, hx, he⟩
  choose V hxV e he using hcov
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ ((V x).1 : Set X))
    (fun x ↦ (V x).1.isOpen) (fun x _ ↦ Set.mem_iUnion.2 ⟨x, hxV x⟩)
  let ι := {x // x ∈ T}
  let W : ι → X.Opens := fun j ↦ (V j.1).1
  have hW (j : ι) : IsAffineOpen (W j) := (V j.1).2
  have hcover : ⊤ ≤ iSup W := by
    intro x _
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, hi⟩, hxi⟩
  let fc : ∀ j : ι, Γ(X, W j) := fun j ↦
    (he j.1).coeff (σ.app (W j) (unitSectionsEquiv _ 1))
  have hfc (j : ι) : σ.app (W j) (unitSectionsEquiv _ 1) = fc j • e j.1 :=
    ((he j.1).coeff_smul _).symm
  have hXs' : (Hom.zeroLocus σ).support.compl = X_s := by
    ext x
    exact Set.ext_iff.mp
      ((nonvanishingLocus_eq_compl_support_zeroLocus X L s).symm.trans hXs.symm) x
  have hD (j : ι) : X.basicOpen (fc j) = W j ⊓ X_s := by
    rw [← hXs']
    exact basicOpen_coeff_eq σ (V j.1) (he j.1)
  have hDle (j : ι) : X.basicOpen (fc j) ≤ X_s := (hD j).le.trans inf_le_right
  have hz (j : ι) : F.presheaf.map (homOfLE (X.basicOpen_le (fc j))).op
      (F.presheaf.map (homOfLE (le_top : W j ≤ ⊤)).op t) = 0 := by
    have h := congrArg (F.presheaf.map (homOfLE (hDle j)).op) hzero
    rw [map_zero] at h
    simpa only [← Functor.map_comp_apply, ← op_comp, homOfLE_comp] using h
  have hlocal (j : ι) := exists_pow_smul_eq_zero_of_isAffineOpen F (hW j) (fc j)
    (F.presheaf.map (homOfLE (le_top : W j ≤ ⊤)).op t) (hz j)
  choose n hn using hlocal
  let m := Finset.univ.sup n
  have hnm (j : ι) : n j ≤ m := Finset.le_sup (Finset.mem_univ j)
  refine ⟨m, ?_⟩
  let G : TopCat.Sheaf AddCommGrpCat X :=
    ⟨(tensorObj F (L.tensorPow m)).presheaf, (tensorObj F (L.tensorPow m)).isSheaf⟩
  apply G.eq_of_locally_eq' W ⊤ (fun _ ↦ homOfLE le_top) hcover
  intro j
  change (tensorObj F (L.tensorPow m)).presheaf.map (homOfLE (le_top : W j ≤ ⊤)).op _ =
    (tensorObj F (L.tensorPow m)).presheaf.map (homOfLE (le_top : W j ≤ ⊤)).op 0
  obtain ⟨E, -, hE⟩ := exists_tensorPowSectionOne_eq_pow_smul σ (he j.1) (hfc j) m
  rw [map_zero, tmulSection_map, presheaf_map_tensorPowSectionOne, hE,
    tmulSection_smul, ← smul_tmulSection]
  have hkill : fc j ^ m •
      F.presheaf.map (homOfLE (le_top : W j ≤ ⊤)).op t = 0 := by
    rw [← Nat.sub_add_cancel (hnm j), pow_add, mul_smul, hn, smul_zero]
  rw [hkill, zero_tmulSection]

end AlgebraicGeometry.Scheme.Modules
