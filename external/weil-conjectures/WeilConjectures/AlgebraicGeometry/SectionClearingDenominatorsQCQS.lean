/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
public import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.SectionNonvanishingZeroLocus
import WeilConjectures.AlgebraicGeometry.Modules.QcqsSections

/-! # Clearing denominators of sections on a nonvanishing locus

Source: Stacks Project, Properties, Lemma 01PW, proof of part (2)
(blueprint: lem-sc-p1-section-clearing-denominators-qcqs).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- On a quasi-compact and quasi-separated scheme, sections on the nonvanishing locus of a
section of an invertible module become restrictions of global sections after a tensor power.
Here `U` is an open with underlying set `X_s = nonvanishingLocus L s` and the right side is
`t ⊗ (s|_U)^{⊗ m}`.
Source: Stacks Project, Properties, Lemma 01PW, proof of part (2)
(blueprint: lem-sc-p1-section-clearing-denominators-qcqs).

Proof:
1. Using `def-sc-invertible-module` and `pqf-def-coherent`, choose affine neighbourhoods
   with a basis for `L` and a module presentation for `F`. Refine their intersections by
   principal opens; `lem-weil-pbc-spec-module-tilde-sections` preserves the presentations.
   By `def-weil-pbc-quasi-compact-scheme`, take a finite cover `Vᵢ = Spec Aᵢ`. Write
   `s = fᵢ eᵢ` on each chart. Its residue-field value is nonzero precisely on `D(fᵢ)`.
   The same affine-sections lemma identifies sections there with localized modules.
   Write the given section locally as `vᵢ / fᵢ ^ aᵢ`, take a common exponent `a`, and
   form `wᵢ = fᵢ ^ (a - aᵢ) vᵢ ⊗ eᵢ ^ a`. Its restriction is the given section times
   `s ^ a`.
2. Quasi-separatedness makes each overlap `Wᵢⱼ = Vᵢ ∩ Vⱼ` quasi-compact.
   The difference of the two local lifts vanishes on `Wᵢⱼ ∩ X_s`. The basis of
   `L ^ a` on `Vᵢ` identifies this difference with a section of `F` on `Wᵢⱼ`.
   Its restriction to `D(fᵢ|_{Wᵢⱼ})` is zero, by injectivity of tensoring with
   the restricted basis. Apply `exists_pow_smul_eq_zero_of_isCompact` to this
   section of `F`: a power of `fᵢ` kills it, hence also the original difference.
3. Take a common exponent `b` for the finitely many pairs. After multiplying each lift
   by `s ^ b` and identifying the tensor powers, the resulting sections agree on every
   overlap. Glue them by the sheaf axiom to a global section of `F ⊗ L ^ (a + b)`.
   On the principal opens covering `X_s` it equals the given section times `s ^ (a + b)`.
   Thus `m = a + b` has the required property.
-/
theorem exists_tensorPowSection_eq_restrict_qcqs [CompactSpace X]
    [QuasiSeparatedSpace X] (L : X.Modules) [L.IsInvertible]
    (s : Γ(L, ⊤)) (F : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F]
    (U : X.Opens) (hU : (U : Set X) = nonvanishingLocus L s) (t : Γ(F, U)) :
    ∃ (m : ℕ) (u : Γ(F ⊗ L.tensorPow m, ⊤)),
      (F ⊗ L.tensorPow m).presheaf.map (homOfLE le_top).op u =
        tmulSection t (tensorPowSectionOne (homOfGlobalSection L s) m U) := by
  classical
  have := IsInvertible.sheafOfModules_isInvertible L
  let σ := homOfGlobalSection L s
  have hXs : (Hom.zeroLocus σ).support.compl = U := by
    apply SetLike.coe_injective
    exact (nonvanishingLocus_eq_compl_support_zeroLocus X L s).symm.trans hU.symm
  have hcov (x : X) : ∃ V : X.affineOpens, x ∈ V.1 ∧ ∃ e : Γ(L, V.1), IsFreeGenerator e := by
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
  let fc : ∀ j : ι, Γ(X, W j) := fun j ↦ (he j.1).coeff (σ.app (W j) (unitSectionsEquiv _ 1))
  have hfc (j : ι) : σ.app (W j) (unitSectionsEquiv _ 1) = fc j • e j.1 :=
    ((he j.1).coeff_smul _).symm
  have hD (j : ι) : X.basicOpen (fc j) = W j ⊓ U := by
    rw [← hXs]
    exact basicOpen_coeff_eq σ (V j.1) (he j.1)
  have hDle (j : ι) : X.basicOpen (fc j) ≤ U := (hD j).le.trans inf_le_right
  -- Step 1: lift `t` on each `D(f_j)` to `W j` after multiplying by a power of `f_j`.
  have hlift (j : ι) := exists_map_eq_pow_smul_of_isAffineOpen F (hW j) (fc j)
    (F.presheaf.map (homOfLE (hDle j)).op t)
  choose n t₀ ht₀ using hlift
  let a := Finset.univ.sup n
  have hna (j : ι) : n j ≤ a := Finset.le_sup (Finset.mem_univ j)
  let t₁ : ∀ j : ι, Γ(F, W j) := fun j ↦ fc j ^ (a - n j) • t₀ j
  have ht₁ (j : ι) : F.presheaf.map (homOfLE (X.basicOpen_le (fc j))).op (t₁ j) =
      X.presheaf.map (homOfLE (X.basicOpen_le (fc j))).op (fc j) ^ a •
        F.presheaf.map (homOfLE (hDle j)).op t := by
    rw [map_smul, ht₀, smul_smul, map_pow, ← pow_add, Nat.sub_add_cancel (hna j)]
  choose E hE hE' using fun (j : ι) (m : ℕ) ↦
    exists_tensorPowSectionOne_eq_pow_smul σ (he j.1) (hfc j) m
  let u₁ : ∀ j : ι, Γ(F ⊗ L.tensorPow a, W j) := fun j ↦ tmulSection (t₁ j) (E j a)
  have hu₁ (j : ι) {P : X.Opens} (hP : P ≤ X.basicOpen (fc j)) :
      (F ⊗ L.tensorPow a).presheaf.map (homOfLE (hP.trans (X.basicOpen_le _))).op (u₁ j) =
        tmulSection (F.presheaf.map (homOfLE (hP.trans (hDle j))).op t)
          (tensorPowSectionOne σ a P) := by
    rw [tmulSection_map, ← presheaf_map_homOfLE_map_homOfLE (X.basicOpen_le (fc j)) hP (t₁ j), ht₁,
      map_smul, map_pow, presheaf_map_homOfLE_map_homOfLE,
      ← presheaf_map_tensorPowSectionOne σ a (homOfLE (hP.trans (X.basicOpen_le _))), hE',
      map_smul, map_pow, tmulSection_smul, smul_tmulSection, Scheme.presheaf_map_map_apply]
    rfl
  -- Step 2: on overlaps, the `u₁ j` agree after multiplication by a power of `f_j`.
  have hover (j k : ι) : ∃ b : ℕ,
      X.presheaf.map (homOfLE (inf_le_left : W j ⊓ W k ≤ W j)).op (fc j) ^ b •
        ((F ⊗ L.tensorPow a).presheaf.map (homOfLE inf_le_left).op (u₁ j) -
          (F ⊗ L.tensorPow a).presheaf.map (homOfLE inf_le_right).op (u₁ k)) = 0 := by
    set g := X.presheaf.map (homOfLE (inf_le_left : W j ⊓ W k ≤ W j)).op (fc j)
    set d := (F ⊗ L.tensorPow a).presheaf.map (homOfLE inf_le_left).op (u₁ j) -
      (F ⊗ L.tensorPow a).presheaf.map (homOfLE inf_le_right).op (u₁ k)
    have hg : X.basicOpen g = (W j ⊓ W k) ⊓ X.basicOpen (fc j) := X.basicOpen_res _ _
    have hPj : X.basicOpen g ≤ X.basicOpen (fc j) := hg.le.trans inf_le_right
    have hPk : X.basicOpen g ≤ X.basicOpen (fc k) := by
      rw [hD k]
      refine le_inf ((X.basicOpen_le g).trans inf_le_right) (hPj.trans (hDle j))
    have hd0 : (F ⊗ L.tensorPow a).presheaf.map (homOfLE (X.basicOpen_le g)).op d = 0 := by
      rw [map_sub, presheaf_map_homOfLE_map_homOfLE, presheaf_map_homOfLE_map_homOfLE, hu₁ j hPj,
        hu₁ k hPk]
      exact sub_self _
    obtain ⟨d', hd'⟩ := ((hE j a).bijective_tmulSection_right
      (inf_le_left : W j ⊓ W k ≤ W j)).2 d
    dsimp only at hd'
    have hd'0 : F.presheaf.map (homOfLE (X.basicOpen_le g)).op d' = 0 := by
      apply ((hE j a).bijective_tmulSection_right ((X.basicOpen_le g).trans inf_le_left)).1
      dsimp only
      rw [zero_tmulSection, ← presheaf_map_homOfLE_map_homOfLE inf_le_left (X.basicOpen_le g),
        ← tmulSection_map, hd', hd0]
    obtain ⟨b, hb⟩ := exists_pow_smul_eq_zero_of_isCompact F
      (QuasiSeparatedSpace.inter_isCompact (W j : Set X) (W k : Set X)
        (W j).isOpen (hW j).isCompact (W k).isOpen (hW k).isCompact) g d' hd'0
    refine ⟨b, ?_⟩
    rw [← hd', ← smul_tmulSection, hb, zero_tmulSection]
  choose b hb using hover
  -- Step 3: multiply by `σ^{⊗ b}` and glue.
  let b' := Finset.univ.sup fun p : ι × ι ↦ b p.1 p.2
  have hbb (j k : ι) : b j k ≤ b' := Finset.le_sup (f := fun p : ι × ι ↦ b p.1 p.2)
    (Finset.mem_univ (j, k))
  let ν := mulTensorPowSection σ F a b'
  let v : ∀ j : ι, Γ(F ⊗ L.tensorPow (a + b'), W j) := fun j ↦ ν.app (W j) (u₁ j)
  let 𝓕 : TopCat.Sheaf Ab X :=
    ⟨(F ⊗ L.tensorPow (a + b')).presheaf, (F ⊗ L.tensorPow (a + b')).isSheaf⟩
  have hcompat : TopCat.Presheaf.IsCompatible 𝓕.1 W v := by
    intro j k
    rw [← sub_eq_zero]
    have key : ν.app (W j ⊓ W k)
        ((F ⊗ L.tensorPow a).presheaf.map (homOfLE inf_le_left).op (u₁ j) -
          (F ⊗ L.tensorPow a).presheaf.map (homOfLE inf_le_right).op (u₁ k)) = 0 := by
      refine mulTensorPowSection_app_eq_zero σ F a b'
        (g := X.presheaf.map (homOfLE (inf_le_left : W j ⊓ W k ≤ W j)).op (fc j) ^ b')
        (E := (L.tensorPow b').presheaf.map (homOfLE (inf_le_left : W j ⊓ W k ≤ W j)).op
          (E j b')) ?_ ?_
      · rw [← presheaf_map_tensorPowSectionOne σ b' (homOfLE inf_le_left), hE', map_smul,
          map_pow]
      · rw [← Nat.sub_add_cancel (hbb j k), pow_add, mul_smul, hb, smul_zero]
    rw [map_sub, Hom.app_presheaf_map, Hom.app_presheaf_map] at key
    exact key
  obtain ⟨u, hu, -⟩ := 𝓕.existsUnique_gluing' W ⊤ (fun j ↦ homOfLE le_top) hcover v hcompat
  refine ⟨a + b', u, ?_⟩
  refine 𝓕.eq_of_locally_eq' (fun j ↦ W j ⊓ U) U (fun j ↦ homOfLE inf_le_right) ?_ _ _
    fun j ↦ ?_
  · intro x hx
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcover (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hj, hx⟩
  · have hu' : (F ⊗ L.tensorPow (a + b')).presheaf.map (homOfLE (le_top : W j ≤ ⊤)).op u =
        v j := hu j
    refine (presheaf_map_homOfLE_map_homOfLE _ _ _).trans
      ((presheaf_map_homOfLE_map_homOfLE le_top inf_le_left u).symm.trans ?_)
    rw [hu', ← Hom.app_presheaf_map, hu₁ j (hD j).ge, mulTensorPowSection_app_tmulSection,
      tmulSection_map, presheaf_map_tensorPowSectionOne]

end AlgebraicGeometry.Scheme.Modules
