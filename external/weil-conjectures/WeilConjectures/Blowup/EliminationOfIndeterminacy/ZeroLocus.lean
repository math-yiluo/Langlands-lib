/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Zero loci of fraction equations in relative affine space

Zero loci of fraction equations `v i * tⱼ = w i j` in relative affine space over `Spec S` lie
in the range of the morphism defined by the fractions
(`AlgebraicGeometry.AffineSpace.zeroLocus_subset_range_homOfVector`).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry
section GraphClosedness

/-! ### Closedness of graphs cut out by fraction equations

Over `Spec S`, consider a morphism `γ` to `𝔸(σ; Spec S)` defined on a union `O` of
basic opens `D(v i)` whose `j`-th coordinate on `D(v i)` is the fraction `w i j / v i`.
If the elements `v i` and `w i j` generate the unit ideal and satisfy the
compatibilities `v i * w i' j = v i' * w i j`, the range of `γ` is closed in the whole
relative affine space: it is the vanishing locus of the sections
`v̂ᵢ · tⱼ − ŵᵢⱼ`. This is the chart-local core of the graph-closedness statement of
Conrad's Theorem 2.4, Case 1. -/

/-- The scheme-theoretic zero locus of the `ΓSpecIso`-preimage of a set of ring
elements is the prime-spectrum zero locus. -/
lemma Scheme.zeroLocus_ΓSpecIso_inv_image {R : CommRingCat.{u}} (s : Set R) :
    (Spec R).zeroLocus (U := ⊤) ((Scheme.ΓSpecIso R).inv '' s) =
      PrimeSpectrum.zeroLocus s := by
  ext x
  rw [Scheme.mem_zeroLocus_iff, PrimeSpectrum.mem_zeroLocus]
  constructor
  · intro h e he
    have h2 := h _ (Set.mem_image_of_mem _ he)
    rw [basicOpen_eq_of_affine] at h2
    by_contra hne
    exact h2 ((PrimeSpectrum.mem_basicOpen _ _).mpr hne)
  · rintro h - ⟨e, he, rfl⟩
    rw [basicOpen_eq_of_affine]
    intro hmem
    exact (PrimeSpectrum.mem_basicOpen _ _).mp hmem (h he)

namespace AffineSpace

variable {σ : Type u}

/-- Over `Spec L`, the vanishing locus of the sections `coordⱼ − ĉⱼ` is contained in
the range of the section of `𝔸(σ; Spec L) ↘ Spec L` with coordinates `c`. -/
lemma zeroLocus_subset_range_homOfVector_spec {L : CommRingCat.{u}} (c : σ → L) :
    𝔸(σ; Spec L).zeroLocus (U := ⊤) (Set.range fun j ↦ coord (Spec L) j -
        (𝔸(σ; Spec L) ↘ Spec L).appTop ((Scheme.ΓSpecIso L).inv (c j))) ⊆
      Set.range (homOfVector (𝟙 (Spec L)) fun j ↦ (Scheme.ΓSpecIso L).inv (c j)) := by
  set ev : CommRingCat.of (MvPolynomial σ L) ⟶ L := CommRingCat.ofHom (MvPolynomial.eval c)
    with hev_def
  have hev : Function.Surjective (MvPolynomial.eval c) :=
    fun l ↦ ⟨MvPolynomial.C l, by simp⟩
  -- the section with coordinates `c` is `Spec` of the evaluation at `c`
  have hsec : Spec.map ev ≫ (SpecIso σ L).inv =
      homOfVector (𝟙 (Spec L)) fun j ↦ (Scheme.ΓSpecIso L).inv (c j) := by
    apply hom_ext
    · rw [Category.assoc, SpecIso_inv_over, homOfVector_over, ← Spec.map_comp,
        ← Spec.map_id]
      congr 1
      ext p
      change MvPolynomial.eval c (MvPolynomial.C p) = p
      simp
    · intro j
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, SpecIso_inv_appTop_coord,
        homOfVector_appTop_coord, ← CommRingCat.comp_apply,
        ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply, hev_def]
      congr 1
      simp
  intro x hx
  -- transport the vanishing condition to the prime spectrum of the polynomial ring
  have hpre : (SpecIso σ L).inv ⁻¹' (𝔸(σ; Spec L).zeroLocus (U := ⊤)
      (Set.range fun j ↦ coord (Spec L) j -
        (𝔸(σ; Spec L) ↘ Spec L).appTop ((Scheme.ΓSpecIso L).inv (c j)))) =
      PrimeSpectrum.zeroLocus
        (Set.range fun j ↦ MvPolynomial.X j - MvPolynomial.C (c j)) := by
    rw [Scheme.preimage_zeroLocus, ← Scheme.zeroLocus_ΓSpecIso_inv_image
      (R := CommRingCat.of (MvPolynomial σ L))
      (Set.range fun j ↦ MvPolynomial.X j - MvPolynomial.C (c j))]
    congr 1
    rw [← Set.range_comp, ← Set.range_comp]
    congr 1
    funext j
    simp only [Function.comp_apply, map_sub]
    congr 1
    · exact SpecIso_inv_appTop_coord L j
    · rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, SpecIso_inv_over,
        ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
        CommRingCat.comp_apply]
      rfl
  have hx' : (SpecIso σ L).hom x ∈ PrimeSpectrum.zeroLocus
      (Set.range fun j ↦ MvPolynomial.X j - MvPolynomial.C (c j)) := by
    rw [← hpre, Set.mem_preimage]
    have hxx : (SpecIso σ L).inv ((SpecIso σ L).hom x) = x := by
      rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
      rfl
    rwa [hxx]
  -- the vanishing locus is the range of `Spec` of the evaluation
  rw [← PrimeSpectrum.zeroLocus_span, ← MvPolynomial.ker_eval,
    ← range_comap_of_surjective _ _ hev] at hx'
  obtain ⟨y, hy⟩ := hx'
  refine ⟨y, ?_⟩
  rw [← hsec, Scheme.Hom.comp_apply]
  have hSpec : (Spec.map ev) y = PrimeSpectrum.comap (MvPolynomial.eval c) y := rfl
  rw [hSpec, hy, ← Scheme.Hom.comp_apply, Iso.hom_inv_id]
  rfl

/-- The vanishing locus of the sections `coordⱼ − t̂ⱼ` on a relative affine space over
an affine scheme is contained in the range of the section with coordinates `t`. -/
lemma zeroLocus_subset_range_homOfVector {Z : Scheme.{u}} [IsAffine Z] (t : σ → Γ(Z, ⊤)) :
    𝔸(σ; Z).zeroLocus (U := ⊤)
        (Set.range fun j ↦ coord Z j - (𝔸(σ; Z) ↘ Z).appTop (t j)) ⊆
      Set.range (homOfVector (𝟙 Z) t) := by
  set tL : σ → Γ(Spec Γ(Z, ⊤), ⊤) := fun j ↦ Z.isoSpec.inv.appTop (t j) with htL
  set c : σ → Γ(Z, ⊤) := fun j ↦ (Scheme.ΓSpecIso Γ(Z, ⊤)).hom (tL j) with hc
  have hct : ∀ j, (Scheme.ΓSpecIso Γ(Z, ⊤)).inv (c j) = tL j := fun j ↦
    Iso.hom_inv_id_apply (Scheme.ΓSpecIso Γ(Z, ⊤)) (tL j)
  have hisot : ∀ j, Z.isoSpec.hom.appTop (tL j) = t j := by
    intro j
    rw [htL, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Iso.hom_inv_id]
    simp
  set α := map σ Z.isoSpec.hom with hα
  have : IsIso α := by
    refine ⟨map σ Z.isoSpec.inv, ?_, ?_⟩ <;>
      rw [hα, ← map_comp] <;> simp [map_id]
  have hcomm : homOfVector (𝟙 Z) t ≫ α = Z.isoSpec.hom ≫
      homOfVector (𝟙 (Spec Γ(Z, ⊤))) tL := by
    apply hom_ext
    · rw [Category.assoc, hα, map_over, homOfVector_over_assoc, Category.id_comp,
        Category.assoc, homOfVector_over, Category.comp_id]
    · intro j
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hα, map_appTop_coord,
        homOfVector_appTop_coord, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        homOfVector_appTop_coord, hisot]
  intro x hx
  have hfun : ∀ j, α.appTop (coord (Spec Γ(Z, ⊤)) j -
      (𝔸(σ; Spec Γ(Z, ⊤)) ↘ Spec Γ(Z, ⊤)).appTop ((Scheme.ΓSpecIso Γ(Z, ⊤)).inv (c j))) =
      coord Z j - (𝔸(σ; Z) ↘ Z).appTop (t j) := by
    intro j
    rw [map_sub, hα, map_appTop_coord, hct, ← CommRingCat.comp_apply,
      ← Scheme.Hom.comp_appTop, map_over, Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply, hisot]
  have hαx : α x ∈ 𝔸(σ; Spec Γ(Z, ⊤)).zeroLocus (U := ⊤)
      (Set.range fun j ↦ coord (Spec Γ(Z, ⊤)) j -
        (𝔸(σ; Spec Γ(Z, ⊤)) ↘ Spec Γ(Z, ⊤)).appTop
          ((Scheme.ΓSpecIso Γ(Z, ⊤)).inv (c j))) := by
    have hpre : α ⁻¹' (𝔸(σ; Spec Γ(Z, ⊤)).zeroLocus (U := ⊤)
        (Set.range fun j ↦ coord (Spec Γ(Z, ⊤)) j -
          (𝔸(σ; Spec Γ(Z, ⊤)) ↘ Spec Γ(Z, ⊤)).appTop
            ((Scheme.ΓSpecIso Γ(Z, ⊤)).inv (c j)))) =
        𝔸(σ; Z).zeroLocus (U := ⊤)
          (Set.range fun j ↦ coord Z j - (𝔸(σ; Z) ↘ Z).appTop (t j)) := by
      rw [Scheme.preimage_zeroLocus, ← Set.range_comp]
      exact congrArg (fun s ↦ 𝔸(σ; Z).zeroLocus (U := ⊤) s)
        (congrArg Set.range (funext hfun))
    rw [← Set.mem_preimage, hpre]
    exact hx
  have hmem := zeroLocus_subset_range_homOfVector_spec c hαx
  obtain ⟨z, hz⟩ := hmem
  have hfun : (fun j ↦ (Scheme.ΓSpecIso Γ(Z, ⊤)).inv (c j)) = tL := funext hct
  rw [hfun] at hz
  refine ⟨Z.isoSpec.inv z, ?_⟩
  have hαeq : α (homOfVector (𝟙 Z) t (Z.isoSpec.inv z)) = α x := by
    rw [← Scheme.Hom.comp_apply, hcomm, Scheme.Hom.comp_apply]
    have h1 : Z.isoSpec.hom (Z.isoSpec.inv z) = z := by
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
      rfl
    rw [h1, hz]
  exact (Scheme.Hom.homeomorph α).injective hαeq

end AffineSpace

end GraphClosedness

end AlgebraicGeometry
