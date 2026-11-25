/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LinearProjection
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import WeilConjectures.RingTheory.GradedAlgebra.LinearPair
public import WeilConjectures.RingTheory.GradedAlgebra.PowersAlgebraSpan

/-!
# Auxiliary results for the homogeneous coordinate model of a projective scheme

This file collects the general facts used to identify an integral closed subscheme of
projective space with `Proj` of its homogeneous coordinate ring, see
`AlgebraicGeometry.exists_isStandard_iso_proj`.

## Main statements

- `AlgebraicGeometry.AffineSpace.isoSpec_inv_comp_eq_homOfVector` — a morphism from an affine
  scheme `Y` to `𝔸(m; Spec k)` is, under `Y ≅ Spec Γ(Y, ⊤)`, given by its coordinates.
- `AlgebraicGeometry.surjective_of_isClosedImmersion_SpecMap` — a ring map whose `Spec` is a
  closed immersion is surjective.
- `AlgebraicGeometry.Proj.isReduced_of_isDomain` — `Proj` of a graded domain is reduced.
- `AlgebraicGeometry.IsClosedImmersion.exists_iso_of_range_eq` — two closed immersions with
  reduced sources and the same image are isomorphic over the target.
- `AlgebraicGeometry.Proj.exists_isClosedImmersion_chart` — the projective closure of an affine
  chart `Spec K ⟶ 𝔸(n ∖ {j₀}; Spec k)`, as `Proj` of a standard graded domain.
-/

@[expose] public section

universe u

open CategoryTheory Limits HomogeneousLocalization

noncomputable section

namespace ProjectiveSpectrum

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (𝒜 : ℕ → Submodule R A)
  [GradedAlgebra 𝒜]

/-- If `A` is a graded domain with a nonzero element `f` of positive degree, the zero ideal is a
point of `Proj A` (not containing `f`) which specializes to every point. -/
lemma exists_notMem_forall_specializes [IsDomain A] {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : d ≠ 0)
    (hf0 : f ≠ 0) : ∃ x₀ : ProjectiveSpectrum 𝒜, f ∉ x₀.asHomogeneousIdeal ∧ ∀ x, x₀ ⤳ x := by
  have hirr : f ∈ HomogeneousIdeal.irrelevant 𝒜 := by
    rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
      DirectSum.decompose_of_mem_ne _ hf hd]
  have hbot (h : f ∈ (⊥ : HomogeneousIdeal 𝒜)) : False := hf0 (by
    rwa [← HomogeneousIdeal.mem_iff, HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot] at h)
  refine ⟨⟨⊥, by simpa using Ideal.isPrime_bot, fun h ↦ hbot (h hirr)⟩, hbot, fun x ↦ ?_⟩
  rw [specializes_iff_mem_closure, ← le_iff_mem_closure, ← as_ideal_le_as_ideal]
  exact bot_le

end ProjectiveSpectrum

namespace AlgebraicGeometry

/-- A ring map whose `Spec` is a closed immersion is surjective. -/
lemma surjective_of_isClosedImmersion_SpecMap {A B : CommRingCat.{u}} (ψ : A ⟶ B)
    [IsClosedImmersion (Spec.map ψ)] : Function.Surjective ψ := by
  obtain ⟨-, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine (Spec.map ψ)
  intro x
  obtain ⟨y, hy⟩ := hsurj ((Scheme.ΓSpecIso B).inv x)
  refine ⟨(Scheme.ΓSpecIso A).hom y, ?_⟩
  have := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_naturality ψ)) y
  exact this.symm.trans (by rw [CommRingCat.comp_apply, hy]; simp)

/-- For an affine scheme `Y`, the morphism `Y.isoSpec.inv : Spec Γ(Y, ⊤) ⟶ Y` induces the
inverse of `Γ(Spec Γ(Y, ⊤), ⊤) ≅ Γ(Y, ⊤)` on global sections. -/
lemma Scheme.isoSpec_inv_appTop (Y : Scheme.{u}) [IsAffine Y] :
    Y.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(Y, ⊤)).inv := by
  rw [← cancel_epi (Scheme.ΓSpecIso Γ(Y, ⊤)).hom, Iso.hom_inv_id, ← Scheme.toSpecΓ_appTop,
    ← Scheme.isoSpec_hom, ← Scheme.Hom.comp_appTop, Iso.inv_hom_id, Scheme.Hom.id_appTop]

namespace AffineSpace

variable {k : Type u} [CommRing k] {m : Type u}

/-- A morphism `g` from an affine scheme `Y` to `𝔸(m; Spec k)` is, under `Y ≅ Spec Γ(Y, ⊤)`,
the morphism given by the coordinates `g^* Tⱼ`, where `Γ(Y, ⊤)` is a `k`-algebra via the
structure morphism `Y ⟶ Spec k`. -/
lemma isoSpec_inv_comp_eq_homOfVector {Y : Scheme.{u}} [IsAffine Y]
    (g : Y ⟶ 𝔸(m; Spec (.of k))) :
    letI := ((Scheme.ΓSpecIso (.of k)).inv ≫
      (g ≫ 𝔸(m; Spec (.of k)) ↘ Spec (.of k)).appTop).hom.toAlgebra
    Y.isoSpec.inv ≫ g =
      homOfVector (Spec.map (CommRingCat.ofHom (algebraMap k Γ(Y, ⊤))))
        (fun j ↦ (Scheme.ΓSpecIso Γ(Y, ⊤)).inv (g.appTop (coord _ j))) := by
  let _ := ((Scheme.ΓSpecIso (.of k)).inv ≫
      (g ≫ 𝔸(m; Spec (.of k)) ↘ Spec (.of k)).appTop).hom.toAlgebra
  refine hom_ext ?_ fun j ↦ ?_
  · rw [homOfVector_over, Category.assoc, ← Scheme.isoSpec_inv_naturality,
      Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    rfl
  · rw [homOfVector_appTop_coord, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      Scheme.isoSpec_inv_appTop]

/-- Precomposing the morphism `Spec A ⟶ 𝔸(m; Spec R)` given by coordinates `w` with
`Spec φ` for an `R`-algebra map `φ : A → B` gives the morphism given by the coordinates
`φ ∘ w`. -/
lemma SpecMap_comp_homOfVector {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B) (w : m → A) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        homOfVector (Spec.map (CommRingCat.ofHom (algebraMap R A)))
          (fun j ↦ (Scheme.ΓSpecIso (.of A)).inv (w j)) =
      homOfVector (Spec.map (CommRingCat.ofHom (algebraMap R B)))
        (fun j ↦ (Scheme.ΓSpecIso (.of B)).inv (φ (w j))) := by
  have h : MvPolynomial.aeval (R := R) (fun j ↦ φ (w j)) = φ.comp (MvPolynomial.aeval w) :=
    (MvPolynomial.comp_aeval w φ).symm
  rw [homOfVector_SpecMap_eq, homOfVector_SpecMap_eq, h, ← Category.assoc, ← Spec.map_comp]
  rfl

end AffineSpace

namespace Proj

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] (𝒜 : ℕ → Submodule R A)
  [GradedAlgebra 𝒜]

/-- `Proj` of a graded domain is reduced: it is covered by the spectra of the degree-zero
parts of localizations, which are subrings of localizations of a domain. -/
lemma isReduced_of_isDomain [IsDomain A] : IsReduced (Proj 𝒜) := by
  have (i : (affineOpenCover 𝒜).openCover.I₀) : IsReduced ((affineOpenCover 𝒜).openCover.X i) := by
    change IsReduced (Spec (.of (Away 𝒜 _)))
    have : _root_.IsReduced (Away 𝒜 i.2.1) :=
      isReduced_of_injective (algebraMap _ (Localization.Away (i.2.1 : A)))
        (val_injective _)
    infer_instance
  exact IsReduced.of_openCover (𝒰 := (affineOpenCover 𝒜).openCover)

end Proj

/-- **Closed subschemes are determined by their support when reduced**: two closed immersions
`i₁ : Z₁ ⟶ X` and `i₂ : Z₂ ⟶ X` from reduced schemes with the same image are isomorphic over
`X`. -/
lemma IsClosedImmersion.exists_iso_of_range_eq {Z₁ Z₂ X : Scheme.{u}} (i₁ : Z₁ ⟶ X)
    (i₂ : Z₂ ⟶ X) [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsReduced Z₁] [IsReduced Z₂]
    (h : Set.range i₁ = Set.range i₂) : ∃ e : Z₁ ≅ Z₂, e.hom ≫ i₂ = i₁ := by
  have hker : i₂.ker = i₁.ker := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal, Scheme.Hom.ker_eq_vanishingIdeal]
    congr 2
    exact congrArg closure h.symm
  have := IsClosedImmersion.isIso_lift i₂ i₁ hker
  exact ⟨asIso (IsClosedImmersion.lift i₂ i₁ hker.le), IsClosedImmersion.lift_fac _ _ _⟩


namespace Proj

open ProjectiveSpace

/-- Over the standard open `D₊(Tᵢ)`, the linear projection is isomorphic to the morphism
`Spec B ⟶ 𝔸(ι ∖ {i}; Spec k)` given by coordinates `wⱼ`, for any `k`-algebra isomorphism
`φ : A_(lᵢ) ≅ B` with `φ (lⱼ / lᵢ) = wⱼ`. -/
lemma exists_iso_linearProjection_restrict_of_algHom {k A B : Type u} [CommRing k]
    [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] (𝒜 : ℕ → Submodule k A)
    [GradedAlgebra 𝒜] {ι : Type u} (l : ι → A) (hl : ∀ i, l i ∈ 𝒜 1)
    (hcov : ⨆ i, basicOpen 𝒜 (l i) = ⊤) (i : ι) (φ : Away 𝒜 (l i) →ₐ[k] B)
    (hφ : Function.Bijective φ) (w : {j // j ≠ i} → B)
    (hw : ∀ j, φ (Away.mk 𝒜 (hl i) 1 (l j.1) (by simpa using hl j.1)) = w j) :
    ∃ ψ : Spec (.of B) ≅ (linearProjection 𝒜 l hl hcov ⁻¹ᵁ standardOpen ι (Spec (.of k)) i),
      ψ.hom ≫ (linearProjection 𝒜 l hl hcov ∣_ standardOpen ι (Spec (.of k)) i) ≫
          (standardOpenIso ι (Spec (.of k)) i).hom =
        AffineSpace.homOfVector (Spec.map (CommRingCat.ofHom (algebraMap k B)))
          (fun j ↦ (Scheme.ΓSpecIso (.of B)).inv (w j)) := by
  obtain ⟨e, he⟩ := exists_iso_linearProjection_restrict 𝒜 l hl hcov i
  let φ' : CommRingCat.of (Away 𝒜 (l i)) ⟶ CommRingCat.of B := CommRingCat.ofHom φ.toRingHom
  have : IsIso φ' := (ConcreteCategory.isIso_iff_bijective φ').mpr hφ
  refine ⟨asIso (Spec.map φ') ≪≫ e, ?_⟩
  rw [Iso.trans_hom, asIso_hom, Category.assoc, he, AffineSpace.SpecMap_comp_homOfVector]
  simp only [hw]

set_option backward.isDefEq.respectTransparency true in
/-- **The projective closure of an affine chart**: let `K` be a domain which is a `k`-algebra
generated by elements `v j`, `j ≠ j₀`. Put `a_{j₀} = 1` and `a_j = v_j` otherwise, and let
`S = k[a_j t] ⊆ K[t]`. Then `S` is a standard graded domain, generated by the linear forms
`l_j = a_j t`, these define a closed immersion `p : Proj S ⟶ ℙ(n; Spec k)` over `k` (the linear
projection `AlgebraicGeometry.Proj.linearProjection` by the `l_j`), and over the standard chart
`D₊(T_{j₀})` it is isomorphic to the closed immersion `Spec K ⟶ 𝔸(n ∖ {j₀}; Spec k)` given by
the `v j`. Moreover `Proj S` has a generic point (the zero ideal) lying over `D₊(T_{j₀})`. -/
theorem exists_isClosedImmersion_chart {k K : Type u} [Field k] [CommRing K] [IsDomain K]
    [Algebra k K] {n : Type u} [Finite n] (j₀ : n) (v : {j : n // j ≠ j₀} → K)
    (hv : Algebra.adjoin k (Set.range v) = ⊤) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra k S) (𝒜 : ℕ → Submodule k S)
      (_ : GradedAlgebra 𝒜), GradedAlgebra.IsStandard 𝒜 ∧ IsDomain S ∧
      ∃ (l : n → S) (hl : ∀ j, l j ∈ 𝒜 1) (hcov : ⨆ j, basicOpen 𝒜 (l j) = ⊤),
      Algebra.adjoin k (Set.range l) = ⊤ ∧
      ∃ p : Proj 𝒜 ⟶ ℙ(n; Spec (.of k)), p = linearProjection 𝒜 l hl hcov ∧ IsClosedImmersion p ∧
        p ≫ ℙ(n; Spec (.of k)) ↘ Spec (.of k) = Proj.toSpecBase 𝒜 ∧
        (∃ x₀ : Proj 𝒜, x₀ ∈ p ⁻¹ᵁ standardOpen n (Spec (.of k)) j₀ ∧ ∀ x, x₀ ⤳ x) ∧
        ∃ ψ : Spec (.of K) ≅ (p ⁻¹ᵁ standardOpen n (Spec (.of k)) j₀).toScheme,
          ψ.hom ≫ (p ∣_ standardOpen n (Spec (.of k)) j₀) ≫
              (standardOpenIso n (Spec (.of k)) j₀).hom =
            AffineSpace.homOfVector (Spec.map (CommRingCat.ofHom (algebraMap k K)))
              (fun j ↦ (Scheme.ΓSpecIso (.of K)).inv (v j)) := by
  classical
  let a : n → K := fun j ↦ if hj : j = j₀ then 1 else v ⟨j, hj⟩
  have ha : a j₀ = 1 := dite_eq_left rfl
  have hstd : GradedAlgebra.IsStandard (Submodule.span k (Set.range a)).powersGrading :=
    Submodule.isStandard_powersGrading (Submodule.fg_span (Set.finite_range a))
  have hl := Submodule.powersLinearForm_mem k a
  have hcov : ⨆ j, basicOpen _ (Submodule.powersLinearForm k a j) = ⊤ :=
    iSup_basicOpen_eq_top _ _
      (GradedAlgebra.IsStandard.irrelevant_le_of_grade_one_subset fun x hx ↦
        Submodule.span_le_restrictScalars k _ _ (Submodule.powersGrading_one_le_span k a hx))
  have hgen (j : n) : Algebra.adjoin k (Set.range fun j' : {j' // j' ≠ j} ↦
      Away.mk _ (hl j) 1 (Submodule.powersLinearForm k a j'.1) (by simpa using hl j'.1)) = ⊤ := by
    refine eq_top_iff.mpr ((GradedAlgebra.IsStandard.adjoin_away_eq_top hl
      (Submodule.powersGrading_one_le_span k a) j).symm.le.trans (Algebra.adjoin_le ?_))
    rintro _ ⟨j', rfl⟩
    by_cases hj : j' = j
    · subst hj
      beta_reduce
      rw [SetLike.mem_coe, Away.mk_self]
      exact one_mem _
    · exact Algebra.subset_adjoin (Set.mem_range.mpr ⟨⟨j', hj⟩, rfl⟩)
  set p := linearProjection _ _ hl hcov
  have hp : IsClosedImmersion p := isClosedImmersion_linearProjection _ _ hl hcov hgen
  -- the chart comparison
  set φ := Submodule.powersAwayEval k ha
  have hφ (j : {j : n // j ≠ j₀}) :
      φ (Away.mk _ (hl j₀) 1 (Submodule.powersLinearForm k a j.1) (by simpa using hl j.1)) =
        v j := by
    rw [Submodule.powersAwayEval_powersLinearForm]
    exact dite_eq_right j.2
  have hsurj : Function.Surjective φ := by
    have : Algebra.adjoin k (Set.range v) ≤ φ.range := Algebra.adjoin_le (by
      rintro _ ⟨j, rfl⟩
      exact ⟨_, hφ j⟩)
    rw [hv] at this
    exact fun r ↦ this (Algebra.mem_top (x := r))
  obtain ⟨ψ, hψ⟩ := exists_iso_linearProjection_restrict_of_algHom _ _ hl hcov j₀ φ
    ⟨Submodule.powersAwayEval_injective k ha, hsurj⟩ v hφ
  -- the generic point
  have hl0 : Submodule.powersLinearForm k a j₀ ≠ 0 := by
    intro h
    have := congrArg (fun F : (Submodule.span k (Set.range a)).powersAlgebra ↦
      (F : Polynomial K).coeff 1) h
    simp [Submodule.powersLinearForm, ha] at this
  obtain ⟨x₀, hx₀, hsp⟩ :=
    ProjectiveSpectrum.exists_notMem_forall_specializes _ (hl j₀) one_ne_zero hl0
  have hadj : Algebra.adjoin k (Set.range (Submodule.powersLinearForm k a)) = ⊤ :=
    eq_top_iff.2 (hstd.adjoin_one.symm.le.trans (Algebra.adjoin_le fun x hx ↦
      Algebra.span_le_adjoin k _ (Submodule.powersGrading_one_le_span k a hx)))
  refine ⟨(Submodule.span k (Set.range a)).powersAlgebra, inferInstance, inferInstance,
    (Submodule.span k (Set.range a)).powersGrading, inferInstance, hstd, inferInstance, _, hl,
    hcov, hadj, p, rfl, hp,
    linearProjection_over _ _ hl hcov, ⟨x₀, ?_, hsp⟩, ψ, hψ⟩
  rw [linearProjection_preimage_standardOpen]
  exact hx₀

end Proj

end AlgebraicGeometry
