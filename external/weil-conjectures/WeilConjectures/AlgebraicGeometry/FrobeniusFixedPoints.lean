/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.SpecAlgebraicClosure
public import WeilConjectures.Mathlib.FieldTheory.Finite.Basic

/-!
# Frobenius-fixed geometric points

Let `X` be a quasi-compact scheme, locally of finite type over a finite field `K` with `q`
elements. The arithmetic Frobenius `σ : x ↦ x ^ q` of `K̄` acts on the geometric points
`Spec K̄ → X` by coordinates, and its fixed points are the `K`-rational points. We show that
there are only finitely many of them: on an affine chart `Spec R` with `R` of finite type over
`K`, a fixed point is a `K`-algebra map `R → K̄` with values in the fixed field `K` of `σ`, so
it is determined by its values on finitely many generators of `R`.

## Main statements

- `AlgebraicGeometry.finite_setOf_spec_map_comp_eq_self`: for an endomorphism `σ` of a field
  extension `Ω` of a finite field `K` with fixed points in `K`, only finitely many `Ω`-points of
  `X` are fixed by `σ`.
- `AlgebraicGeometry.Scheme.finite_setOf_specAlgebraicClosureMap_frobenius_comp_eq_self`: the
  geometric points of `X` fixed by the arithmetic Frobenius form a finite set.

## Blueprint

These are the finiteness step `A^σ = A₀(k₀)` finite of blueprint
`proposition-no-frobenius-fixed-vector`.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

variable {K : Type u} [Field K] {Ω : Type u} [Field Ω] [Algebra K Ω]

/-- Let `X` be a scheme over a finite field `K`, `Spec R → X` an open immersion such that `R` is
of finite type over `K`, and `σ` an endomorphism of a field extension `Ω` of `K` whose fixed
points lie in `K`. Then only finitely many `Ω`-points of `X` over `K` lying in the chart
`Spec R` are fixed by `σ`: such a point is a `K`-algebra map `R → Ω` with values in `K`, so it
is determined by its values in `K` on finitely many generators of `R`.

This is the chart computation of blueprint `proposition-no-frobenius-fixed-vector`. -/
theorem finite_setOf_spec_map_comp_eq_self_of_isOpenImmersion [Finite K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) {R : CommRingCat.{u}} (ι : Spec R ⟶ X) [IsOpenImmersion ι]
    [LocallyOfFiniteType (ι ≫ f)] (σ : Ω →+* Ω)
    (hσ : ∀ x, σ x = x → x ∈ Set.range (algebraMap K Ω)) :
    {P : Spec (.of Ω) ⟶ X | P ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ∧
      Spec.map (CommRingCat.ofHom σ) ≫ P = P ∧ Set.range P ⊆ Set.range ι}.Finite := by
  classical
  set ψ := Spec.preimage (ι ≫ f)
  have hψ : Spec.map ψ = ι ≫ f := Spec.map_preimage _
  have hft : ψ.hom.FiniteType := by
    rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), hψ]
    infer_instance
  let := ψ.hom.toAlgebra
  have : Algebra.FiniteType K R := hft
  obtain ⟨s, hs⟩ := this.out
  -- The ring map `R → Ω` of a geometric point landing in the chart.
  let φ (P : Spec (.of Ω) ⟶ X) (h : Set.range P ⊆ Set.range ι) : R ⟶ .of Ω :=
    Spec.preimage (IsOpenImmersion.lift ι P h)
  have hφ (P : Spec (.of Ω) ⟶ X) (h) : Spec.map (φ P h) ≫ ι = P := by
    simp only [φ, Spec.map_preimage, IsOpenImmersion.lift_fac]
  have hφK (P : Spec (.of Ω) ⟶ X) (h)
      (hP : P ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K Ω))) :
      ψ ≫ φ P h = CommRingCat.ofHom (algebraMap K Ω) :=
    Spec.map_injective <| by rw [Spec.map_comp, hψ, ← Category.assoc, hφ, hP]
  have hφσ (P : Spec (.of Ω) ⟶ X) (h) (hP : Spec.map (CommRingCat.ofHom σ) ≫ P = P) :
      φ P h ≫ CommRingCat.ofHom σ = φ P h :=
    Spec.map_injective <| by
      rw [Spec.map_comp, ← cancel_mono ι, Category.assoc, hφ, hP]
  -- The point is determined by the values of its ring map on the generators `s`.
  let Φ (P : Spec (.of Ω) ⟶ X) : s → Ω := fun g ↦
    if h : Set.range P ⊆ Set.range ι then φ P h g else 0
  refine Set.Finite.of_finite_image (f := Φ) ?_ ?_
  · refine (Set.Finite.pi (t := fun _ : s ↦ Set.range (algebraMap K Ω))
      fun _ ↦ Set.finite_range _).subset ?_
    rintro _ ⟨P, ⟨-, hP, h⟩, rfl⟩
    rw [Set.mem_univ_pi]
    intro g
    simp only [Φ, dite_eq_left h]
    exact hσ _ (congr_arg (fun F : R ⟶ .of Ω ↦ F g) (hφσ P h hP))
  · rintro P ⟨hPK, -, hP⟩ Q ⟨hQK, -, hQ⟩ hPQ
    let φP : R →ₐ[K] Ω := ⟨(φ P hP).hom, fun r ↦ congr_arg (fun F ↦ F r) (hφK P hP hPK)⟩
    let φQ : R →ₐ[K] Ω := ⟨(φ Q hQ).hom, fun r ↦ congr_arg (fun F ↦ F r) (hφK Q hQ hQK)⟩
    have : φP = φQ := AlgHom.ext_of_adjoin_eq_top hs fun g hg ↦ by
      have := congr_fun hPQ ⟨g, hg⟩
      simp only [Φ, dite_eq_left hP, dite_eq_left hQ] at this
      exact this
    rw [← hφ P hP, ← hφ Q hQ]
    congr 2
    ext r
    exact congr_arg (fun F : R →ₐ[K] Ω ↦ F r) this

/-- The variant of `finite_setOf_spec_map_comp_eq_self_of_isOpenImmersion` for an open immersion
from an affine scheme. -/
theorem finite_setOf_spec_map_comp_eq_self_of_isAffine [Finite K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) {Y : Scheme.{u}} [IsAffine Y] (ι : Y ⟶ X) [IsOpenImmersion ι]
    [LocallyOfFiniteType (ι ≫ f)] (σ : Ω →+* Ω)
    (hσ : ∀ x, σ x = x → x ∈ Set.range (algebraMap K Ω)) :
    {P : Spec (.of Ω) ⟶ X | P ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ∧
      Spec.map (CommRingCat.ofHom σ) ≫ P = P ∧ Set.range P ⊆ Set.range ι}.Finite := by
  have : LocallyOfFiniteType ((Y.isoSpec.inv ≫ ι) ≫ f) := by
    rw [Category.assoc]; infer_instance
  have hrange : Set.range (Y.isoSpec.inv ≫ ι) = Set.range ι := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨Y.isoSpec.hom z, by simp⟩
  simpa only [hrange] using
    finite_setOf_spec_map_comp_eq_self_of_isOpenImmersion f (Y.isoSpec.inv ≫ ι) σ hσ

/-- Let `X` be a quasi-compact scheme locally of finite type over a finite field `K`, and `σ` an
endomorphism of a field extension `Ω` of `K` whose fixed points lie in `K`. Then only finitely
many `Ω`-points of `X` over `K` are fixed by `σ`: cover `X` by finitely many affine charts and
apply `finite_setOf_spec_map_comp_eq_self_of_isAffine`. -/
theorem finite_setOf_spec_map_comp_eq_self [Finite K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    [CompactSpace X] [LocallyOfFiniteType f] (σ : Ω →+* Ω)
    (hσ : ∀ x, σ x = x → x ∈ Set.range (algebraMap K Ω)) :
    {P : Spec (.of Ω) ⟶ X | P ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ∧
      Spec.map (CommRingCat.ofHom σ) ≫ P = P}.Finite := by
  -- Finitely many affine opens cover `X`.
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun V : X.affineOpens ↦ (V : Set X))
    (fun V ↦ V.1.isOpen) fun x _ ↦ by
      obtain ⟨V, hV, hxV, -⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
        (show x ∈ (⊤ : X.Opens) from trivial)
      exact Set.mem_iUnion.mpr ⟨⟨V, hV⟩, hxV⟩
  refine (t.finite_toSet.biUnion fun V _ ↦
    finite_setOf_spec_map_comp_eq_self_of_isAffine f V.1.ι σ hσ).subset ?_
  rintro P ⟨hPK, hP⟩
  have : Subsingleton (Spec (.of Ω)) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
  let x : Spec (.of Ω) := ⟨⊥, Ideal.isPrime_bot⟩
  obtain ⟨V, hVt, hxV⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ (P x)))
  refine Set.mem_iUnion₂.mpr ⟨V, hVt, hPK, hP, ?_⟩
  rintro _ ⟨y, rfl⟩
  rw [Subsingleton.elim y x, Scheme.Opens.range_ι]
  exact hxV

/-- Blueprint `proposition-no-frobenius-fixed-vector` (finiteness step): the geometric points of a
quasi-compact scheme `X` locally of finite type over a finite field `K` that are fixed by the
arithmetic Frobenius `σ : x ↦ x ^ #K` of `K̄` form a finite set (they are the `K`-rational
points of `X`). -/
theorem Scheme.finite_setOf_specAlgebraicClosureMap_frobenius_comp_eq_self [Fintype K]
    (X : Over (Spec (.of K))) [CompactSpace X.left] [LocallyOfFiniteType X.hom] :
    {P : Scheme.specAlgebraicClosure K ⟶ X |
      Scheme.specAlgebraicClosureMap
        (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)).toAlgHom ≫ P =
        P}.Finite := by
  refine Set.Finite.of_finite_image (f := fun P ↦ P.left) ?_
    (fun P _ Q _ h ↦ Over.OverMorphism.ext h)
  refine (finite_setOf_spec_map_comp_eq_self X.hom
    (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)).toRingHom
    fun x hx ↦ (FiniteField.frobeniusAlgEquivOfAlgebraic_apply_eq_self_iff K _).mp hx).subset ?_
  rintro _ ⟨P, hP, rfl⟩
  exact ⟨Over.w P, congr_arg CommaMorphism.left hP⟩

end AlgebraicGeometry
