import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Local differential slices: a closed embedding into a smooth scheme -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace Langlands.GroupScheme.ReducedBaseSmooth

/-- If the differentials of elements coming from an intermediate algebra `R'` span the cotangent
fibre `κ(Q) ⊗ Ω[A⁄R]`, then `A` is unramified over `R'` at `Q`. -/
theorem isUnramifiedAt_of_span {R R' A : Type u} [CommRing R] [CommRing R'] [CommRing A]
    [Algebra R R'] [Algebra R A] [Algebra R' A] [IsScalarTower R R' A] [Algebra.FiniteType R' A]
    (Q : Ideal A) [Q.IsPrime] (s : Set R')
    (hs : Submodule.span Q.ResidueField
      ((fun r => (1 : Q.ResidueField) ⊗ₜ[A] KaehlerDifferential.D R A (algebraMap R' A r)) '' s) =
        ⊤) :
    Algebra.IsUnramifiedAt R' Q := by
  let K := Q.ResidueField
  let f : K ⊗[A] Ω[A⁄R] →ₗ[K] K ⊗[A] Ω[A⁄R'] :=
    (KaehlerDifferential.map R R' A A).baseChange K
  have hsurj : Function.Surjective f :=
    LinearMap.baseChange_surjective K (KaehlerDifferential.map_surjective R R' A)
  have hzero : Submodule.map f (Submodule.span K
      ((fun r => (1 : K) ⊗ₜ[A] KaehlerDifferential.D R A (algebraMap R' A r)) '' s)) = ⊥ := by
    rw [Submodule.map_span, Submodule.span_eq_bot]
    rintro _ ⟨_, ⟨r, -, rfl⟩, rfl⟩
    simp [f, LinearMap.baseChange_tmul]
  rw [hs, Submodule.map_top, LinearMap.range_eq_top.mpr hsurj] at hzero
  have hsub : Subsingleton (K ⊗[A] Ω[A⁄R']) := (Submodule.subsingleton_iff K).mp
    (subsingleton_of_bot_eq_top (α := Submodule K (K ⊗[A] Ω[A⁄R'])) hzero.symm)
  have hnot : (⟨Q, inferInstance⟩ : PrimeSpectrum A) ∉ Module.support A Ω[A⁄R'] := by
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct]
    exact not_nontrivial_iff_subsingleton.mpr hsub
  have hmem : (⟨Q, inferInstance⟩ : PrimeSpectrum A) ∈ Algebra.unramifiedLocus R' A := by
    rw [Algebra.unramifiedLocus_eq_compl_support]
    exact hnot
  exact hmem

/-- Over a field-valued residue, the differentials of all elements span the cotangent fibre. -/
theorem span_one_tmul_D_eq_top {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (Q : Ideal A) [Q.IsPrime] :
    Submodule.span Q.ResidueField
      (Set.range fun x : A => (1 : Q.ResidueField) ⊗ₜ[A] KaehlerDifferential.D R A x) = ⊤ := by
  have h := Submodule.baseChange_span (R := A) (A := Q.ResidueField)
    (Set.range (KaehlerDifferential.D R A))
  rw [KaehlerDifferential.span_range_derivation, Submodule.baseChange_top] at h
  rw [h, ← Set.range_comp]
  rfl

/-- A finite-dimensional cotangent fibre of dimension `n` is spanned by the differentials of
`n` elements. -/
theorem exists_span_eq_top_of_finrank_eq {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [Algebra.FiniteType R A] (Q : Ideal A) [Q.IsPrime] (n : ℕ)
    (hn : Module.finrank Q.ResidueField (Q.ResidueField ⊗[A] Ω[A⁄R]) = n) :
    ∃ a : Fin n → A, Submodule.span Q.ResidueField
      (Set.range fun i => (1 : Q.ResidueField) ⊗ₜ[A] KaehlerDifferential.D R A (a i)) = ⊤ := by
  let K := Q.ResidueField
  let s : Set (K ⊗[A] Ω[A⁄R]) := Set.range fun x : A => (1 : K) ⊗ₜ[A] KaehlerDifferential.D R A x
  obtain ⟨t, hts, hspan, hli⟩ := exists_linearIndependent K s
  have hspan' : Submodule.span K (Set.range ((↑) : t → K ⊗[A] Ω[A⁄R])) = ⊤ := by
    rw [Subtype.range_coe, hspan]
    exact span_one_tmul_D_eq_top Q
  let b : Module.Basis t K (K ⊗[A] Ω[A⁄R]) := Module.Basis.mk hli hspan'.ge
  have : Module.Finite K (K ⊗[A] Ω[A⁄R]) := inferInstance
  have hfin : Finite t := Module.Finite.finite_basis b
  have hcard : Nat.card t = n := by
    rw [← hn, Module.finrank_eq_nat_card_basis b]
  let e : t ≃ Fin n := (Finite.equivFin t).trans (finCongr hcard)
  have hpre : ∀ i : Fin n, ∃ x : A,
      (1 : K) ⊗ₜ[A] KaehlerDifferential.D R A x = ((e.symm i : t) : K ⊗[A] Ω[A⁄R]) :=
    fun i => hts (e.symm i).2
  choose a ha using hpre
  refine ⟨a, ?_⟩
  have hrange : (Set.range fun i => (1 : K) ⊗ₜ[A] KaehlerDifferential.D R A (a i)) =
      Set.range ((↑) : t → K ⊗[A] Ω[A⁄R]) := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e.symm i, (ha i).symm⟩
    · rintro ⟨w, rfl⟩
      exact ⟨e w, by beta_reduce; rw [ha, Equiv.symm_apply_apply]⟩
  rw [hrange, hspan']

/-- **Differential slice.** If `A` is of finite type over `R` and the differentials of
`a₁, …, aₙ` span the cotangent fibre at a prime `Q`, then on a principal open `D(f) ∋ Q` the
spectrum of `A` is a closed subscheme of a scheme étale over affine `n`-space over `R`; in
particular of a scheme smooth of relative dimension `n` over `Spec R`. -/
theorem exists_closedImmersion_smooth_of_span {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [Algebra.FiniteType R A] (Q : Ideal A) [Q.IsPrime] {n : ℕ} (a : Fin n → A)
    (ha : Submodule.span Q.ResidueField
      (Set.range fun i => (1 : Q.ResidueField) ⊗ₜ[A] KaehlerDifferential.D R A (a i)) = ⊤) :
    ∃ f : A, f ∉ Q ∧ ∃ (Z0 : Scheme.{u}) (p0 : Z0 ⟶ Spec (CommRingCat.of R))
      (i0 : Spec (CommRingCat.of (Localization.Away f)) ⟶ Z0),
      SmoothOfRelativeDimension n p0 ∧ QuasiCompact p0 ∧ QuasiSeparated p0 ∧
        IsClosedImmersion i0 ∧
        i0 ≫ p0 = Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f))) := by
  let R' := MvPolynomial (Fin n) R
  let : Algebra R' A := (MvPolynomial.aeval a).toRingHom.toAlgebra
  have : IsScalarTower R R' A := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R A r = MvPolynomial.aeval a (MvPolynomial.C r)
    rw [MvPolynomial.aeval_C]
  have : Algebra.FiniteType R' A := Algebra.FiniteType.of_restrictScalars_finiteType R R' A
  have hspan : Submodule.span Q.ResidueField
      ((fun r => (1 : Q.ResidueField) ⊗ₜ[A] KaehlerDifferential.D R A (algebraMap R' A r)) ''
        Set.range (MvPolynomial.X : Fin n → R')) = ⊤ := by
    rw [← Set.range_comp, ← ha]
    congr 2
    ext i
    simp only [Function.comp_apply]
    congr 2
    change MvPolynomial.aeval a (MvPolynomial.X i) = a i
    rw [MvPolynomial.aeval_X]
  have : Algebra.IsUnramifiedAt R' Q := isUnramifiedAt_of_span Q _ hspan
  obtain ⟨f, hfQ, P, φ, hφ⟩ :=
    Algebra.IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn (R := R') Q
  refine ⟨f, hfQ, Spec (CommRingCat.of P.Ring),
    Spec.map (CommRingCat.ofHom (algebraMap R' P.Ring)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R R')),
    Spec.map (CommRingCat.ofHom φ.toRingHom), ?_, inferInstance, inferInstance,
    IsClosedImmersion.spec_of_surjective _ hφ, ?_⟩
  · have h1 : SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := by
      rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)]
      apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
      rw [CommRingCat.hom_ofHom, RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
      infer_instance
    have h0 : Etale (Spec.map (CommRingCat.ofHom (algebraMap R' P.Ring))) := by
      rw [HasRingHomProperty.Spec_iff (P := @Etale), CommRingCat.hom_ofHom,
        RingHom.etale_algebraMap]
      infer_instance
    have := smoothOfRelativeDimension_comp (n := 0) (m := n)
      (Spec.map (CommRingCat.ofHom (algebraMap R' P.Ring)))
      (Spec.map (CommRingCat.ofHom (algebraMap R R')))
    rwa [zero_add] at this
  · rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext r
    change φ (algebraMap R' P.Ring (algebraMap R R' r)) = algebraMap R (Localization.Away f) r
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R R' (Localization.Away f)]

end Langlands.GroupScheme.ReducedBaseSmooth
