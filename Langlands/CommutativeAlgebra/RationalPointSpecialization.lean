import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Integer
import Mathlib.Algebra.Polynomial.Lifts

/-! # Rational points from a separable primitive element over a fraction field

Let `P` be a domain over a separably closed field `k` with fraction field `F`, let `K / F` be a
finite separable extension and let `f : R → K` be a `k`-algebra map from a finitely generated
`k`-algebra `R`. If every nonzero element of `P` stays nonzero under some `k`-algebra map
`P → k`, then `R` has a `k`-algebra map to `k`. The proof spreads a primitive element of `K / F`,
its minimal polynomial and the images of the generators of `R` out over a localization `P[1/D]`,
and specializes along a `k`-point of `P` at which `D` does not vanish.
-/

open Polynomial

namespace Langlands.CommutativeAlgebra.RationalPointSpecialization

/-- Let `g` be a separable polynomial over a ring `C` whose image under an injective map
`ι : C → F` to a field is the minimal polynomial of an integral element `y` of an `F`-algebra.
Then for every map `ψ : C → k` to a separably closed field there is `t : k` such that every
polynomial `h` over `C` with `h(y) = 0` satisfies `ψ(h)(t) = 0`. -/
theorem exists_forall_eval_map_eq_zero {C F K k : Type*} [CommRing C] [Field F] [Ring K]
    [Nontrivial K] [Algebra F K] [Field k] [IsSepClosed k] (ι : C →+* F)
    (hι : Function.Injective ι) (ψ : C →+* k) {y : K} (hy : IsIntegral F y) {g : C[X]}
    (hg : g.map ι = minpoly F y) (hsep : g.Separable) :
    ∃ t : k, ∀ h : C[X], aeval y (h.map ι) = 0 → (h.map ψ).eval t = 0 := by
  have : Nontrivial C := ι.domain_nontrivial
  have hmon : g.Monic := monic_of_injective hι (hg ▸ minpoly.monic hy)
  have hdeg : (g.map ψ).degree ≠ 0 := by
    have hpos : 0 < (g.map ψ).natDegree := by
      rw [hmon.natDegree_map, ← natDegree_map_eq_of_injective hι, hg]
      exact minpoly.natDegree_pos hy
    exact (natDegree_pos_iff_degree_pos.mp hpos).ne'
  obtain ⟨t, ht⟩ := IsSepClosed.exists_root (g.map ψ) hdeg (hsep.map)
  refine ⟨t, fun h hh => ?_⟩
  have hrem : h %ₘ g = 0 := by
    by_contra hne
    have h1 : (h %ₘ g).map ι ≠ 0 := (Polynomial.map_ne_zero_iff hι).mpr hne
    have h2 : aeval y ((h %ₘ g).map ι) = 0 := by
      rw [modByMonic_eq_sub_mul_div h g, Polynomial.map_sub, Polynomial.map_mul, map_sub,
        map_mul, hh, hg, minpoly.aeval, zero_mul, sub_zero]
    have h3 := minpoly.degree_le_of_ne_zero F y h1 h2
    rw [degree_map_eq_of_injective hι, ← hg, degree_map_eq_of_injective hι] at h3
    exact absurd (h3.trans_lt (degree_modByMonic_lt h hmon)) (lt_irrefl _)
  rw [← modByMonic_add_div h g, hrem, zero_add, Polynomial.map_mul, eval_mul, ht.eq_zero,
    zero_mul]

/-- Let `P` be a domain over a separably closed field `k` with fraction field `F`, and let `K` be
a finite separable extension of `F`. Assume that every nonzero element of `P` stays nonzero under
some `k`-algebra map `P → k`. Then every finitely generated `k`-algebra `R` with a `k`-algebra
map `R → K` has a `k`-algebra map `R → k`. -/
theorem nonempty_algHom_of_isFractionRing {k P F K R : Type*} [Field k] [IsSepClosed k]
    [CommRing P] [IsDomain P] [Algebra k P] [Field F] [Algebra P F] [IsFractionRing P F]
    [Algebra k F] [IsScalarTower k P F] [Field K] [Algebra F K] [Algebra k K]
    [IsScalarTower k F K] [FiniteDimensional F K] [Algebra.IsSeparable F K]
    [CommRing R] [Algebra k R] [Algebra.FiniteType k R] (f : R →ₐ[k] K)
    (H : ∀ D : P, D ≠ 0 → ∃ ψ : P →ₐ[k] k, ψ D ≠ 0) :
    Nonempty (R →ₐ[k] k) := by
  classical
  let pb := Field.powerBasisOfFiniteOfSeparable F K
  set y := pb.gen
  have hy : IsIntegral F y := pb.isIntegral_gen
  obtain ⟨u, v, huv⟩ : (minpoly F y).Separable := Algebra.IsSeparable.isSeparable F y
  obtain ⟨n, π, hπ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType k R›
  choose Q hQ using fun i : Fin n => pb.exists_eq_aeval' (f (π (MvPolynomial.X i)))
  change ∀ i, _ = aeval y (Q i) at hQ
  -- the finitely many coefficients to be spread out
  let S : Finset F := (minpoly F y).coeffs ∪ u.coeffs ∪ v.coeffs ∪
    Finset.univ.biUnion fun i => (Q i).coeffs
  obtain ⟨⟨D, hD⟩, hS⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors P) S
  obtain ⟨ψ₀, hψ₀⟩ := H D (nonZeroDivisors.ne_zero hD)
  let C := Localization.Away D
  have hDF : IsUnit (IsScalarTower.toAlgHom k P F D) :=
    (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hD).isUnit
  let ι : C →ₐ[k] F := IsLocalization.Away.liftAlgHom D hDF
  let ψ : C →ₐ[k] k := IsLocalization.Away.liftAlgHom D hψ₀.isUnit
  have hι : Function.Injective ι := by
    change Function.Injective (IsLocalization.Away.lift D hDF)
    refine (IsLocalization.lift_injective_iff _).mpr fun a b => ⟨fun h => ?_, fun h => ?_⟩
    · simpa using congrArg (IsLocalization.Away.lift D hDF) h
    · rw [IsFractionRing.injective P F h]
  have hrange : ∀ q ∈ S, q ∈ Set.range ι := by
    intro q hq
    obtain ⟨a, ha⟩ := hS q hq
    refine ⟨IsLocalization.mk' C a (⟨D, Submonoid.mem_powers D⟩ : Submonoid.powers D), ?_⟩
    change IsLocalization.lift _ _ = q
    rw [IsLocalization.lift_mk'_spec]
    simpa [Algebra.smul_def] using ha
  have hlift : ∀ p : F[X], p.coeffs ⊆ S → ∃ p' : C[X], p'.map (ι : C →+* F) = p := by
    intro p hp
    refine (mem_lifts p).mp ((lifts_iff_coeff_lifts p).mpr fun m => ?_)
    by_cases hm : p.coeff m = 0
    · exact ⟨0, by simp [hm]⟩
    · exact hrange _ (hp (coeff_mem_coeffs hm))
  obtain ⟨g', hg'⟩ := hlift (minpoly F y) fun a ha => by simp [S, ha]
  obtain ⟨u', hu'⟩ := hlift u fun a ha => by simp [S, ha]
  obtain ⟨v', hv'⟩ := hlift v fun a ha => by simp [S, ha]
  choose Q' hQ' using fun i => hlift (Q i) fun a ha => by
    simp only [S, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact Or.inr ⟨i, ha⟩
  have hsep : g'.Separable := by
    refine ⟨u', v', Polynomial.map_injective (ι : C →+* F) hι ?_⟩
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, ← derivative_map, hg', hu',
      hv', huv, Polynomial.map_one]
  obtain ⟨t, ht⟩ := exists_forall_eval_map_eq_zero (ι : C →+* F) hι (ψ : C →+* k) hy hg' hsep
  let Θ : MvPolynomial (Fin n) k →ₐ[k] C[X] := MvPolynomial.aeval Q'
  have hE : ((aeval y).restrictScalars k).comp ((mapAlgHom ι).comp Θ) = f.comp π := by
    refine MvPolynomial.algHom_ext fun i => ?_
    simp [Θ, hQ' i, hQ i]
  let Φ : MvPolynomial (Fin n) k →ₐ[k] k := (aeval t).comp ((mapAlgHom ψ).comp Θ)
  have hker : ∀ z ∈ RingHom.ker π, Φ z = 0 := by
    intro z hz
    have hz' : aeval y ((Θ z).map (ι : C →+* F)) = 0 := by
      have := DFunLike.congr_fun hE z
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, coe_mapAlgHom] at this
      rw [this, RingHom.mem_ker.mp hz, map_zero]
    have := ht (Θ z) hz'
    simpa [Φ, coe_aeval_eq_eval] using this
  exact ⟨(Ideal.Quotient.liftₐ (RingHom.ker π) Φ hker).comp
    (Ideal.quotientKerAlgEquivOfSurjective hπ).symm.toAlgHom⟩

end Langlands.CommutativeAlgebra.RationalPointSpecialization
