/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.QuasiFiniteAtPrime
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.RingTheory.DimensionQuasiFiniteOverPolynomialAlgebra
import WeilConjectures.RingTheory.QuasiFiniteFourRings
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Fibre dimension bound from a quasi-finite polynomial factorization

Source: Stacks Project, proof of Tag 00QH, after the application of Tag 00QE.
(blueprint: lem-weil-pbc-fibre-dimension-bound-of-polynomial-factorization).
-/

@[expose] public section

universe u v


namespace Algebra

open scoped _root_.TensorProduct in
set_option backward.isDefEq.respectTransparency false in
private theorem polynomial_factorization_baseChange
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (A : Type*) [CommRing A] [Algebra R A] (n : ℕ)
    (f : MvPolynomial (Fin n) R →ₐ[R] S)
    (hft : @FiniteType (MvPolynomial (Fin n) R) S _ _ f.toRingHom.toAlgebra)
    (hq : ∀ q : PrimeSpectrum S,
      @IsQuasiFiniteAtPrime (MvPolynomial (Fin n) R) S
        _ _ f.toRingHom.toAlgebra hft q) :
    ∃ φ : MvPolynomial (Fin n) A →ₐ[A] A ⊗[R] S,
      ∃ hφ : @FiniteType (MvPolynomial (Fin n) A) (A ⊗[R] S)
        _ _ φ.toRingHom.toAlgebra,
      ∀ q : PrimeSpectrum (A ⊗[R] S),
        @IsQuasiFiniteAtPrime (MvPolynomial (Fin n) A) (A ⊗[R] S)
          _ _ φ.toRingHom.toAlgebra hφ q := by
  classical
  let P := MvPolynomial (Fin n) R
  let P' := MvPolynomial (Fin n) A
  let T := A ⊗[R] S
  let φ : P' →ₐ[A] T :=
    (Algebra.TensorProduct.map (AlgHom.id A A) f).comp
      (MvPolynomial.algebraTensorAlgEquiv R A).symm.toAlgHom
  let : Algebra P S := f.toRingHom.toAlgebra
  let : FiniteType P S := hft
  let : Algebra P P' := (MvPolynomial.map (algebraMap R A)).toAlgebra
  let : Algebra P' T := φ.toRingHom.toAlgebra
  let : Algebra S T := Algebra.TensorProduct.rightAlgebra
  let : Algebra P T :=
    ((Algebra.TensorProduct.includeRight (R := R) (A := A)).comp f).toRingHom.toAlgebra
  have : IsScalarTower P S T := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower P P' T := IsScalarTower.of_algebraMap_eq fun x ↦ by
    change (1 : A) ⊗ₜ[R] f x = φ (MvPolynomial.map (algebraMap R A) x)
    change 1 ⊗ₜ[R] f x = Algebra.TensorProduct.map (AlgHom.id A A) f
      ((MvPolynomial.algebraTensorAlgEquiv R A).symm
        (MvPolynomial.map (algebraMap R A) x))
    rw [MvPolynomial.algebraTensorAlgEquiv_symm_map]
    simp
  have hgen : ∀ x : T, ∃ (m : ℕ) (s : Fin m → S) (r : Fin m → P'),
      x = ∑ i, algebraMap S T (s i) * algebraMap P' T (r i) := by
    intro x
    obtain ⟨m, a, s, hx⟩ := TensorProduct.exists_sum_tmul_eq x
    refine ⟨m, s, fun i ↦ MvPolynomial.C (a i), ?_⟩
    rw [hx]
    congr 1
    funext i
    change a i ⊗ₜ[R] s i = (1 ⊗ₜ[R] s i) * φ (MvPolynomial.C (a i))
    rw [show MvPolynomial.C (a i) = algebraMap A P' (a i) from rfl, φ.commutes]
    change a i ⊗ₜ[R] s i = (1 ⊗ₜ[R] s i) * (a i ⊗ₜ[R] (1 : S))
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  obtain ⟨hφ, hqφ⟩ := finiteType_and_isQuasiFiniteAtPrime_of_four_rings
    P S P' T hgen
  exact ⟨φ, hφ, fun q ↦ hqφ q (hq _)⟩

set_option backward.isDefEq.respectTransparency false in
/-- A quasi-finite factorization of `R → S[g⁻¹]` through a polynomial algebra in `n`
variables bounds the local dimensions of all the original fibres at primes in `D(g)`.
No distinguished prime or initial fibre-dimension hypothesis is needed.

Source: Stacks Project, Algebra, proof of Tag 00QH, the sentence "Considering the fibres",
using Tags 00PN, 00QG and 00E4.
(blueprint: lem-weil-pbc-fibre-dimension-bound-of-polynomial-factorization).

Proof: fix `q ∈ D(g)` and let `p` be its contraction to `R`. Localize `q` to a prime
`qg` of `S[g⁻¹]`; its contraction to `R` remains `p`. Write `k = κ(p)` and
`T = k ⊗[R] S[g⁻¹]`. Base change the given map to `k`. Polynomial scalar extension
identifies its source with `k[t₁, …, tₙ]`, and tensor cancellation identifies its target
with `T`. The four-rings theorem (Tag 00PN) makes this map finite type and quasi-finite
at every prime: the relevant tensor-product map is an isomorphism, hence surjective.
Also `T` is finite type over `k`, since the generators of `S` and `g⁻¹` generate it.
Tag 00QG bounds the global dimension of `Spec T` by `n`, so its local dimension at the
fibre prime corresponding to `qg` is at most `n` (local dimension is an infimum over
open neighbourhoods, including the whole space).

Localization commutes with base change, so `T` is the localization of `k ⊗[R] S` at
the image of `g`. Its spectrum is the principal open of that image. Under the fibre-prime
bijections the point for `qg` maps to the point for `q`: this follows by contraction,
since the bijection's inverse is contraction along the canonical tensor inclusion.
The latter point lies in this principal open because `g ∉ q`. The local dimension
at a point is invariant under an open-subspace inclusion. Thus the bound on `Spec T`
is exactly the asserted bound on the original fibre.

Edge cases: `n = 0` uses the same dimension bound; if `D(g)` is empty the conclusion is
vacuous. Neither injectivity of the polynomial map nor a domain hypothesis is needed. -/
theorem fibre_dimension_le_of_quasiFinite_polynomial_localization
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [FiniteType R S] (g : S) (n : ℕ)
    (f : MvPolynomial (Fin n) R →ₐ[R] Localization.Away g)
    (hft : @FiniteType (MvPolynomial (Fin n) R) (Localization.Away g)
      _ _ f.toRingHom.toAlgebra)
    (hq : ∀ qg : PrimeSpectrum (Localization.Away g),
      @IsQuasiFiniteAtPrime (MvPolynomial (Fin n) R) (Localization.Away g)
        _ _ f.toRingHom.toAlgebra hft qg)
    (q : PrimeSpectrum S) (hg : g ∉ q.asIdeal) :
    topologicalKrullDimAt
      (PrimeSpectrum.preimageEquivFiber R S (q.comap (algebraMap R S))
        ⟨q, rfl⟩) ≤ (n : WithBot ℕ∞) := open scoped _root_.TensorProduct in by
  classical
  let p := q.comap (algebraMap R S)
  let k := p.asIdeal.ResidueField
  let F := p.asIdeal.Fiber S
  let T := p.asIdeal.Fiber (Localization.Away g)
  let Q : PrimeSpectrum F := PrimeSpectrum.preimageEquivFiber R S p ⟨q, rfl⟩
  obtain ⟨φ, hφ, hqφ⟩ := polynomial_factorization_baseChange k n f hft hq
  let : Algebra (MvPolynomial (Fin n) k) T := φ.toRingHom.toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin n) k) T :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (φ.commutes x).symm
  have : FiniteType k T := FiniteType.trans
    (inferInstance : FiniteType k (MvPolynomial (Fin n) k)) hφ
  have hdim := AlgebraicGeometry.topologicalKrullDim_spec_le_of_quasiFinite_over_mvPolynomial
    k n T φ hφ hqφ
  change topologicalKrullDim (PrimeSpectrum T) ≤ (n : WithBot ℕ∞) at hdim
  let j : F →ₐ[k] T := Algebra.TensorProduct.map (AlgHom.id k k)
    (IsScalarTower.toAlgHom R S (Localization.Away g))
  let : Algebra F T := j.toRingHom.toAlgebra
  have : IsScalarTower k F T := IsScalarTower.of_algebraMap_eq fun x ↦ (j.commutes x).symm
  have hloc := IsLocalization.tensorProduct_tensorProduct_right R k (Submonoid.powers g)
    (Localization.Away g) (by
      ext x
      change j (1 ⊗ₜ[R] x) = 1 ⊗ₜ[R] algebraMap S (Localization.Away g) x
      exact Algebra.TensorProduct.map_tmul (AlgHom.id k k)
        (IsScalarTower.toAlgHom R S (Localization.Away g)) 1 x)
  have : IsLocalization.Away
      (Algebra.TensorProduct.includeRight (R := R) (A := k) g) T := by
    simpa only [Submonoid.map_powers] using hloc
  let b : F := Algebra.TensorProduct.includeRight g
  have hj := PrimeSpectrum.localization_away_isOpenEmbedding T b
  have hr := PrimeSpectrum.localization_away_comap_range T b
  have hQ : Q.comap Algebra.TensorProduct.includeRight.toRingHom = q :=
    congrArg Subtype.val ((PrimeSpectrum.preimageEquivFiber R S p).symm_apply_apply ⟨q, rfl⟩)
  have hmem : Q ∈ PrimeSpectrum.basicOpen b := by
    change g ∉ (Q.comap Algebra.TensorProduct.includeRight.toRingHom).asIdeal
    rw [hQ]
    exact hg
  have hbasic : topologicalKrullDim (PrimeSpectrum.basicOpen b) ≤ (n : WithBot ℕ∞) := by
    let e := hj.toIsEmbedding.toHomeomorph
    have he := IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph
    rw [hr] at he
    exact he.symm.trans_le hdim
  exact (iInf₂_le (PrimeSpectrum.basicOpen b) hmem).trans hbasic

end Algebra
