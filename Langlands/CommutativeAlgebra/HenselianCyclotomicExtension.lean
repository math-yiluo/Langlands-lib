import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCompleteEtaleCover
import Langlands.CommutativeAlgebra.HenselianEtaleAlgebraLift
import Langlands.CommutativeAlgebra.RegularLocalFactorialProof
import WeilConjectures.RingTheory.FiniteLocalHenselian
import WeilConjectures.RingTheory.Etale.IntegrallyClosed
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.Etale.Field

/-! # Finite étale local extensions carrying roots of unity and a residue automorphism -/

noncomputable section

universe u

open Polynomial IsLocalRing TensorProduct

namespace Langlands.CommutativeAlgebra.HenselianCyclotomicExtension

/-- Two `n`-th roots of unity with the same image in a field agree when `n` is nonzero in the
field and every element with nonzero image is a unit. -/
theorem eq_of_pow_eq_one {A F : Type*} [CommRing A] [Field F] (π : A →+* F)
    (hπ : ∀ x, π x ≠ 0 → IsUnit x) {n : ℕ} (hn : (n : F) ≠ 0) {a b : A}
    (ha : a ^ n = 1) (hb : b ^ n = 1) (hab : π a = π b) : a = b := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hsum : (∑ i ∈ Finset.range n, a ^ i * b ^ (n - 1 - i)) * (a - b) = 0 := by
    rw [geom_sum₂_mul, ha, hb, sub_self]
  have hπa : π a ≠ 0 := by
    intro h
    have := congrArg π ha
    rw [map_pow, h, map_one, zero_pow hn0] at this
    exact zero_ne_one this
  have hunit : IsUnit (∑ i ∈ Finset.range n, a ^ i * b ^ (n - 1 - i)) := by
    apply hπ
    rw [map_sum]
    simp only [map_mul, map_pow, ← hab]
    rw [geom_sum₂_self]
    exact mul_ne_zero hn (pow_ne_zero _ hπa)
  exact sub_eq_zero.mp ((hunit.mul_right_eq_zero).mp hsum)

variable {R : Type u} [CommRing R] [IsDomain R] [IsRegularLocalRing R] [HenselianLocalRing R]

omit [IsDomain R] [HenselianLocalRing R] in
/-- An étale `R`-algebra `S` with a prime `z` over the maximal ideal of `R` has an `R`-algebra
map to the separable closure of the residue field `k`. The prime `z` certifies that the closed
fibre `k ⊗[R] S` is nonempty; the map is obtained from a maximal ideal of that fibre, not
necessarily from `z` itself. -/
theorem exists_residuePoint (S : Type u) [CommRing S] [Algebra R S] [Algebra.Etale R S]
    (z : Ideal S) [z.IsPrime] (hz : z.comap (algebraMap R S) = maximalIdeal R) :
    Nonempty (S →ₐ[R] SeparableClosure (ResidueField R)) := by
  classical
  let k := ResidueField R
  let A := k ⊗[R] S
  have hk : ∀ a ∈ maximalIdeal R, (Algebra.ofId R (S ⧸ z)) a = 0 := by
    intro a ha
    change Ideal.Quotient.mk z (algebraMap R S a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, hz]
    exact ha
  let f : A →ₐ[R] S ⧸ z := Algebra.TensorProduct.productMap
    (Ideal.Quotient.liftₐ (maximalIdeal R) (Algebra.ofId R (S ⧸ z)) hk)
    (Ideal.Quotient.mkₐ R z)
  have : Nontrivial A := f.toRingHom.domain_nontrivial
  obtain ⟨M, hM⟩ := Ideal.exists_maximal A
  let := Ideal.Quotient.field M
  have : Algebra.IsSeparable k (A ⧸ M) := inferInstance
  let ι : A ⧸ M →ₐ[k] SeparableClosure k := IsSepClosed.lift
  exact ⟨((ι.restrictScalars R).comp (Ideal.Quotient.mkₐ R M)).comp
    Algebra.TensorProduct.includeRight⟩

/-- A finite subset of a normal extension `K` of `k` lies in an intermediate field which is
finite-dimensional and normal over `k`, namely the normal closure of the field it generates. -/
theorem exists_finiteDimensional_normal {k K : Type*} [Field k] [Field K] [Algebra k K]
    [Normal k K] (T : Set K) (hT : T.Finite) :
    ∃ k' : IntermediateField k K, FiniteDimensional k k' ∧ Normal k k' ∧ T ⊆ k' := by
  have : Finite T := hT.to_subtype
  have : FiniteDimensional k (IntermediateField.adjoin k T) :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  exact ⟨IntermediateField.normalClosure k (IntermediateField.adjoin k T) K,
    normalClosure.is_finiteDimensional k _ K, normalClosure.normal k _ K,
    fun x hx => IntermediateField.le_normalClosure _ (IntermediateField.subset_adjoin k T hx)⟩

local notation "𝓀" => ResidueField R
local notation "𝓚" => SeparableClosure (ResidueField R)

omit [IsDomain R] [HenselianLocalRing R] in
/-- A finite-dimensional intermediate field `k'` of `SeparableClosure k` over the residue field
`k` of a regular local ring `R` is a quotient of a finite étale local `R`-algebra. -/
theorem exists_etaleCover_intermediateField (k' : IntermediateField 𝓀 𝓚)
    [FiniteDimensional 𝓀 k'] :
    ∃ (L : Type u) (_ : CommRing L) (_ : Algebra R L), IsLocalRing L ∧ Module.Finite R L ∧
      Algebra.Etale R L ∧ ∃ π : L →ₐ[R] k', Function.Surjective π := by
  have : Algebra.IsSeparable 𝓀 k' := inferInstance
  have : Algebra.FormallyUnramified 𝓀 k' := Algebra.FormallyUnramified.of_isSeparable 𝓀 k'
  have : Algebra.FormallyUnramified R 𝓀 :=
    Algebra.FormallyUnramified.of_surjective (Algebra.ofId R 𝓀) residue_surjective
  have : Algebra.FormallyUnramified R k' := Algebra.FormallyUnramified.comp R 𝓀 k'
  have : IsLocalHom (algebraMap R k') := ⟨fun x hx => by
    by_contra h
    have h0 : algebraMap R 𝓀 x = 0 :=
      (IsLocalRing.residue_eq_zero_iff x).mpr ((mem_maximalIdeal x).mpr h)
    have hK : IsUnit (algebraMap R 𝓚 x) := hx.map (algebraMap k' 𝓚)
    rw [IsScalarTower.algebraMap_apply R 𝓀 𝓚, h0, map_zero] at hK
    exact not_isUnit_zero hK⟩
  have h𝓀 : Module.Finite R 𝓀 :=
    Module.Finite.of_surjective (Algebra.linearMap R 𝓀) residue_surjective
  have : Module.Finite R k' := Module.Finite.trans 𝓀 k'
  exact Langlands.AlgebraicGeometry.UnramifiedFunctor.CompleteLocal.exists_etaleCover

/-- A finite-dimensional intermediate field `k'` of `SeparableClosure k` over the residue field
`k` of a Henselian regular local ring `R` is the residue field of a finite étale `R`-algebra `L`
which is a Henselian local domain into which `R` injects. -/
theorem exists_domainCover (k' : IntermediateField 𝓀 𝓚) [FiniteDimensional 𝓀 k'] :
    ∃ (L : Type u) (_ : CommRing L) (_ : IsDomain L) (_ : HenselianLocalRing L) (_ : Algebra R L),
      Module.Finite R L ∧ Algebra.Etale R L ∧ Function.Injective (algebraMap R L) ∧
      ∃ π : L →ₐ[R] k', Function.Surjective π ∧ ∀ x, π x ≠ 0 → IsUnit x := by
  obtain ⟨L, _, _, hLloc, hLfin, hLet, π, hπ⟩ := exists_etaleCover_intermediateField (R := R) k'
  have := hLloc
  have := hLfin
  have := hLet
  have : HenselianLocalRing L := HenselianLocalRing.finite_local_henselian R L
  have : UniqueFactorizationMonoid R :=
    Langlands.CommutativeAlgebra.regularLocalFactorial R inferInstance
  have : IsLocalization.AtPrime L (maximalIdeal L) :=
    IsLocalization.of_le_isUnit (fun x hx => IsLocalRing.notMem_maximalIdeal.mp hx)
  have hdom := Algebra.Etale.isDomain_and_isIntegrallyClosed_of_isLocalization (R := R) (B := L)
    (maximalIdeal L) L
  have : IsDomain L := hdom.1
  have hker : RingHom.ker π.toRingHom = maximalIdeal L :=
    IsLocalRing.ker_eq_maximalIdeal π.toRingHom hπ
  have hunit : ∀ x : L, π x ≠ 0 → IsUnit x := by
    intro x hx
    by_contra h
    have hm : x ∈ maximalIdeal L := h
    rw [← hker] at hm
    exact hx hm
  have hinj : Function.Injective (algebraMap R L) := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    by_contra hr0
    have hreg : IsSMulRegular L r :=
      Module.Flat.isSMulRegular_of_isRegular (IsRegular.of_ne_zero hr0)
    have : r • (1 : L) = r • (0 : L) := by rw [Algebra.smul_def, hr, zero_mul, smul_zero]
    exact one_ne_zero (hreg this)
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, hLfin, hLet, hinj, π, hπ,
    hunit⟩

omit [IsRegularLocalRing R] [HenselianLocalRing R] in
/-- In a Henselian local ring `L` in which `n` is a unit, an `n`-th root of unity of a field
quotient `π : L →+* F` whose kernel consists of the non-units lifts to an `n`-th root of unity
of `L`. -/
theorem exists_root_of_unity_lift {L F : Type*} [CommRing L] [HenselianLocalRing L] [Field F]
    (π : L →+* F) (hπ : Function.Surjective π) (hunit : ∀ x, π x ≠ 0 → IsUnit x) {n : ℕ}
    (hn : IsUnit (n : L)) (hn0 : n ≠ 0) (ζ₀ : F) (hζ₀ : ζ₀ ^ n = 1) :
    ∃ ζ : L, ζ ^ n = 1 ∧ π ζ = ζ₀ := by
  have hmem : ∀ x : L, x ∈ maximalIdeal L ↔ π x = 0 := by
    intro x
    constructor
    · intro hx
      by_contra h
      exact hx (hunit x h)
    · intro hx hu
      have := hu.map π
      rw [hx] at this
      exact not_isUnit_zero this
  obtain ⟨a₀, ha₀⟩ := hπ ζ₀
  have hζ₀0 : ζ₀ ≠ 0 := by
    rintro rfl
    rw [zero_pow hn0] at hζ₀
    exact zero_ne_one hζ₀
  have ha₀u : IsUnit a₀ := hunit a₀ (by rw [ha₀]; exact hζ₀0)
  have hmon : ((X : L[X]) ^ n - C 1).Monic := monic_X_pow_sub_C 1 hn0
  have h1 : ((X : L[X]) ^ n - C 1).eval a₀ ∈ maximalIdeal L := by
    rw [hmem]
    simp [ha₀, hζ₀]
  have h2 : IsUnit (((X : L[X]) ^ n - C 1).derivative.eval a₀) := by
    simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul, eval_C,
      eval_pow, eval_X]
    exact IsUnit.mul (by simpa using hn) (ha₀u.pow _)
  obtain ⟨ζ, hζroot, hζa⟩ := HenselianLocalRing.is_henselian _ hmon a₀ h1 h2
  refine ⟨ζ, ?_, ?_⟩
  · simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_C] at hζroot
    exact sub_eq_zero.mp hζroot
  · rw [hmem, map_sub, ha₀, sub_eq_zero] at hζa
    exact hζa

/-- **Finite étale local extensions with a primitive root of unity and a residue lift.**
Let `R` be a Henselian regular local ring with residue field `k`, `n` invertible in `R`, and
`φ` a `k`-automorphism of `SeparableClosure k` with `φ ζ = ζ ^ q` for every `n`-th root of
unity `ζ`. For an étale `R`-algebra `S` with a prime over the maximal ideal there is a finite
étale `R`-algebra `R'` which is a domain into which `R` injects, with an `R`-algebra map
`S → R'`, an element `ζ` with `ζ ^ n = 1` and `ζ ^ l - 1` a unit for `0 < l < n`, and an
`R`-algebra endomorphism `α` of `R'` with `α ζ = ζ ^ q`. -/
theorem exists_extension (n : ℕ) (hn : IsUnit (n : R)) (q : ℕ)
    (φ : SeparableClosure (ResidueField R) ≃ₐ[ResidueField R] SeparableClosure (ResidueField R))
    (hφ : ∀ ζ : SeparableClosure (ResidueField R), ζ ^ n = 1 → φ ζ = ζ ^ q)
    (S : Type u) [CommRing S] [Algebra R S] [Algebra.Etale R S]
    (z : Ideal S) [z.IsPrime] (hz : z.comap (algebraMap R S) = maximalIdeal R) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : Algebra R R'),
      Module.Finite R R' ∧ Algebra.Etale R R' ∧ Function.Injective (algebraMap R R') ∧
      ∃ (ζ : R') (α : R' →ₐ[R] R') (_ : S →ₐ[R] R'), ζ ^ n = 1 ∧
        (∀ l, 0 < l → l < n → IsUnit (ζ ^ l - 1)) ∧ α ζ = ζ ^ q := by
  classical
  obtain ⟨ψ₀⟩ := exists_residuePoint S z hz
  have hnk : (n : 𝓀) ≠ 0 := by
    have h := hn.map (residue R)
    rw [map_natCast] at h
    exact h.ne_zero
  have hnK : (n : 𝓚) ≠ 0 := by
    rw [← map_natCast (algebraMap 𝓀 𝓚)]
    exact (_root_.map_ne_zero _).mpr hnk
  have hn0 : n ≠ 0 := by rintro rfl; exact hnk Nat.cast_zero
  have : NeZero (n : 𝓚) := ⟨hnK⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot 𝓚 n
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := S)
  obtain ⟨k', hk'fin, hk'norm, hT⟩ := exists_finiteDimensional_normal (k := 𝓀)
    ((ψ₀ '' (s : Set S)) ∪ {ζ₀}) ((s.finite_toSet.image _).union (Set.finite_singleton ζ₀))
  obtain ⟨L, _, _, _, _, hLfin, hLet, hinj, π, hπ, hunit⟩ := exists_domainCover (R := R) k'
  let : Algebra L k' := π.toRingHom.toAlgebra
  have : IsScalarTower R L k' := IsScalarTower.of_algebraMap_eq (fun x => (π.commutes x).symm)
  -- The map `S → L`.
  have hψ : ∀ x, ψ₀ x ∈ k' := by
    have hle : Algebra.adjoin R (s : Set S) ≤
        (k'.toSubalgebra.restrictScalars R).comap ψ₀ := by
      rw [Algebra.adjoin_le_iff]
      intro x hx
      exact hT (Or.inl ⟨x, hx, rfl⟩)
    intro x
    exact hle (hs ▸ Algebra.mem_top : x ∈ Algebra.adjoin R (s : Set S))
  let ψ' : S →ₐ[R] k' := ψ₀.codRestrict (k'.toSubalgebra.restrictScalars R) hψ
  obtain ⟨b, -⟩ := HenselianEtaleAlgebraLift.exists_lift (P := R) (A := L) (K := k') (E := S)
    hπ ψ'
  refine ⟨L, inferInstance, inferInstance, inferInstance, hLfin, hLet, hinj, ?_⟩
  -- The endomorphism `α`.
  let φk : k' ≃ₐ[𝓀] k' := φ.restrictNormal k'
  have hφk : ∀ x : k', (φk x : 𝓚) = φ x := fun x => AlgEquiv.restrictNormal_commutes φ k' x
  obtain ⟨α, hα⟩ := HenselianEtaleAlgebraLift.exists_lift (P := R) (A := L) (K := k') (E := L)
    hπ ((φk.toAlgHom.restrictScalars R).comp π)
  have hαπ : ∀ x, π (α x) = φk (π x) := fun x => AlgHom.congr_fun hα x
  -- The root of unity `ζ`.
  let ζ₀' : k' := ⟨ζ₀, hT (Or.inr rfl)⟩
  have hζ₀' : ζ₀' ^ n = 1 := Subtype.ext (by simpa using hζ₀.pow_eq_one)
  have hnL : IsUnit (n : L) := by simpa using hn.map (algebraMap R L)
  obtain ⟨ζ, hζn, hπζ⟩ := exists_root_of_unity_lift π.toRingHom hπ hunit hnL hn0 ζ₀' hζ₀'
  refine ⟨ζ, α, b, hζn, ?_, ?_⟩
  · intro l hl0 hln
    apply hunit
    rw [map_sub, map_pow, map_one]
    erw [hπζ]
    intro h
    apply hζ₀.pow_ne_one_of_pos_of_lt hl0.ne' hln
    have := congrArg (fun x : k' => (x : 𝓚)) (sub_eq_zero.mp h)
    simpa [ζ₀'] using this
  · have hnk' : (n : k') ≠ 0 := by
      rw [← map_natCast (algebraMap 𝓀 k')]
      exact (_root_.map_ne_zero _).mpr hnk
    refine eq_of_pow_eq_one π.toRingHom hunit hnk' ?_ ?_ ?_
    · rw [← map_pow, hζn, map_one]
    · rw [← pow_mul, mul_comm, pow_mul, hζn, one_pow]
    · change π (α ζ) = π (ζ ^ q)
      rw [hαπ, map_pow]
      erw [hπζ]
      apply Subtype.ext
      rw [hφk]
      simpa [ζ₀'] using hφ ζ₀ hζ₀.pow_eq_one

end Langlands.CommutativeAlgebra.HenselianCyclotomicExtension
