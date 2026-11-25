module

public import StacksFrontier.RingTheory.DiscreteValuationRing.ArtinSchreier.OrbitPolynomial
import all StacksFrontier.RingTheory.DiscreteValuationRing.ArtinSchreier.OrbitPolynomial

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Eliminating degree-prime ramification: weak solutions and the orbit extension

Weak solutions obtained from weakly unramified extensions, ramification indices under
localization and surjective base change, and the totally ramified Galois orbit extension.

## Main results

* `IsDiscreteValuationRing.exists_isGalois_totallyRamified_orbitExtension_forall_depth`: the orbit
  extension built from a prescribed depth and rank, with its translation subgroup certified at
  every smaller depth.
-/

@[expose] public section

open Polynomial
open nonZeroDivisors
open WithZero

open scoped TensorProduct

attribute [local instance] FractionRing.liftAlgebra
attribute [local instance] Ideal.Quotient.field

universe uA uB uC uK uL uM uK₁

namespace IsDiscreteValuationRing

/-- A surjective algebra has ramification index one at every prime. -/
private theorem ramificationIdx_eq_one_of_surjective {S T : Type*} [CommRing S] [CommRing T]
    [Algebra S T] (hsurj : Function.Surjective (algebraMap S T)) (q : Ideal T) [q.IsPrime] :
    q.ramificationIdx S = 1 := by
  have : Algebra.FormallyUnramified S T :=
    Algebra.FormallyUnramified.of_surjective (Algebra.ofId S T) hsurj
  have : Algebra.FiniteType S T := Algebra.FiniteType.of_surjective (Algebra.ofId S T) hsurj
  have : Algebra.IsUnramifiedAt S q :=
    Algebra.FormallyUnramified.comp S T (Localization.AtPrime q)
  exact Ideal.ramificationIdx_eq_one q S

/-- If an `R`-algebra `E` embeds into the fraction field of an integrally closed domain `R`
compatibly with `R`, then `R` surjects onto the integral closure of `R` in `E`. -/
private theorem algebraMap_integralClosure_surjective_of_embedding {R F E : Type*} [CommRing R]
    [IsDomain R] [IsIntegrallyClosed R] [Field F] [Algebra R F] [IsFractionRing R F]
    [CommRing E] [Algebra R E] (ψ : E →+* F) (hψ : Function.Injective ψ)
    (hcomp : ψ.comp (algebraMap R E) = algebraMap R F) :
    Function.Surjective (algebraMap R (integralClosure R E)) := by
  intro x
  have hx : IsIntegral R (ψ x) := by
    obtain ⟨P, hmonic, hP⟩ := x.2
    refine ⟨P, hmonic, ?_⟩
    rw [← hcomp, ← Polynomial.hom_eval₂, hP, map_zero]
  obtain ⟨c, hc⟩ := (IsIntegrallyClosed.isIntegral_iff (R := R) (K := F)).mp hx
  refine ⟨c, Subtype.ext (hψ ?_)⟩
  rw [← hc, ← hcomp]
  rfl

/-- A local domain `C` inside the fraction field of a Dedekind domain `S`, dominating the nonzero
prime `P = m_C ∩ S`, is the localisation of `S` at `P`. -/
private theorem isLocalization_atPrime_of_dominates {S C M : Type*}
    [CommRing S] [IsDedekindDomain S]
    [Field M] [Algebra S M] [IsFractionRing S M] [CommRing C] [IsLocalRing C]
    [Algebra S C] [Algebra C M] [IsScalarTower S C M]
    (hCM : Function.Injective (algebraMap C M))
    (hP : (IsLocalRing.maximalIdeal C).comap (algebraMap S C) ≠ ⊥) :
    IsLocalization.AtPrime C ((IsLocalRing.maximalIdeal C).comap (algebraMap S C)) := by
  classical
  set P := (IsLocalRing.maximalIdeal C).comap (algebraMap S C) with hPdef
  let Sp := Localization.AtPrime P
  have : IsDiscreteValuationRing Sp :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S hP Sp
  have hSM : Function.Injective (algebraMap S M) := IsFractionRing.injective S M
  have hSC : Function.Injective (algebraMap S C) := by
    intro x y h
    apply hSM
    rw [IsScalarTower.algebraMap_apply S C M, h, ← IsScalarTower.algebraMap_apply]
  have hSSp : Function.Injective (algebraMap S Sp) :=
    IsLocalization.injective Sp P.primeCompl_le_nonZeroDivisors
  have hunit : ∀ s : S, s ∉ P → IsUnit (algebraMap S C s) := fun s hs => by
    by_contra h
    exact hs ((IsLocalRing.mem_maximalIdeal _).mpr h)
  refine
    { map_units := fun s => hunit s s.2
      surj := fun c => ?_
      exists_of_eq := fun {x y} h => ⟨1, by simp [hSC h]⟩ }
  obtain ⟨⟨x, y⟩, hxy⟩ := IsLocalization.surj (nonZeroDivisors S) (algebraMap C M c)
  simp only at hxy
  have hy0 : (y : S) ≠ 0 := nonZeroDivisors.coe_ne_zero y
  have hcb : ∀ u v : S, x * u = y * v → c * algebraMap S C u = algebraMap S C v := fun u v h => by
    apply hCM
    apply mul_left_cancel₀ (show algebraMap S M y ≠ 0 from
      (map_ne_zero_iff _ hSM).mpr hy0)
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      ← mul_assoc, mul_comm (algebraMap S M y), hxy, ← map_mul, h, map_mul]
  rcases PreValuationRing.cond (algebraMap S Sp x) (algebraMap S Sp y) with ⟨w, hw⟩
  obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalization.surj P.primeCompl w
  simp only at hbs
  have hS : ∀ u v : S, algebraMap S Sp u * w = algebraMap S Sp v → u * b = v * s :=
    fun u v hw => by
      apply hSSp
      rw [map_mul, map_mul, ← hbs, ← mul_assoc, hw]
  rcases hw with hw | hw
  · have hcb' := hcb b s (hS x y hw)
    by_cases hb : b ∈ P
    · exfalso
      apply (s : P.primeCompl).2
      change algebraMap S C s ∈ IsLocalRing.maximalIdeal C
      rw [← hcb']
      exact Ideal.mul_mem_left _ _ hb
    · refine ⟨⟨s, ⟨b, hb⟩⟩, ?_⟩
      simpa [mul_comm] using hcb'
  · exact ⟨⟨b, s⟩, hcb s b (hS y x hw).symm⟩

/-- If every maximal ideal of the integral closure of `B` in `M` has ramification index one, then
every extension of discrete valuation rings `B → C` with fraction field `M` is weakly unramified.
-/
private theorem ramificationIndex_eq_of_ramificationIdx'_eq
    (B C L M : Type*) [CommRing B] [CommRing C] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing B] [IsDiscreteValuationRing C] [Field L] [Field M]
    [Algebra B C] [Algebra B L] [Algebra C M] [Algebra L M] [Algebra B M]
    [IsScalarTower B C M] [IsScalarTower B L M] [IsExtension B C]
    [IsFractionRing B L] [IsFractionRing C M] [FiniteDimensional L M] [Algebra.IsSeparable L M]
    (e : ℕ) (hunr : ∀ m : Ideal (integralClosure B M), m.IsMaximal →
      Ideal.ramificationIdx' (IsLocalRing.maximalIdeal B) m = e) :
    ramificationIndex B C = e := by
  classical
  let S := integralClosure B M
  have : IsDedekindDomain S := integralClosure.isDedekindDomain B L M
  have : IsFractionRing S M := integralClosure.isFractionRing_of_finite_extension L M
  have : Module.Finite B S := IsIntegralClosure.finite B L M S
  have hCM : Function.Injective (algebraMap C M) := IsFractionRing.injective C M
  have hint : ∀ x : S, IsIntegral C (x : M) := fun x => x.2.tower_top
  let f : S →+* C :=
    { toFun := fun x => IsIntegralClosure.mk' C (x : M) (hint x)
      map_one' := by apply hCM; simp
      map_mul' := fun x y => by apply hCM; simp
      map_zero' := by apply hCM; simp
      map_add' := fun x y => by apply hCM; simp }
  have hf : ∀ x : S, algebraMap C M (f x) = x := fun x =>
    IsIntegralClosure.algebraMap_mk' C (x : M) (hint x)
  let : Algebra S C := f.toAlgebra
  have : IsScalarTower S C M := IsScalarTower.of_algebraMap_eq fun x => (hf x).symm
  have : IsScalarTower B S C := IsScalarTower.of_algebraMap_eq fun b => by
    apply hCM
    change algebraMap C M (algebraMap B C b) = algebraMap C M (f (algebraMap B S b))
    rw [hf, ← IsScalarTower.algebraMap_apply]
    rfl
  let mC := IsLocalRing.maximalIdeal C
  let P := mC.comap (algebraMap S C)
  have hBC : Function.Injective (algebraMap B C) :=
    (faithfulSMul_iff_algebraMap_injective B C).mp inferInstance
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible B
  have hπP : algebraMap B S π ∈ P := by
    change algebraMap S C (algebraMap B S π) ∈ mC
    rw [← IsScalarTower.algebraMap_apply]
    exact map_nonunit (algebraMap B C) π ((IsLocalRing.mem_maximalIdeal _).mpr hπ.not_isUnit)
  have hP : P ≠ ⊥ := by
    intro h
    have : algebraMap B S π = 0 := by rwa [← Ideal.mem_bot, ← h]
    apply hπ.ne_zero
    apply (IsFractionRing.injective B L)
    apply (algebraMap L M).injective
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply B S M, this]
    simp
  have hloc : IsLocalization.AtPrime C P := isLocalization_atPrime_of_dominates hCM hP
  have : P.IsPrime := Ideal.comap_isPrime _ _
  have hPmax : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP
  have : Module.Flat S C := IsLocalization.flat C P.primeCompl
  have : mC.LiesOver P := ⟨rfl⟩
  have hSinj : Function.Injective (algebraMap B S) := by
    intro x y h
    apply IsFractionRing.injective B L
    apply (algebraMap L M).injective
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply B S M, h, ← IsScalarTower.algebraMap_apply B S M]
  have : Module.IsTorsionFree B S := Module.isTorsionFree_iff_algebraMap_injective.mpr hSinj
  have hone : mC.ramificationIdx S = 1 := by
    have : Algebra.FormallyUnramified S C :=
      Algebra.FormallyUnramified.of_isLocalization P.primeCompl
    have : Algebra.EssFiniteType S C := Algebra.EssFiniteType.of_isLocalization C P.primeCompl
    have : Algebra.IsUnramifiedAt S mC :=
      Algebra.FormallyUnramified.comp S C (Localization.AtPrime mC)
    exact Ideal.ramificationIdx_eq_one mC S
  rw [ramificationIndex_eq_ramificationIdx]
  rw [Ideal.ramificationIdx_tower (R := B) (S := S) (T := C) P mC, hone, mul_one]
  have hlies : P.LiesOver (IsLocalRing.maximalIdeal B) :=
    ⟨((IsLocalRing.isMaximal_iff B).mp
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := B) P)).symm⟩
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx _ P (IsDiscreteValuationRing.not_a_field B)]
  exact hunr P hPmax

private theorem isWeaklyUnramified_of_ramificationIdx'_eq_one
    (B C L M : Type*) [CommRing B] [CommRing C] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing B] [IsDiscreteValuationRing C] [Field L] [Field M]
    [Algebra B C] [Algebra B L] [Algebra C M] [Algebra L M] [Algebra B M]
    [IsScalarTower B C M] [IsScalarTower B L M] [IsExtension B C]
    [IsFractionRing B L] [IsFractionRing C M] [FiniteDimensional L M] [Algebra.IsSeparable L M]
    (hunr : ∀ m : Ideal (integralClosure B M), m.IsMaximal →
      Ideal.ramificationIdx' (IsLocalRing.maximalIdeal B) m = 1) :
    IsWeaklyUnramified B C :=
  ramificationIndex_eq_of_ramificationIdx'_eq B C L M 1 hunr

/-- The case `n = 0` of Tag 09F1: if `M / L` is generated by a root `z` of `X ^ p - X - ξ` with
`ξ` integral over `B`, then `C` is weakly unramified over `B` (Tag 09F0, clause (A)). -/
theorem isWeaklyUnramified_of_artinSchreier_integral
    (B C L M : Type*) [CommRing B] [CommRing C] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing B] [IsDiscreteValuationRing C] [Field L] [Field M]
    [Algebra B C] [Algebra B L] [Algebra C M] [Algebra L M] [Algebra B M]
    [IsScalarTower B C M] [IsScalarTower B L M] [IsExtension B C]
    [IsFractionRing B L] [IsFractionRing C M] [FiniteDimensional L M] [IsGalois L M]
    (p : ℕ) (hp : p.Prime) [CharP L p] (hdegree : Module.finrank L M = p)
    (ξ : L) (z : M) (hz : z ^ p - z = algebraMap L M ξ) (hgen : Algebra.adjoin L {z} = ⊤)
    (hξ : ∃ b : B, ξ = algebraMap B L b) :
    IsWeaklyUnramified B C := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible B
  obtain ⟨_, -, -, hA, -, -⟩ :=
    isGalois_and_ramification_cases_of_adjoin_root_artinSchreier B L M p hp ξ z hz
      hgen π hπ
  apply isWeaklyUnramified_of_ramificationIdx'_eq_one B C L M
  intro m hm
  rcases hA hξ with htriv | ⟨-, hunr⟩
  · exfalso
    have : Module.finrank L M = 1 :=
      (Algebra.finrank_eq_one_iff_bijective_algebraMap).mpr
        ⟨(algebraMap L M).injective, htriv⟩
    exact hp.one_lt.ne' (hdegree ▸ this)
  · obtain ⟨_, he, -⟩ := hunr m hm
    exact he

/-- Given a uniformizer `π` of a discrete valuation ring `A` of equal characteristic `p`, a depth
`N ≥ 1` and a rank `r`, there is a finite Galois extension `K₁ / K` of degree `p ^ r`, totally
ramified with respect to `A`, generated by an integral root `α` of `∏_{v ∈ V} (X - v) = π` for a
subgroup `V ⊆ π ^ N A` of order `p ^ r`. -/
theorem exists_isGalois_totallyRamified_orbitExtension
    (A : Type uA) (K : Type uK) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (p : ℕ) (hp : p.Prime) [CharP K p] (π : A) (hπ : Irreducible π)
    (depth rank : ℕ) (hdepth : 1 ≤ depth) :
    ∃ (K₁ : Type uK) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁) (_ : IsGalois K K₁),
      IsTotallyRamifiedWithRespectTo A K K₁ ∧ Module.finrank K K₁ = p ^ rank ∧
        ∃ (V : AddSubgroup A) (_ : Fintype V) (α : K₁), Fintype.card V = p ^ rank ∧ IsIntegral A α ∧
          (∀ v : V, (v : A) ∈ Ideal.span {π ^ depth}) ∧
          ∏ v : V, (α - algebraMap A K₁ v) = algebraMap A K₁ π := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : CharP A p := (algebraMap A K).charP (IsFractionRing.injective A K) p
  let : Algebra (ZMod p) A := ZMod.algebra A p
  obtain ⟨V, hVfin, hcard, hV⟩ := exists_finite_translation_subgroup_in_power
    (Constants := ZMod p) π hπ.ne_zero hπ.not_isUnit depth rank
  rw [ZMod.card] at hcard
  let mA : Ideal A := IsLocalRing.maximalIdeal A
  have hmA : mA = Ideal.span {π} := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  have hVmA : ∀ v : V, (v : A) ∈ mA := by
    intro v
    rw [hmA]
    exact Ideal.span_singleton_le_span_singleton.mpr (dvd_pow_self π (by omega)) (hV v)
  have hπmA : π ∈ mA := by rw [hmA]; exact Ideal.subset_span rfl
  have hπsq : π ∉ mA ^ 2 := by
    rw [hmA, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rintro ⟨c, hc⟩
    apply hπ.not_isUnit
    have : π * 1 = π * (π * c) := by rwa [mul_one, ← mul_assoc, ← pow_two]
    exact IsUnit.of_mul_eq_one c (mul_left_cancel₀ hπ.ne_zero this).symm
  let f : A[X] := orbitPolynomial V - C π
  have hmonic : f.Monic := by
    have orbit_monic : (orbitPolynomial V).Monic := monic_prod_X_sub_C _ _
    have orbit_positive : 0 < (orbitPolynomial V).degree :=
      natDegree_pos_iff_degree_pos.mp (by simp [orbitPolynomial, Fintype.card_pos])
    exact orbit_monic.sub_of_left (lt_of_le_of_lt degree_C_le orbit_positive)
  have hdeg : f.natDegree = Fintype.card V := by
    simp [f, orbitPolynomial]
  have heis : f.IsEisensteinAt mA :=
    orbitPolynomial_sub_C_isEisensteinAt V mA (Ideal.IsMaximal.ne_top inferInstance) hVmA π
      hπmA hπsq
  have hirrA : Irreducible f := heis.irreducible (Ideal.IsMaximal.isPrime inferInstance)
    hmonic.isPrimitive (by rw [hdeg]; exact Fintype.card_pos)
  have hirr : Irreducible (f.map (algebraMap A K)) :=
    (hmonic.irreducible_iff_irreducible_map_fraction_map).mp hirrA
  have : Fact (Irreducible (f.map (algebraMap A K))) := ⟨hirr⟩
  let K₁ := AdjoinRoot (f.map (algebraMap A K))
  let pb := AdjoinRoot.powerBasis hirr.ne_zero
  have : Module.Finite K K₁ := pb.finite
  have hgal : IsGalois K K₁ :=
    orbitPolynomial_sub_C_map_adjoinRoot_isGalois (IsFractionRing.injective A K) V π
  have hfinrank : Module.finrank K K₁ = Fintype.card V := by
    rw [pb.finrank, AdjoinRoot.powerBasis_dim, (hmonic.natDegree_map _), hdeg]
  let α : K₁ := AdjoinRoot.root (f.map (algebraMap A K))
  have hαf : aeval α f = 0 := by
    rw [← aeval_map_algebraMap K α f, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hαint : IsIntegral A α := ⟨f, hmonic, by rwa [← aeval_def]⟩
  have hprod : ∏ v : V, (α - algebraMap A K₁ v) = algebraMap A K₁ π := by
    have h := hαf
    simp only [f, orbitPolynomial, map_sub, aeval_C, map_prod, aeval_X] at h
    exact sub_eq_zero.mp h
  refine ⟨K₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hgal,
    ?_, hfinrank.trans hcard, V, hVfin, α, hcard, hαint, hV, hprod⟩
  let B := integralClosure A K₁
  obtain ⟨P, hPmax⟩ := Ideal.exists_maximal B
  have := hPmax
  apply isTotallyRamified_of_map_le_pow_finrank A K K₁ P
  have hunder : P.under A = mA := IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A P)
  have hmemP : ∀ a ∈ mA, algebraMap A B a ∈ P := by
    intro a ha
    rw [← hunder] at ha
    exact ha
  let αB : B := ⟨α, hαint⟩
  have hprodB : ∏ v : V, (αB - algebraMap A B v) = algebraMap A B π := by
    apply Subtype.ext
    simpa [αB] using hprod
  have hαP : αB ∈ P := by
    have hmem : ∏ v : V, (αB - algebraMap A B v) ∈ P := hprodB ▸ hmemP π hπmA
    obtain ⟨v, -, hv⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hPmax.isPrime)).mp hmem
    simpa using P.add_mem hv (hmemP v (hVmA v))
  change Ideal.map (algebraMap A B) mA ≤ _
  rw [hmA, Ideal.map_span, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff,
    hfinrank, ← hprodB]
  have := Ideal.prod_mem_prod (s := Finset.univ) (I := fun _ : V => P)
    (x := fun v : V => αB - algebraMap A B v)
    (fun v _ => P.sub_mem hαP (hmemP v (hVmA v)))
  rwa [Finset.prod_const, Finset.card_univ] at this

/-- **The orbit extension at a prescribed depth serves every smaller depth.**

Identical to `exists_isGalois_totallyRamified_orbitExtension` except that the translation
subgroup `V` is certified to lie in `π ^ N A` for **every** `N ≤ depth`, not only for `depth`
itself.  That is immediate — `π ^ depth` divides `π ^ N` — and it is the form a shared extension
has to be handed over in.

The point is the quantifier order.  A single extension is built once, from a depth and a rank
prescribed in advance; each consumer then draws on the same `V` and the same `α` at whatever depth
its own data demands.  Nothing is enlarged after the fact and no consumer is distinguished: the
extension does not depend on which consumer is asking, so the family of demands is met by one
object rather than by one object per demand amalgamated afterwards.

Depth is the parameter that behaves well this way; rank is not.  `Module.finrank K K₁ = p ^ rank`
pins the degree exactly, so a shared extension cannot simultaneously realise two different ranks,
and consumers must agree on one rank in advance rather than each choosing its own and meeting
later.  Supplying that agreement is what `exists_unique_max_scaled_pole_of_le` is for: it frees
the rank from being determined by a single consumer's data, constraining it only from below. -/
theorem exists_isGalois_totallyRamified_orbitExtension_forall_depth
    (A : Type uA) (K : Type uK) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (p : ℕ) (hp : p.Prime) [CharP K p] (π : A) (hπ : Irreducible π)
    (depth rank : ℕ) (hdepth : 1 ≤ depth) :
    ∃ (K₁ : Type uK) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁) (_ : IsGalois K K₁),
      IsTotallyRamifiedWithRespectTo A K K₁ ∧ Module.finrank K K₁ = p ^ rank ∧
        ∃ (V : AddSubgroup A) (_ : Fintype V) (α : K₁), Fintype.card V = p ^ rank ∧ IsIntegral A α ∧
          (∀ N ≤ depth, ∀ v : V, (v : A) ∈ Ideal.span {π ^ N}) ∧
          ∏ v : V, (α - algebraMap A K₁ v) = algebraMap A K₁ π := by
  obtain ⟨K₁, hK₁field, hK₁alg, hK₁algA, hK₁tower, hK₁fin, hK₁gal, htot, hfinrank,
    V, hVfin, α, hcard, hαint, hV, hprod⟩ :=
    exists_isGalois_totallyRamified_orbitExtension A K p hp π hπ depth rank hdepth
  refine ⟨K₁, hK₁field, hK₁alg, hK₁algA, hK₁tower, hK₁fin, hK₁gal, htot, hfinrank,
    V, hVfin, α, hcard, hαint, fun N hN v => ?_, hprod⟩
  exact Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π hN) (hV v)

end IsDiscreteValuationRing
