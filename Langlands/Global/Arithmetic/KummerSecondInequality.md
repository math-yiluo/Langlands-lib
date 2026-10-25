# The second inequality for Kummer extensions of prime degree

Author: Worker 226.

This module proves the Library statement `IdeleClassKummerPrimeDegreeSecondInequality.{u, u}`
(module `Langlands.Global.AdelicFunctoriality.IdeleClassCyclotomicSecondInequalityStatement`)
from three unproved Library statements, which it takes as hypotheses. Let `L/K` be a Galois
extension of number fields of prime degree `p`, with `K` containing a primitive `p`-th root of
unity. Then the index of the range of the idele-class norm `C_L → C_K` divides `p`. The proof
follows Artin–Tate, *Class Field Theory*, Chapter VI §3, Lemmas 2 and 3. Everything is in
namespace `Langlands.Global.Arithmetic.KummerSecondInequality`.

Notation: `J_K` is the idele group, `P` the principal ideles, `J^S` the Library's
`sUnitIdeles K S` (ideles that are units at the finite places outside `S`; module
`Langlands.Global.Arithmetic.IdeleSUnits`), and `U_S` the `S`-units `sUnits K S`
(module `Langlands.Global.Arithmetic.SUnitIndex`).

## Elementary facts

- `dvd_of_dvd_pow_of_le`: if `p` is prime, `n ∣ p ^ r` and `n ≤ p`, then `n ∣ p`.
- `finite_valuation_ne_one`: an element `x ∈ Kˣ` has `v`-adic valuation `1` at all but finitely
  many finite places `v`. The set of such `v` lies in the union of the Mathlib supports of `x`
  and `x⁻¹` (`HeightOneSpectrum.Support.finite`).
- `isUnit_natCast_of_valuation_eq_one`: if `v.valuation K p = 1`, then `p` is a unit of the
  valuation ring `O_v` of `K_v`.
- `exists_initialPlaces p hp a`: for `p ≠ 0` and `a ∈ Kˣ`, there is a finite set `S` of finite
  places such that:
  - `S` has global uniformizers (the Library's `HasGlobalUniformizers K S`, so that
    `P ⊔ J^S = J_K` by `principal_sup_sUnitIdeles`);
  - `p` is a unit in `O_v` for every `v ∉ S`;
  - `a` is an `S`-unit.

  This is the set `S₁` of Artin–Tate.

## Local power classes

- `PowerClassProd K S p` is the product type
  `(∏_{v ∈ S} K_vˣ / localPowers v p) × (∏_{w ∣ ∞} K_wˣ / infiniteUnitPowers w p)`. Here
  `localPowers v p` (Library module `Langlands.ClassField.Global.LocalPowerIndex`) and
  `infiniteUnitPowers w p` (module `Langlands.ClassField.Global.LocalUnitPowers`) are the
  subgroups of `p`-th powers of `K_vˣ` and `K_wˣ`.
- `PowerClassGroup K S p` is a type synonym of `PowerClassProd K S p`. Its commutative group
  structure is the product structure, declared as a single instance.
- `powerClasses K S p : J_K →* PowerClassGroup K S p` sends an idele to the classes of its
  coordinates at the finite places of `S` and at all infinite places. `powerClasses_fst` and
  `powerClasses_snd` compute its components.
- `powerClasses_eq_one_iff`: `powerClasses K S p x = 1` iff the `v`-coordinate of `x` is a `p`-th
  power in `K_vˣ` for every `v ∈ S`, and the `w`-coordinate is a `p`-th power in `K_wˣ` for every
  infinite `w`.
- `finite_powerClassGroup hζ S`: if `K` contains a primitive `p`-th root of unity `ζ` with `p`
  prime, then `PowerClassGroup K S p` is finite.
  - Finite places: `localPowers_finiteIndex`.
  - Complex places: every unit is a `p`-th power (`infiniteUnitPowers_eq_top_of_isComplex`).
  - Real places: `p = 2` (the Library's `eq_two_of_isReal`, module `KummerRadical`), and
    `infiniteUnitPowers_two_finiteIndex` applies.
- `card_powerClassGroup_le S`: for `p` prime,
  `|PowerClassGroup K S p| ≤ p ^ (2 (|S| + |S_∞|))`. This is the Library bound
  `prod_index_localPowers_le`.

## The index count

`S₁` and `T` are finite sets of finite places, and `S = S₁ ∪ T`.

- `kummerSubgroup K S₁ T p` is the group `D₂` of Artin–Tate: the ideles in `J^S` whose
  coordinates are `p`-th powers at the finite places of `S₁` and at all infinite places,
  i.e. `J^S ⊓ ker (powerClasses K S₁ p)`. No condition is imposed at the places of `T`.
- `sUnitPowerClasses K S₁ T p : U_S →* PowerClassGroup K S₁ p` is `powerClasses K S₁ p`
  applied to principal ideles of `S`-units. `sUnitPowerClassRange K S₁ T p` is its range.
- `principal_sup_kummerSubgroup_subgroupOf`: an idele `x ∈ J^S` lies in `P ⊔ D₂` iff
  `powerClasses K S₁ p x` lies in `sUnitPowerClassRange K S₁ T p`.
  - If `x = a · d` with `a ∈ P` and `d ∈ D₂`, then `a = x d⁻¹ ∈ J^S` is the principal idele of
    an `S`-unit (`unitEmbedding_mem_sUnitIdeles_iff`), and `x` has the power classes of `a`.
  - Conversely, if `x` has the power classes of an `S`-unit `e`, then `e⁻¹ x ∈ D₂`.
- `index_principal_sup_kummerSubgroup hS₁ T p`: if `S₁` has global uniformizers, then the index
  of `P ⊔ D₂` in `J_K` equals the index of `(P ⊔ D₂) ∩ J^S` in `J^S`. This holds because
  `J^S ⊔ (P ⊔ D₂) = J_K` (Mathlib's `Subgroup.relIndex_sup_right`).
- `index_principal_sup_le hζ hS₁ hdisj hcard hpow`: assume
  - `K` contains a primitive `p`-th root of unity `ζ`, with `p` prime;
  - `S₁` has global uniformizers;
  - `S₁` and `T` are disjoint, with `|T| + 1 = |S₁| + |S_∞|`;
  - `hpow`: every `S`-unit whose power classes at `S₁` and at the infinite places are trivial
    is a `p`-th power of an `S`-unit (the kernel of `sUnitPowerClasses` is contained in `U_S^p`).

  Then the index of `P ⊔ D₂` in `J_K` is nonzero and at most `p`. Proof: let `R` be
  `sUnitPowerClassRange`.
  - By the two previous results, the index of `P ⊔ D₂` divides the index of `R` in
    `PowerClassGroup K S₁ p`. Mathlib's `Subgroup.index_comap` and
    `Subgroup.relIndex_dvd_index_of_normal` give this.
  - By `hpow`, `|R| = (U_S : ker)` is at least `(U_S : U_S^p) = p ^ (|S| + |S_∞|)` (the Library's
    `index_pow_sUnits`). Here `|S| = |S₁| + |T| = 2(|S₁| + |S_∞|) - 1 - |S_∞|`.
  - Hence `(index of R) · p ^ (|S| + |S_∞|) ≤ |PowerClassGroup K S₁ p| ≤
    p ^ (2(|S₁| + |S_∞|)) = p · p ^ (|S| + |S_∞|)`, so the index of `R` is at most `p`. It is
    nonzero because `PowerClassGroup K S₁ p` is finite.

## Global `p`-th powers

- `mem_range_pow_of_powerClasses_eq_one hdescent hherbrand hζ hS₁ hpS hdisj hT x hx` is step
  (iii). Its inputs:
  - `hdescent`: the Library statement `IdeleClassGaloisDescent.{u, u}`;
  - `hherbrand`: the Library statement `CyclicIdeleClassHerbrandQuotient.{u, u}`, the first
    inequality in the form `h²(C_E) = [E : F] · h¹(C_E)`;
  - `S₁` has global uniformizers, and `p` is a unit outside `S₁`;
  - `T` is disjoint from `S₁`;
  - `hT`: every family of elements of `K_qˣ` that are units at the places `q ∈ T` agrees at every
    `q ∈ T` with a single `S₁`-unit modulo `p`-th powers of `K_qˣ` (the last conclusion of
    `exists_auxiliaryPrimes`, Library module `AuxiliaryPrimes`);
  - `x` is an `S`-unit whose power classes at `S₁` and at the infinite places are trivial.

  Then `x` is the `p`-th power of an `S`-unit.

  Proof. If `x = c ^ p` with `c ∈ K`, then `c` is an `S`-unit (compare valuations). Otherwise
  let `K' = K(x^{1/p})` be the Library's `radicalExtension K p x`, cyclic of degree `p` over
  `K`. The idele-class norm `C_{K'} → C_K` is surjective:
  - Write an idele as `y = π z` with `π ∈ P` and `z ∈ J^{S₁}` (`principal_sup_sUnitIdeles`).
  - The coordinates of `z` at `T` are units, so `hT` gives an `S₁`-unit `e` such that
    `d = z e⁻¹` has `p`-th power coordinates at every `q ∈ T`.
  - Then `d` is a norm from `K'`. This is the Library's `mem_range_ideleNorm_of_radical`
    (module `KummerNormLift`) for `S`, with `a = x`. Outside `S`, `p`, `x` and `d` are units. At
    `S₁` and at the infinite places, `x` is a local `p`-th power. At `T`, `d` is a local `p`-th
    power.
  - Hence the class of `y` is the class of `d`, which is a norm class.

  So the norm index is `1`. The Library proofs `cyclicH2NormIndexComparison` (applied to
  `hdescent` and the Library proof `ideleClassNormGaloisProduct`) give that `|H²(C_{K'})|`
  divides this index. By `hherbrand`, `|H²(C_{K'})| = p · |H¹(C_{K'})|`. Thus `p ∣ 1`, a
  contradiction.

## The main theorem

`ideleClassKummerPrimeDegreeSecondInequality_of hNS hdescent hherbrand :
IdeleClassKummerPrimeDegreeSecondInequality.{u, u}`, where `hNS` is the Library statement
`CyclicNonsplitPrimeStatement.{u, u}`.

Proof. Let `L/K` be Galois of prime degree `p`, with `ζ ∈ K` a primitive `p`-th root of unity.
1. **Kummer generator.** `Gal(L/K)` is cyclic. By Mathlib's
   `exists_root_adjoin_eq_top_of_isCyclic`, `L = K(β)` with `β ^ p = a ∈ K`.
   `X ^ p - a` is irreducible (`irreducible_X_pow_sub_C_of_root_adjoin_eq_top`), so `a` is not a
   `p`-th power in `K` (`X_pow_sub_C_irreducible_iff_of_prime`). In particular `a ≠ 0`.
2. **The sets `S₁` and `T`.** Choose `S₁` by `exists_initialPlaces p _ a`. Choose `T` by the
   Library's `exists_auxiliaryPrimes hNS hζ S₁`. Then:
   - `T` is disjoint from `S₁`, with `|T| + 1 = |S₁| + |S_∞|`;
   - `a` is a `p`-th power in `K_q` for all `q ∈ T`;
   - `hT` holds.
3. **The count.** By `mem_range_pow_of_powerClasses_eq_one`, `index_principal_sup_le` applies:
   the index of `P ⊔ D₂` is nonzero and at most `p`.
4. **`D₂` consists of norms.** `D₂` lies in the range of the idele norm `J_L → J_K`, again by
   `mem_range_ideleNorm_of_radical` for `S`:
   - at `S₁` and at the infinite places, the coordinates of `y ∈ D₂` are `p`-th powers;
   - at `T`, `a` is a local `p`-th power;
   - outside `S`, `p`, `a` and `y` are units.
5. **Conclusion.**
   - Let `H` be the range of the idele-class norm. Its preimage in `J_K` contains `P ⊔ D₂`.
     So the index of `H`, which equals the index of its preimage
     (`Subgroup.index_comap_of_surjective`), divides the index of `P ⊔ D₂`. Hence it is nonzero
     and at most `p`.
   - By the Library's `ideleClassNorm_range_index_dvd` (the quotient is killed by `p`), the
     index of `H` divides a power of `p`.
   - So it divides `p` (`dvd_of_dvd_pow_of_le`).

## Provenance

Artin–Tate, *Class Field Theory*, Chapter VI §3 (printed pp. 24–27), prove the second inequality
for Kummer extensions of prime degree `n` with groups `D₁, D₂` attached to `S = S₁ ∪ S₂`:
- Lemma 2: `k^× D_i ⊆ k^× N_j J_j` and the index formula
  `(J : k^× D_i) = ∏_{p ∈ S_j} (k_p^× : k_p^{×n}) · [K_i : k] / n^s`;
- Lemma 3: `S₂` can be chosen so that `J_k = k^× D₁` and `K₁ = K`;
- the first inequality gives `K₂ = k`;
- the divisibility comes from Lemma 1 of the chapter.

Here `S₁` holds only the finite places; the infinite places are always treated like A–T's
`S₁`. `D₂` is their `D₂`. Their `S₂` is `T`.

Differences from their proof:
- Only upper bounds for local indices are used (the Library's `LocalPowerIndex`), not their
  exact values. The count gives `(J : K^× D₂) ≤ p` rather than an equality.
- Their conclusion `K₂ = k` is replaced by step (iii), proved one radical at a time. For each
  `x ∈ Δ₂` that is not a `p`-th power, the field `K(x^{1/p})` would have a surjective
  idele-class norm. This contradicts the first inequality in the form of the Library statement
  `CyclicIdeleClassHerbrandQuotient`, combined with `cyclicH2NormIndexComparison`.
- The local norm computations are in the Library module `KummerNormLift`. The auxiliary primes
  come from the Library module `AuxiliaryPrimes`, which uses the cyclic nonsplit-prime statement
  instead of Chapter V, Theorem 4.

The Lean proofs, the groups `PowerClassGroup` and `kummerSubgroup`, and this arrangement of the
argument are internal.
