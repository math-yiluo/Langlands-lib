# The cyclotomic reduction of the prime-degree second inequality

Authors: Worker 269, with Worker 123 (the two tower index lemmas are adapted from Worker 123's
unreviewed draft for task 29981152).

This module is in namespace `Langlands.Global.AdelicFunctoriality`. It proves the implication
`IdeleClassCyclotomicSecondInequalityReduction.{u,v}` of
[IdeleClassCyclotomicSecondInequalityStatement](IdeleClassCyclotomicSecondInequalityStatement.md).
The implication has three antecedents:

- the finite norm-index / degree-power bound `IdeleClassNormIndexFinite.{u,v}`;
- the norm tower law `IdeleClassNormTower.{u,v,v}`;
- the Kummer case `IdeleClassKummerPrimeDegreeSecondInequality.{v,v}`.

Its conclusion is the prime-degree second inequality `IdeleClassPrimeDegreeSecondInequality.{u,v}`
for the actual idele-class norm `ideleClassNorm`. The theorem proves only the implication. It
does not prove any of the three antecedents. The module changes none of the imported
definitions.

## Definition

`cyclotomicRootField K L p` is defined for fields `K : Type u` and `L : Type v` with
`[Algebra K L] [CharZero L]`, and for `p : ℕ` with `[NeZero p]`. It is an intermediate field
of `CyclotomicField p L / K`, namely
`IntermediateField.adjoin K {ζ}` with `ζ = IsCyclotomicExtension.zeta p L (CyclotomicField p L)`.
Here `ζ` is Mathlib's chosen primitive `p`-th root of unity in `L(ζ) = CyclotomicField p L`.
So `cyclotomicRootField K L p` is the field `K(ζ)` inside `L(ζ)`. The structure `Algebra K
(CyclotomicField p L)` and the tower `IsScalarTower K L (CyclotomicField p L)` are Mathlib's
derived instances on `CyclotomicField`. Both fields have carriers in `Type v`.

## Statements

Write `M = CyclotomicField p L`, `E = cyclotomicRootField K L p`, and
`L' = (IsScalarTower.toAlgHom K L M).fieldRange` for the image of `L` in `M`.

- `ideleClassNorm_range_index_dvd_mul_of_tower K L M htower` (number fields `K : Type u`,
  `L : Type v`, `M : Type w`, with algebras `K → L`, `L → M` and `K → M`). Let `htower` be the
  tower identity `N_{M/K} = N_{L/K} ∘ N_{M/L}` on `IdeleClassGroup (𝓞 M) M`. Then the range
  index of `N_{M/K}` divides the range index of `N_{L/K}` times the range index of `N_{M/L}`.
- `ideleClassNorm_range_index_dvd_of_tower K L M htower`: under the same hypotheses, the range
  index of `N_{L/K}` divides the range index of `N_{M/K}`.
- `zeta_mem_cyclotomicRootField`: `ζ ∈ E`.
- `isIntegral_cyclotomicField_zeta`: `ζ` is integral over `K`.
- The instance `finiteDimensional_cyclotomicRootField`: `FiniteDimensional K E`.
- `finrank_cyclotomicRootField_le_totient`: `finrank K E ≤ φ(p)`.
- `exists_isPrimitiveRoot_cyclotomicRootField`: some `ζ' : E` is a primitive `p`-th root of
  unity.
- `cyclotomicRootField_sup_fieldRange_eq_top`: `E ⊔ L' = ⊤` as intermediate fields of `M/K`.
- `finrank_cyclotomicField_cyclotomicRootField hcop`: assume
  `hcop : (finrank K E).Coprime (finrank K L)`. Then `finrank E M = finrank K L`.
- `isGalois_cyclotomicField_cyclotomicRootField`: assume `[FiniteDimensional K L]
  [IsGalois K L]`. Then `IsGalois E M`.
- `ideleClassCyclotomicSecondInequalityReduction_holds :
  IdeleClassCyclotomicSecondInequalityReduction.{u, v}`. The universes are the published ones:
  `K : Type u` and `L : Type v` are independent, and `p = 2` is not excluded.

## Proofs

Tower index lemmas: the tower identity makes the monoid homomorphism `N_{M/K}` equal to
`N_{L/K} ∘ N_{M/L}`. So its range is the image of `range N_{M/L}` under `N_{L/K}`
(`MonoidHom.range_comp`). This image lies in `range N_{L/K}`, which gives the second lemma by
`Subgroup.index_dvd_of_le`. For the first lemma, `Subgroup.index_map` writes the index of the
image as `(range N_{M/L} ⊔ ker N_{L/K}).index * (range N_{L/K}).index`. The first factor
divides `(range N_{M/L}).index` because `range N_{M/L}` is contained in the join
(`Subgroup.index_dvd_of_le le_sup_left`). Both lemmas
use Mathlib's index convention, where an infinite index is `0`, and need no finiteness
hypothesis. They are adapted from `index_range_comp_dvd` and `index_range_dvd_comp` in Worker
123's draft.

Integrality and degree of `K(ζ)`: Mathlib maps `Φ_p` over `K` to `Φ_p` over `M`
(`map_cyclotomic`). The primitive root `ζ` is a root of `Φ_p` (`IsPrimitiveRoot.isRoot_cyclotomic`).
Since `Φ_p` is monic, `ζ` is integral over `K`, and `E = K⟮ζ⟯` is finite-dimensional
(`IntermediateField.adjoin.finiteDimensional`). Also `finrank K E` is the degree of the minimal
polynomial of `ζ` (`IntermediateField.adjoin.finrank`). That polynomial divides `Φ_p`
(`minpoly.dvd`), so its degree is at most `deg Φ_p = φ(p)` (`natDegree_le_of_dvd`,
`natDegree_cyclotomic`).

Primitive root in `E`: the element `⟨ζ, zeta_mem_cyclotomicRootField⟩` of `E` is primitive,
because primitivity can be checked after coercion into `M`
(`IsPrimitiveRoot.coe_submonoidClass_iff`).

`E ⊔ L' = ⊤`: the subring `E ⊔ L'` contains the image of `L`. So it is an `L`-subalgebra `S`
of `M`, and `S` contains `ζ`. Mathlib's `IsCyclotomicExtension.adjoin_primitive_root_eq_top`
says that `Algebra.adjoin L {ζ} = ⊤`. Then `Algebra.adjoin_le` gives `⊤ ≤ S`.

Degree of `M/E`: the field isomorphism `AlgEquiv.ofInjectiveField : L ≃ₐ[K] L'` shows
`finrank K L = finrank K L'`. When `finrank K E` and `finrank K L'` are coprime, `E` and `L'` are
linearly disjoint over `K` (`IntermediateField.LinearDisjoint.of_finrank_coprime`). Together
with `E ⊔ L' = ⊤`, `LinearDisjoint.finrank_left_eq_finrank` gives
`finrank E M = finrank K L'`.

Galois property: `L'` is Galois and finite over `K` by transport along the same isomorphism
(`IsGalois.of_algEquiv`, `Module.Finite.equiv`). Since `L' ⊔ E = ⊤`, Mathlib's
`IsGalois.sup_right` shows that `M/E` is Galois.

Main theorem: let `L/K` be Galois with `p = finrank K L` prime. Put `M = CyclotomicField p L`
and `E = cyclotomicRootField K L p`. Then `0 < finrank K E` (`Module.finrank_pos`) and
`finrank K E ≤ φ(p) < p` (`Nat.totient_lt`). So `p` is coprime to `finrank K E`
(`Nat.coprime_of_lt_prime`). By the lemmas above, `finrank E M = p`, `M/E` is Galois, and `E`
contains a primitive `p`-th root of unity. Both `E` and `M` have carriers in `Type v`, so the
Kummer antecedent `{v,v}` applies to `M/E`: the norm index of `M/E` divides `p`. The norm
index bound `{u,v}` gives an `r` with `(index N_{L/K}) ∣ p ^ r`, and an `s` with
`(index N_{E/K}) ∣ (finrank K E) ^ s`. The tower law `{u,v,v}` is used twice. With
`K ⊂ L ⊂ M` it gives `index N_{L/K} ∣ index N_{M/K}`. With `K ⊂ E ⊂ M` it gives
`index N_{M/K} ∣ index N_{E/K} * index N_{M/E}`. Hence
`index N_{L/K} ∣ (finrank K E) ^ s * p`. Since `index N_{L/K}` divides `p ^ r`, it is coprime
to `(finrank K E) ^ s`, so it divides `p` (`Nat.Coprime.dvd_of_dvd_mul_left`).

## Provenance

Derived. Artin and Tate, *Class Field Theory* (2009), Chapter VI §1, Reduction 2 and its proof,
printed pp.20–21 (PDF pp.29–30). The proof there runs as follows. The norm index of `K/k`
divides that of `K(ζ)/k`. That index divides the product of the indices of `k(ζ)/k` and of
`K(ζ)/k(ζ)`. The index of `k(ζ)/k` is prime to `ℓ`. The index of `K/k` is a power of `ℓ`, so it
divides the index of `K(ζ)/k(ζ)`. The two tower lemmas are the second lemma of VI §1 (printed
p.20, PDF p.29), parts 1 and 2. The power-of-the-degree bound is the first lemma there,
supplied here by the `IdeleClassNormIndexFinite` antecedent.

Artin and Tate state that `K(ζ)/k(ζ)` is cyclic of degree `ℓ` without proof. The Lean proof
supplies this step by the degree bound `[k(ζ) : k] ≤ φ(ℓ) < ℓ` and linear disjointness. It
uses Galois of prime degree in place of cyclic, as in the published Kummer antecedent. The book
assumes `ℓ` differs from the characteristic; this is automatic for number fields. The
statement module also cites an alternative route through Milne's *Class Field Theory*; this
proof does not use it.

The definition `cyclotomicRootField` and the auxiliary lemmas are internal packaging. The
module and theorem names follow the plan agreed with Worker 226 and Worker 145 for the
published target, whose proof task is e28072cb.
