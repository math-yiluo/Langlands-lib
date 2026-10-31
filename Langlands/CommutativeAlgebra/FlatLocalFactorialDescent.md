# Factoriality descends along flat local homomorphisms

This helper module proves that unique factorization descends along a flat
local homomorphism of local rings. It works for arbitrary commutative rings
`R` and `S` with an algebra structure `[Algebra R S]`.

```lean
theorem Langlands.CommutativeAlgebra.dvd_of_algebraMap_dvd_of_faithfullyFlat
    [Module.FaithfullyFlat R S] {a b : R}
    (h : algebraMap R S a ∣ algebraMap R S b) : a ∣ b

theorem Langlands.CommutativeAlgebra.exists_common_multiples_of_flat
    [Module.Flat R S] {a b : R} {s t : S}
    (h : algebraMap R S a * s = algebraMap R S b * t) :
    ∃ (k : ℕ) (z : Fin k → R) (y : Fin k → S), (∀ j, a ∣ z j ∧ b ∣ z j) ∧
      algebraMap R S a * s = ∑ j, algebraMap R S (z j) * y j

theorem Langlands.CommutativeAlgebra.uniqueFactorizationMonoid_of_flat_of_isLocalHom
    [IsLocalRing R] [IsLocalRing S] [Module.Flat R S]
    [IsLocalHom (algebraMap R S)] [UniqueFactorizationMonoid S] :
    UniqueFactorizationMonoid R
```

## Divisibility reflects along faithfully flat maps

`dvd_of_algebraMap_dvd_of_faithfullyFlat` applies Mathlib's
`Ideal.comap_map_eq_self_of_faithfullyFlat` to the principal ideal `(a)`.
The extended ideal is `(a) S`, so `b` lies in `(a)` exactly when its image
lies in `(a) S`, that is, when the image of `a` divides the image of `b`.

## Common multiples over a flat algebra

`exists_common_multiples_of_flat` applies the equational criterion of
flatness, `Module.Flat.isTrivialRelation_of_sum_smul_eq_zero`, to the
relation `a • s + (-b) • t = 0` in `S`. The criterion gives a matrix `c`
over `R` and elements `y j` of `S` with `s = ∑ c 0 j • y j`,
`t = ∑ c 1 j • y j` and `a * c 0 j - b * c 1 j = 0` for every `j`. The
elements `z j = a * c 0 j` are common multiples of `a` and `b`, and
`a * s = ∑ z j • y j`.

## Descent of factoriality

For `uniqueFactorizationMonoid_of_flat_of_isLocalHom`, Mathlib's
`Module.FaithfullyFlat.of_flat_of_isLocalHom` makes `S` faithfully flat
over `R`. Hence `algebraMap R S` is injective (`FaithfulSMul.algebraMap_injective`),
and `R` is a domain because `S` is one.

Well-founded divisibility pulls back along the injective map: a strict
divisibility `a ∣ b` with a nonunit cofactor in `R` stays strict in `S`,
because an element that becomes a unit in `S` is already a unit in `R`
(the map is a local homomorphism). Thus the strict-divisibility relation on
`R` is a subrelation of the inverse image of the well-founded relation on
`S`.

Then `R` is shown to be a GCD monoid with `isGCDMonoid_iff_exists_lcm`, by
building a least common multiple for each pair `a, b`. If `a` or `b` is
zero, the least common multiple is `0`. Otherwise let `L` be a least common
multiple in `S` of the images of `a` and `b`. Then `L ≠ 0`, and
`L = a s = b t` for some `s, t` in `S`. The previous lemma writes
`a s = ∑ z j y j`, where every `z j` is a common multiple of `a` and `b` in `R`.
So `L` divides the image of each `z j`, say with cofactors `c j`.
Cancelling `L` gives `∑ c j y j = 1`. Since `S` is local, some `c j` is a
unit, so the image of `z j` is associated to `L`. Every common multiple `d`
of `a` and `b` in `R` has image divisible by `L`, hence by the image of
`z j`. Divisibility reflects along the faithfully flat map, so `z j ∣ d`,
and `z j` is a least common multiple in `R`.

A GCD monoid with well-founded divisibility is a unique factorization
monoid (`ufm_of_decomposition_of_wfDvdMonoid`).

## Provenance and contributions

This is an internal helper for the proof of
`Langlands.AlgebraicGeometry.SmoothAlgClosedFactorialStalks`, where it is
applied to the completion map of a Noetherian local ring. Descent of
factoriality along faithfully flat maps is classical. The argument here is
written directly from the equational criterion of flatness, the
local-ring unit trick and the least-common-multiple characterization of
GCD monoids. It does not follow a particular published proof. Worker 254
wrote the Lean proof and this description.
