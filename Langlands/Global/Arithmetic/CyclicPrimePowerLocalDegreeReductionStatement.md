# A degree-prime intermediate-field test for full local degree

`Langlands.Global.CyclicPrimePowerLocalDegreeReductionStatement.{u,v}` is a
derived proposition definition. For number fields `F : Type u` and `E : Type v`,
an `F`-algebra structure on `E`, a Galois extension `E/F` with cyclic automorphism
group, a prime `ℓ`, and a positive integer `r` such that `[E : F] = ℓ^r`, it asserts
the existence of an actual intermediate field `K : IntermediateField F E` with:

- `K/F` Galois and `K ≃ₐ[F] K` cyclic;
- `[K : F] = ℓ`;
- for every finite prime `v` of `F` and every finite prime `q` of `K` above `v`,
  if `[K_q : F_v] ≠ 1`, there is a finite prime `w` of `E` above both `q` and `v`
  such that `[E_w : F_v] = [E : F]`.

Here each finite prime is an element of `HeightOneSpectrum` of the appropriate
ring of integers. Each relation of primes is the actual `Ideal.LiesOver`
relation. The witness `_hwq` records that `w` lies above the specified `q`;
it is retained in the conclusion even though the displayed degree only needs
the witness `hwv` that `w` lies above `v`.

All local fields are the actual `adicCompletion` fields, and all displayed
degrees are `Module.finrank`. The inherited intermediate-field algebras give
the tower `F → K → E`. Mathlib's `NumberField.of_intermediateField` supplies
`NumberField K` from the given number fields; it is not an additional premise.
The scoped instances in `AdelicFunctoriality.FiniteExtension` give the
completion algebra structures. The proposition installs `hq` before forming
`[K_q : F_v]` and `hwv` before forming `[E_w : F_v]`. The universes of `F` and
`E` remain independent.

## Source and derivation

The source is Emil Artin and John Tate, *Class Field Theory*, AMS Chelsea, 2009,
Chapter V §4, Theorem 3 and its proof, printed page 17 (PDF page 26), with
the section opening on printed page 16 (PDF page 25). The registered source is
`artin-tate-2009-class-field-theory`, SHA-256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
The source's base field `k`, upper field `K`, and intermediate field `F`
correspond respectively to this declaration's `F`, `E`, and `K`.

The source proves infinitude of primes with full local degree by using the
unique degree-prime intermediate field and Theorem 2 on primes that do not
split completely. The present proposition isolates the pointwise arithmetic
step in that argument, specialized to number fields. It is derived from the
proof, rather than a restatement of the infinitude conclusion.

In group terms, let `G = Gal(E/F)` and let `H` be its unique subgroup of index
`ℓ`. Its fixed field is the degree-`ℓ` field `K`; the quotient `G/H` shows that
`K/F` is Galois and cyclic. Choose a prime `w` of `E` above the specified `q`
and let `D` be its decomposition subgroup in `G`. If `D` were proper, cyclic
prime-power group theory would give `D ≤ H`. Restriction to `K` then makes the
decomposition subgroup at `q` trivial, so `[K_q : F_v] = 1`. The assumed
inequality rules this out. Consequently `D = G` and
`[E_w : F_v] = |D| = |G| = [E : F]`.

This explains the source's argument through the intermediate field inside
the local base field using decomposition groups. The published
`AdelicFunctoriality.exists_place_above` supplies place extension, and
`AdelicFunctoriality.localDegree_eq` identifies completed degree with `e f`.
The later proof must still establish and assemble the cyclic subgroup,
fixed-field, and decomposition-group restriction comparisons needed for this
test; this module proves none of them.

## Scope

Only a proposition is defined here. Neither this reduction nor any local/global
comparison is assumed as an extra hypothesis. The declaration asserts
existence of a suitable intermediate field, without adding a uniqueness clause.
It does not assert existence or infinitude of primes satisfying the local
premise, and it does not prove
`Langlands.Global.CyclicPrimePowerLocalDegreeStatement`.
The local degrees include ramification: no unramifiedness or equality of
residue degree with global degree is asserted.
