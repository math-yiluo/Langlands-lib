# The fixed subring of a group acting on a local ring

`Langlands.LocalFactor.Ramification.FixedSubring`. For a monoid `M` acting on a ring `R` by ring
automorphisms (`MulSemiringAction M R`), Mathlib's `FixedPoints.subring R M` is the subring of
invariants. This module proves that the invariants of a local ring form a local ring whose
maximal ideal is the contraction of the maximal ideal of `R`, that a group acting faithfully on a
commutative ring is a Galois group of the ring over its invariants (Mathlib's `IsGaloisGroup`),
and that the invariants of a finite group acting on a discrete valuation ring form a discrete
valuation ring. These are the facts about `FixedPoints.subring` that the lower-numbering theory
of this directory uses: every later file studies an action on a local ring `R` together with the
induced action of a quotient `G ⧸ H` on `FixedPoints.subring R H`.

## Statements

All declarations are in the name space `Langlands.Ramification`.

- An invariant element is a unit of the invariants exactly when it is a unit of `R`:

  ```lean
  theorem isUnit_fixedSubring_iff {R : Type*} [Ring R] {M : Type*} [Monoid M]
      [MulSemiringAction M R] (a : FixedPoints.subring R M) :
      IsUnit a ↔ IsUnit (a : R)
  ```

  Consequently the inclusion is a local homomorphism (instance `isLocalHom_fixedSubring_subtype`)
  and, if `R` is local, so are the invariants (instance `isLocalRing_fixedSubring`).
- The maximal ideal of the invariants of a local commutative ring is the contraction of that of
  `R`:

  ```lean
  theorem maximalIdeal_fixedSubring_eq_comap {R : Type*} [CommRing R] [IsLocalRing R]
      {M : Type*} [Monoid M] [MulSemiringAction M R] :
      IsLocalRing.maximalIdeal (FixedPoints.subring R M) =
        Ideal.comap (FixedPoints.subring R M).subtype (IsLocalRing.maximalIdeal R)
  ```

  with the membership form `mem_maximalIdeal_fixedSubring_iff` and the maximality of the
  contraction, `isMaximal_comap_maximalIdeal_fixedSubring`.
- A group acting faithfully on a commutative ring `S` is a Galois group of `S` over its
  invariants:

  ```lean
  theorem isGaloisGroup_fixedSubring {S : Type*} [CommRing S] {G : Type*} [Group G]
      [MulSemiringAction G S] [FaithfulSMul G S] :
      IsGaloisGroup G (FixedPoints.subring S G) S
  ```
- The invariants of a finite group acting on a discrete valuation ring form a discrete valuation
  ring:

  ```lean
  theorem isDiscreteValuationRing_fixedSubring {R : Type*} [CommRing R] [IsDomain R]
      [IsDiscreteValuationRing R] {H : Type*} [Group H] [Finite H] [MulSemiringAction H R] :
      IsDiscreteValuationRing (FixedPoints.subring R H)
  ```

  The group need not act faithfully.
- For a trivial monoid (`Subsingleton M`) the invariants are everything:
  `fixedSubring_eq_top_of_subsingleton` and the ring isomorphism
  `fixedSubringEquivOfSubsingleton : FixedPoints.subring R M ≃+* R`.

## Proofs

If `a` is invariant and `a * b = 1 = b * a` in `R`, then `a * (m • b) = m • (a * b) = 1`, so
`m • b` is also a right inverse of `a` and equals `b`; hence the inverse of an invariant unit is
invariant (`mem_fixedSubring_of_mul_eq_one`), which gives `isUnit_fixedSubring_iff`. Locality of
the invariants follows: if `a + b = 1` among invariants, one of `a`, `b` is a unit of `R`, hence of
the invariants. Non-units of the invariants are then exactly the invariants that are non-units of
`R`, which is the statement on maximal ideals. The Galois-group statement is the three fields of
`IsGaloisGroup`: faithfulness is assumed, the action commutes with multiplication by invariants,
and the invariants are by definition the image of `FixedPoints.subring S G`.

For the discrete valuation ring, write `v = IsDiscreteValuationRing.addVal R`. The norm
`∏ h, h • π` of a uniformizer `π` is invariant, non-zero and of positive valuation, so there is a
least positive value `m` of `v` on invariants; let `t` be an invariant with `v t = m`. Every
invariant non-unit has valuation at least `m`. For an invariant `s ≠ 0` with `v s = q m + r`,
`t ^ q` divides `s` in `R`, the cofactor `c` is invariant (cancel `t ^ q` in `h • (t ^ q c) = t ^ q c`),
and `c` is a unit, since otherwise `v c ≥ m` would contradict `r < m`. So `s = t ^ q · c` with `c`
an invariant unit; `t` is irreducible among the invariants because a factorisation into two
non-units would give `2m ≤ m`. Mathlib's `ofHasUnitMulPowIrreducibleFactorization` concludes.

## Declarations

In the order of the file.

- `mem_fixedSubring_iff`: membership in the invariants.
- `smul_eq_self_of_mem_fixedSubring_of_mul_eq_one`, `mem_fixedSubring_of_mul_eq_one`: the inverse
  of an invariant unit is invariant.
- `isUnit_fixedSubring_iff`; instances `isLocalHom_fixedSubring_subtype`, `isLocalRing_fixedSubring`;
  `isLocalRing_fixedSubring_of_finite` (the same for a finite group, as a theorem).
- `mem_maximalIdeal_fixedSubring_iff`, `maximalIdeal_fixedSubring_eq_comap`,
  `isMaximal_comap_maximalIdeal_fixedSubring`.
- `fixedSubring_eq_top_of_forall_smul_eq`, `fixedSubring_eq_top_of_subsingleton`,
  `fixedSubringEquivOfSubsingleton`.
- `isGaloisGroup_fixedSubring`.
- Lemmas of the proof for discrete valuation rings, in `Langlands.Ramification.FixedSubring`:
  `prod_smul_mem_fixedSubring` (the norm is invariant), `exists_mem_fixedSubring_addVal_pos`,
  `mem_fixedSubring_of_mul_mem` (cancellation of a non-zero invariant factor),
  `exists_addVal_eq_natCast`.
- `isDiscreteValuationRing_fixedSubring`.

## Source and licence

Adapted from four files of the Anthropic Lean formalisation of Fermat's Last Theorem (commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`; registered literature
`anthropic-flt-complete-lean-source-6e837e75`):

| FLT file | SHA-256 |
| --- | --- |
| `Definitions/Def_Mathlib_RingTheory_Invariant_FixedSubringLocal.lean` | `96cafbd97505550f1037d243c833709d3f54836bcd6317ce4732b7d371338a8d` |
| `Definitions/Def_Mathlib_RingTheory_Invariant_FixedSubringGaloisGroup.lean` | `245169faf7fac39485e67df511eadca7f35bd9b478fa542e5eef3f6cb51d9777` |
| `Theorems/Thm_FixedPoints_isDiscreteValuationRing_subring.lean` | `db799038bdd3b8d22026ddbc00e5cb365b521828a58b322c675a3773e4d8abaf` |
| `P2M/Sol/S_FixedPoints_isDiscreteValuationRing_subring.lean` | `5e7267644ede2f6357847ea7217b7e8646a9275267e3a9a19217beff9c167c00` |

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`,
`NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. The FLT `ATTRIBUTION.md` does not
list these files as containing third-party material. The Lean file begins with an attribution
header stating that it was modified.

Changes against the FLT files:

- The four files are one module. Names follow the Library: upstream's `FixedPoints.X_subring_Y`
  is `Langlands.Ramification.X_fixedSubring_Y` (for example `FixedPoints.maximalIdeal_subring_eq_comap`
  is `maximalIdeal_fixedSubring_eq_comap`, `FixedPoints.isDiscreteValuationRing_subring` is
  `isDiscreteValuationRing_fixedSubring`); the table `RAM-NAMES.tsv` of the port lists every name.
- The FLT proof module proved the theorem on discrete valuation rings by a lemma of the same
  statement in its proof name space and stated the theorem in a separate file; here the theorem
  is stated once and carries that proof. The four lemmas of the proof are in
  `Langlands.Ramification.FixedSubring`.
- One deprecated Mathlib name is replaced (`ENat.top_ne_coe` by `ENat.top_ne_natCast`).
- The example blocks and `#print axioms` checks of the FLT definition files are not kept; no
  options are set (the FLT package sets heartbeat limits and a `backward.*` option for every
  file; the module compiles with Lean's defaults).
- Statements are unchanged up to these names.

## Literature

Serre, *Local Fields*, GTM 67 (1979), Chapter II, §2, Proposition 3, printed page 28 (the integral
closure `A_L` of the valuation ring `A_K` of a complete discretely valued field `K` in a finite
extension `L` is a discrete valuation ring), and Chapter IV, Notation and Hypotheses and §1,
printed page 61, where the ramification groups of a Galois extension are studied through the
action of the Galois group on `A_L`. Serre goes from `A_K` up to `A_L`; here the facts are proved
for the invariants of an arbitrary action on a local ring.
