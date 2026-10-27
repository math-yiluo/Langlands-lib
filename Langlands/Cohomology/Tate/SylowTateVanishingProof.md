# Sylow detection of Tate vanishing

This module proves `Langlands.Tate.sylowTateVanishing : SylowTateVanishing.{u}`,
the proposition of module `CohomologicalTrivialityStatement`: for a finite group
`G`, a representation `C : Rep R G` over any commutative ring and an integer
`n`, if `tateCohomology (Rep.res P.1.subtype C) n` is zero for every prime `p`
and every Sylow `p`-subgroup `P`, then `tateCohomology C n` is zero.

## Proof

The proof follows Serre, *Local Fields*, Chapter IX, §2, Theorem 4 and its
Corollary (printed page 140, PDF page 146), with the primary decomposition
replaced by an additive-order argument.

1. Fix `x : tateCohomology C n`, a prime `p` and a Sylow `p`-subgroup `P`.
   Finiteness instances for `P` and `G ⧸ P` are chosen by `Fintype.ofFinite`;
   the hypothesis is stated for every instance. Since the restricted group is
   zero, the Library's actual Tate restriction gives
   `restriction P.1 C n x = 0`. The Library law
   `corestriction_restriction` (module `TransferProof`, imported through
   `TransferLawsProof`) says
   `corestriction P.1 C n (restriction P.1 C n x) = P.1.index • x`, so
   `P.1.index • x = 0` and `addOrderOf x` divides the index of `P`.
2. Suppose `addOrderOf x ≠ 1` and let `q` be its least prime factor
   (`Nat.minFac_prime`). Sylow `q`-subgroups exist (`Sylow` is nonempty), and by
   step 1 `q` divides the index of such a subgroup `P`. This contradicts
   Mathlib's `Sylow.not_dvd_index`. Hence `addOrderOf x = 1`, i.e. `x = 0`.
3. Every element of `tateCohomology C n` is zero, so the module is a
   subsingleton and therefore a zero object (`ModuleCat.isZero_of_subsingleton`).
