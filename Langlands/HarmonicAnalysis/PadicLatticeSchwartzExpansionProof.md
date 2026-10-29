# Single-lattice coset expansions of p-adic Schwartz–Bruhat functions: proof

Author: Worker 739 (sole author).

The closing theorem
`Langlands.HarmonicAnalysis.padicLatticeSchwartzExpansion.{u}` proves exactly
the published
`Langlands.HarmonicAnalysis.PadicLatticeSchwartzExpansionStatement F T` from
[PadicLatticeSchwartzExpansionStatement](PadicLatticeSchwartzExpansionStatement.md).
Its complete telescope is

```lean
{p : ℕ} [Fact p.Prime] (F : Langlands.PadicField.{u} p)
  (T : F.TopologicalData)
```

The universe `u` is arbitrary and the theorem covers every supplied `T`. It
adds no hypotheses. The statement pair and its imports are unchanged.

The module imports the statement module and
`Langlands.HarmonicAnalysis.PadicLatticeGeometryProof`. From the latter it uses
only the openness half of `padicLatticeGeometry F T`: every
`T.additiveLattice n` is open in the supplied topology `T.topology`.

## Auxiliary theorem: one lattice of invariance

```lean
theorem padicSchwartzBruhat_exists_additiveLattice_invariant
    (F : PadicField.{u} p) (T : F.TopologicalData)
    (f : @SchwartzBruhat F.Carrier T.topology) :
    ∃ m : ℤ, ∀ x h : F.Carrier, h ∈ T.additiveLattice m → f (x + h) = f x
```

Every Schwartz–Bruhat function in the supplied topology is invariant under all
translations by one valuation lattice `T.additiveLattice m`, on the whole of
`F.Carrier` and not only near its support. The proof installs `T.topology`,
`T.valuativeRel` and `T.localField`, just as the target does.

1. **Pointwise lattices.** Fix `x`. The set `{d | f (x + d) = f x}` is the
   preimage of the fiber of `f` through `f x` under the continuous map
   `d ↦ x + d`. The fiber is open by `IsLocallyConstant.isOpen_fiber`, applied to
   the local constancy bundled in `f`. The set contains `0`, so it is a
   neighborhood of `0`. The published `T.exists_additiveLattice_subset` then
   gives a level `n x` with `T.additiveLattice (n x)` inside this set:
   `f (x + d) = f x` for every `d` in that lattice. `choose` turns this into a
   function `n : F.Carrier → ℤ`.
2. **Common level.** The support `tsupport f` is compact by the compact support
   bundled in `f`. For each `x`, the coset `{z | z - x ∈ T.additiveLattice (n x)}`
   is open, being the preimage of an open lattice under `z ↦ z - x`, and it
   contains `x`. `IsCompact.elim_nhds_subcover` gives a finite set `t` of points
   whose cosets cover `tsupport f`. `Finset.exists_le`, applied to the image of
   `t` under `x ↦ -n x`, gives an upper bound `M`. The level is `-M`, which
   satisfies `-M ≤ n x` for every `x ∈ t`.
3. **Invariance on the support.** Let `y ∈ tsupport f` and
   `h ∈ T.additiveLattice (-M)`. Choose `x ∈ t` with
   `y - x ∈ T.additiveLattice (n x)`. Monotonicity (`additiveLattice_mono`) puts
   `h` in `T.additiveLattice (n x)`, so `(y - x) + h` lies there too. Step 1 at
   `x` gives `f y = f x` and `f (y + h) = f x`.
4. **Invariance off the support.** Suppose `y ∉ tsupport f`. If
   `y + h ∈ tsupport f`, step 3 applied at `y + h` with `-h`, which lies in the
   lattice, gives `f y = f (y + h)`. Otherwise both points are outside the
   support, and `image_eq_zero_of_notMem_tsupport` makes both values `0`.

## Closing theorem: the coset expansion

Fix `f`. The proof works in the `classical` setting and takes the level `m` from
the auxiliary theorem. Write `L = T.additiveLattice m`, which is open by
`padicLatticeGeometry`.

1. **Finite coset cover.** A second application of
   `IsCompact.elim_nhds_subcover` covers `tsupport f` with finitely many cosets
   `{z | z - x ∈ L}`, for `x` in a finite set `t`.
2. **Distinct classes.** `S` is the image of `t` in the quotient group
   `F.Carrier ⧸ L` under `QuotientAddGroup.mk`. It is a finite set of distinct
   cosets. `S.equivFin` enumerates it as `Fin S.card`.
3. **Witnesses.** The proof supplies the level `m`, `N = S.card`, the
   representatives `a i = (S.equivFin.symm i).1.out`, chosen by `Quotient.out`,
   and the sampled coefficients `c i = f (a i)`.
4. **Pointwise identity.** Fix `x`. By `QuotientAddGroup.eq_iff_sub_mem` and
   `QuotientAddGroup.out_eq'`, `x - q.out ∈ L` holds exactly when the class of
   `x` is `q`. So the summand for the class `q` equals `f q.out` when the class
   of `x` is `q`, and `0` otherwise. `Fintype.sum_equiv` and
   `Finset.sum_coe_sort` rewrite the sum over `Fin N` as a sum over `S`.
   `Finset.sum_ite_eq` then reduces it to `f (class of x).out` if the class of
   `x` lies in `S`, and to `0` otherwise.
   - If the class lies in `S`, invariance under
     `x - (class of x).out ∈ L` gives `f (class of x).out = f x`.
   - If it does not, `x ∉ tsupport f`: otherwise step 1 would place `x` in a
     coset of some `y ∈ t`, so its class would be the class of `y`, which lies
     in `S`. Hence `f x = 0`.

The constructed cosets are pairwise distinct and the coefficients are values of
`f`, but the exported theorem asserts only the target statement's identity.
The proof uses no Haar measure, additive character, integral, Fourier transform
or `exists_compactCosetExpansion`.

## Provenance and original source

The target is a derived internal statement, explained in
[its provenance](PadicLatticeSchwartzExpansionStatement.md). Proof review does
not require the implemented route to follow the literature. The comparison
below records where it differs.

- André Weil, *Basic Number Theory*, second edition (1973), registered
  `weil-1973-basic-number-theory`, SHA-256
  `32fff78f8ccc5d6378907941e26746c34e20fc3adf5096508844cfe8a301e33b`:
  Chapter VII §2, Proposition 2 and its proof, printed p.107 (PDF p.124).
  Worker 739 re-read this page on 2026-10-28.

Weil's proof bounds the support by a norm, giving a lattice `L` that contains
it. Open fibers and compactness of `L` show that the function takes finitely
many values on `L`. Uniform continuity on `L` then gives a smaller lattice `M`
such that the function is constant on cosets modulo `M` in `L`. Finally `L` is
the union of finitely many cosets `e_i + M`, so the function equals
`∑ i, Φ(e_i) · 1_{e_i + M}`.

The Lean proof keeps the sampled coefficients but obtains the lattices
differently. It gets the invariance lattice from a finite subcover of pointwise
lattices, with no uniform continuity and no finiteness of the value set. It
proves invariance on all of `F.Carrier`, not only inside a support lattice. It
uses no outer lattice `L`: the cosets come from the image in `F.Carrier ⧸ L`
(here `L` is the invariance lattice) of a finite coset cover of the support. In
the Lean convention, Weil's `M = P^n` is `T.additiveLattice (-n)`.

The project literature index lists no errata for Weil's book (checked on
2026-10-28).

## Verification

The pinned environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0,
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`). The module compiles
without errors or warnings. To check the complete unapplied telescope,
`@Langlands.HarmonicAnalysis.padicLatticeSchwartzExpansion` is assigned to the
dependent function type with implicit prime, primality instance, explicit `F`
and explicit `T`. Declaration inspection checks its assumptions. Formal
exact-target validation and independent semantic review are separate
publication checks.
