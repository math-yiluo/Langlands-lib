# Unitary chains up a prime cyclic tower from a weak induction

Worker 5130 wrote this module for Task 7784. It builds the chains that B6
(`TowerBaseChangeHeckeComponentStatement`) takes as input. The chain starts at a cuspidal
realization that is a weak automorphic induction of a Hecke character and goes up a prime
cyclic tower. Its terminal datum has the Hecke family of the conjugate characters. One
universe `u` holds all fields.

## Auxiliary lemmas

- `isUnitary_arithmeticComap_ofCuspidal`: for `e : F ≃+* F'` and a cuspidal realization `S`
  over `F'` with unitary central character (`HasUnitaryCentralCharacter`), the pullback
  along `e` of the one-constituent data of `S` is unitary. The pulled-back realization has
  the unitary central character `χ ∘ e` (`arithmeticComap_hasCentralCharacter_iff`), hence
  is unitarizable (`isUnitarizable_of_hasUnitaryCentralCharacter`).
- `IsobaricData.hasHeckeFamily_of_eventually`: isobaric data `D` of rank `r` with an attached
  system `s` have the Hecke family `μ : Fin r → HeckeCharacter K` (`HasHeckeFamily`) as soon
  as, at almost every finite place `v`, all `μ i` are unramified and, where `s` is defined,
  the eigenvalue multiset of `s` at `v` is the multiset of the values `(μ i)_v(π)` at every
  uniformizer `π`. The finite exceptional set is `s.exceptional` together with the finite
  set where the condition fails. On its complement, the Euler polynomial of `s` is the
  product of the factors `1 - (μ i)_v(π) X`.
- `underPowerProfile_of_notMem`: the value of `underPowerProfile s w` (module
  `TowerSpectralInvariant`) where `s` is defined at `w ∩ K`.

## Towers

Let `T` be a `PrimeCyclicBaseChangeTower F K`, with levels `T.level i`, intermediate fields
of `K/F`, and compact adele quotients at every level.

- `algebraMap_bottomEquiv`, `algebraMap_topEquiv_symm`: the identifications
  `T.bottomEquiv : T.level 0 ≃ F` and `T.topEquiv : T.level (last) ≃ K` are compatible with
  the embeddings into `K`.
- `exists_isobaricChain_of_step`: let `hBC` say that every unitary datum at level `i` has a
  unitary weak base change at level `i + 1`. Then every unitary datum `D0` at level `0` is
  the bottom of a chain `D : T.IsobaricChain` with `D 0 = D0` that is unitary and a
  successive weak base change. The chain is defined by `Fin.induction` from a choice
  function for the steps.
- `IsobaricChain.towerSpectralInvariant`: along a successive weak base change, the invariant
  `TowerSpectralInvariant` (with respect to the top field `K`) passes from level `0` to every
  level (`TowerSpectralInvariant.weakBaseChange` at each step).

## Main theorem

`PrimeCyclicBaseChangeTower.exists_isobaricChain_endsAtHeckeFamily`. Assume:

- `K/F` is Galois, `F ⊆ M ⊆ K` (scalar tower), and `F`, `K` have compact adele quotients;
- `hP`: the cuspidal transport statement `CuspidalArithmeticSpectralTransportStatement`;
- `hBC`: unitary weak base changes exist along every step of `T`, as above;
- `S` is a cuspidal realization over `F` of rank `r + 1` with unitary central character,
  whose class is a weak automorphic induction of a Hecke character `χ` of `M`
  (`IsWeakAutomorphicInductionOf`);
- `ρ : Fin (r + 1) → Gal(K/F)` meets every right coset of `Gal(K/M)` exactly once
  (`IsRightCosetFamily`, module `GaloisPlaceCount`).

Then some chain `D` along `T` is unitary, a successive weak base change, starts at the class
of `S` (`StartsAtCuspidal`), and ends at the Hecke family of the conjugates
`conjugateNormFamily χ ρ`, `i ↦ χ ∘ N_{K/M} ∘ ρ i` (`EndsAtHeckeFamily`).

Proof. Let `sc` be a system attached to the class of `S` that is a weak induction of `χ`.
The bottom datum is the pullback of the one-constituent data of `S` along `T.bottomEquiv`.
It is unitary by the first lemma, and `exists_isobaricChain_of_step` gives the chain. The
one-constituent data of `S` satisfy the invariant with profile `underPowerProfile sc`
(`towerSpectralInvariant_ofCuspidal`). The invariant passes to the bottom level along the
pullback (`TowerSpectralInvariant.arithmeticComap`, using `hP`), up the chain, and to the
terminal datum over `K` along `T.topEquiv.symm` (again using `hP`). Over `K`, it says that
an attached system has, at almost every place `w`, the eigenvalue multiset
`underPowerProfile sc w`: the eigenvalues of `sc` at `w ∩ F` raised to `f(w | w ∩ F)`. By
`eventually_power_eq_conjugateNormFamily` (module `InductionBaseChangeHeckeFamily`), at
almost every `w` this multiset is the multiset of values of the conjugates at a uniformizer,
and the conjugates are unramified at `w`. `hasHeckeFamily_of_eventually` concludes.

## Provenance

The chain is the base change of a weak automorphic induction along a solvable tower, as in
Harris, *The local Langlands conjecture for GL(n) over a p-adic field, n < p* (Invent. Math.
134, 1998), proof of Proposition 4.8 and (4.12), with each step from Arthur–Clozel III.4.2
(here the abstract hypothesis `hBC`). The bookkeeping through `TowerSpectralInvariant` is
internal to the project.
