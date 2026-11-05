# Existence of integral Chevalley data (`ChevalleyLieExistence`)

Author: Worker 239.

This module proves the main result of Worker 239's part of the Existence Theorem:

```
theorem nonempty_chevalleyLieData {J X Y : Type u} [Finite J] [AddCommGroup X]
    [AddCommGroup Y] [Module.Finite ℤ X] (P : RootDatum J X Y) [P.IsReduced] (b : P.Base) :
    Nonempty (ChevalleyLieData P b)
```

Every reduced root datum with a finite index type and a finitely generated character lattice
`X` has integral Chevalley data with Lie relations (the structure of `ChevalleyLieData`) for
every base `b`.

## Proof

Choose a finite family `gen : Fin r → X` that generates `X` (`Module.Finite.exists_fin`). The
short-root module `ℤ^(Idx P b gen)` of `ShortRootModule` carries the representations
`simpleRep i` of `ShortRootRep`. Reindexed by `Fin n`, it gives integral `SL₂`-data for the
simple roots (`shortRootData`). `ChevalleyLieConstruction` then turns these data into
`ChevalleyLieData P b`.

## Results

These results assume `Fintype J` and reduced `P`.

- `three_le_card_idx`: if there is a simple root `i`, then the module has at least three basis
  vectors: `u_i`, `v_β` and `v_{−β}` for a short root `β`. A short root exists: either `α_i`
  itself, or the root given by `exists_isShortRoot_pairing_eq_neg_one`. This bound turns the
  vanishing `E k = 0` for `k > 3` of `SL2Rep` into the vanishing for `k > n` required by
  `SimpleRootData`.
- `root_mem_span_range_idxWt`: every root lies in the `ℤ`-span of the weights of the module.
  Short roots are weights. A root `α_x` that is not short equals `α_{s_x β} − α_β` for a short
  root `β` with `⟨β, α_x^∨⟩ = −1`, and both of these are short roots.
- `span_range_idxWt`: if `gen` spans `X`, then so do the weights of the module. Each `gen w`
  differs from a minimal-norm weight `ν` of its coset `gen w + ℤΦ` (`minimalWeights_nonempty`)
  by an element of the root lattice, and the root lattice lies in the span by the previous item.
- `closure_range_idxWt_comp`: the same statement for the reindexed weights, phrased with
  `AddSubgroup.closure` (`Submodule.span_int_eq_addSubgroupClosure`).
- `finRep b gen i`: `simpleRep b gen i` reindexed along `Fintype.equivFin`. The lemmas
  `finRep_E_one` and `finRep_F_one` identify its operators with the reindexed `raiseMat i` and
  `lowerMat i`.
- `finRep_E_one_map_ne_zero`, `finRep_F_one_map_ne_zero`: these operators are nonzero modulo
  every prime, by `exists_raiseCoeff_eq_one`, `exists_lowerCoeff_eq_one` and
  `colMat_map_ne_zero`.
- `finRep_E_F_comm`: for distinct simple roots, `E i 1` and `F i' 1` commute. This is
  `raiseMat_mul_lowerMat_comm`, reindexed.
- `shortRootData b gen hgen : SimpleRootData P b`:
  - `ℓ = posCorootSum b`, which is positive on the simple roots (`posCorootSum_pos`);
  - `n = |Idx P b gen|`, with weights `idxWt` reindexed;
  - `E i`, `F i` and `φ i R = (finRep b gen i).hom R` come from `finRep`. Each field of
    `SimpleRootData` is the corresponding field of `SL2Rep`;
  - `weyl_weight` is `rep_weyl` combined with `reflection_apply`;
  - `E_F_same` is `E_one_mul_F_one_sub`, and `E_F_comm` is `finRep_E_F_comm`.
- `nonempty_simpleRootData` (finite `J`, `Module.Finite ℤ X`, reduced `P`): `SimpleRootData P b`
  is nonempty.
- `nonempty_chevalleyLieData`: the main theorem above. It is
  `nonempty_chevalleyLieData_of_simpleRootData` applied to `nonempty_simpleRootData`.

`nonempty_chevalleyLieData` depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Provenance

The theorem is the integral input to Chevalley's construction of split reductive groups
(Steinberg, *Lectures on Chevalley groups*, §§1–3; Milne, *Algebraic Groups* (2017), §23.h).
Classically one constructs a semisimple Lie algebra from its root system (Serre's theorem), a
Chevalley basis, and an admissible lattice in a faithful representation. This proof avoids all
three. The representation is the explicit short-root module, with integral `SL₂`-actions for
the simple roots. The root operators for all roots are produced by Weyl conjugation inside the
rational Lie algebra that they generate (`ChevalleyLieConstruction`). The route is internal to
this project.
