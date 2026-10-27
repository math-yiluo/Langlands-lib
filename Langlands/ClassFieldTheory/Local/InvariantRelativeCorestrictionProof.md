# Relative corestriction from the image and restriction laws

Author: Worker 272.

This module proves the published proposition
`Langlands.ClassFieldTheory.Local.InvariantRelativeCorestrictionStatement`
(module `Langlands.ClassFieldTheory.Local.InvariantTransferConsequencesStatement`).
The exact-target theorem is

```
theorem invariantRelativeCorestriction :
    InvariantRelativeCorestrictionStatement.{u}
```

in the namespace `Langlands.ClassFieldTheory.Local`. Unfolded, it says: for
every prime `p` and every raw invariant family `I : InvariantFamily.{u,u} p`,
if `I.RelativeImages` and `I.RelativeRestriction` hold, then
`I.RelativeCorestriction` holds. The maps are the Library's actual
`relativeRestriction` and `relativeCorestriction`.

## Source

Jean-Pierre Serre, *Local Fields*, GTM 67, Springer, 1979 (registered source
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`),
Chapter XI, §2, Proposition 1 (i) and (ii) (printed pages 167–168, PDF pages
173–174). Serre deduces (i), surjectivity of restriction on `H²`, from the
divisibility of `ℚ/ℤ` and the injectivity of the invariants. He then deduces
(ii), `inv ∘ Cor = inv`, from (i) and `Cor ∘ Res = [E':E]`. The Lean proof
follows this route for the finite relative groups.

## The implemented proof

The module contains three auxiliary theorems and the exact-target theorem.

1. `rationalModIntegers_exists_nsmul_eq d hd q`: for `d : ℕ` with `0 < d`
   and `q : RationalModIntegers`, there is `w` with `d • w = q`. Choose a
   rational representative `r` of `q` (`QuotientAddGroup.mk_surjective`) and
   take `w` to be the class of `r / d`. After `QuotientAddGroup.mk_nsmul` and
   `nsmul_eq_mul`, the identity `d * (r / d) = r` is closed by `field_simp`
   using `(d : ℚ) ≠ 0`.

2. `InvariantFamily.relativeRestriction_surjective_of_relativeImages I hImg
   hRes F E M c`: in the tower of the restriction clause (p-adic fields
   `F ⊆ E` over `Padic p`, a field `M` finite over `F` and `E`, Galois over
   both), every `c : relativeCohomology E M 2` is
   `relativeRestriction F E M 2 y` for some `y : relativeCohomology F M 2`.
   - By item 1, choose `w` with `[E:F] • w = I.relative E M c`.
   - `I.relative E M c` lies in the range of `I.relative E M`, which
     `RelativeImages` identifies with `denominatorSubgroup [M:E]`.
   - Hence `[M:F] • w = [M:E] • ([E:F] • w) = 0`. Here the tower law
     `Module.finrank_mul_finrank F E M` and `mul_nsmul` are used. So `w` lies
     in `denominatorSubgroup [M:F]`, which is the range of `I.relative F M`.
     Choose `y` with `I.relative F M y = w`.
   - `RelativeRestriction` gives
     `I.relative E M (relativeRestriction F E M 2 y) = [E:F] • w =
     I.relative E M c`. Injectivity of `I.relative E M` (the first part of
     `RelativeImages`) gives `relativeRestriction F E M 2 y = c`.

3. `InvariantFamily.relativeCorestriction_of_relativeImages I hImg hRes`:
   `I.RelativeCorestriction`. Given the tower and `c`, write
   `c = relativeRestriction F E M 2 y` by item 2. The Library theorem
   `relativeH2CorestrictionRestriction` (module
   `RelativeH2CorestrictionRestrictionProof`) gives
   `relativeCorestriction F E M 2 (relativeRestriction F E M 2 y) =
   [E:F] • y`. `map_nsmul` and `RelativeRestriction` turn both sides into
   `[E:F] • I.relative F M y`.

The exact-target theorem introduces `p`, `I` and the two hypotheses and
applies item 3.

## Notes

- `InflationCompatibility` and the `H¹` clause of `RelativeClassFormation`
  are not used.
- Items 1 and 2 are exported for reuse, for example in the absolute
  corestriction proof.
- Axioms used by the target theorem: `propext`, `Classical.choice`,
  `Quot.sound`.
