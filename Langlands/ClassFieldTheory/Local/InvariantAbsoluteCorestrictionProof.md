# Absolute corestriction from bijective invariants and the restriction law

Author: Worker 272.

This module proves the published proposition
`Langlands.ClassFieldTheory.Local.InvariantAbsoluteCorestrictionStatement`
(module `Langlands.ClassFieldTheory.Local.InvariantTransferConsequencesStatement`).
The exact-target theorem is

```
theorem invariantAbsoluteCorestriction :
    InvariantAbsoluteCorestrictionStatement.{u}
```

in the namespace `Langlands.ClassFieldTheory.Local`. Unfolded, it says: for
every prime `p` and every raw invariant family `I : InvariantFamily.{u,u} p`,
if `I.AbsoluteIsomorphisms` and `I.AbsoluteRestriction` hold, then
`I.AbsoluteCorestriction` holds. The maps are the Library's actual
`absoluteRestriction` and `absoluteCorestriction` for the supplied closure
embedding.

## Source

Jean-Pierre Serre, *Local Fields*, GTM 67, Springer, 1979 (registered source
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`),
Chapter XI, §2, Proposition 1 (i) and (ii) (printed pages 167–168, PDF pages
173–174). Serre deduces (i), surjectivity of restriction on `H²`, from the
divisibility of `ℚ/ℤ` and the injectivity of the invariants. He then deduces
(ii), `inv ∘ Cor = inv`, from (i) and `Cor ∘ Res = [E':E]`. The Lean proof
follows this route for continuous cohomology of the algebraic closures.

## The implemented proof

The module contains four auxiliary results and the exact-target theorem. The
file declares a local instance `CompactSpace (Field.absoluteGaloisGroup K)`
for fields of characteristic zero, the same instance as in the Library module
`AbsoluteCorestriction`, where it is also local.

1. `exists_nsmul_eq_of_pos d hd q` (private): for `d : ℕ` with `0 < d` and
   `q : RationalModIntegers`, there is `w` with `d • w = q`. Choose a rational
   representative `r` of `q` and take `w` to be the class of `r / d`. The
   identity `d * (r / d) = r` is closed by `field_simp`. The same fact is
   proved as `rationalModIntegers_exists_nsmul_eq` in the relative
   corestriction proof module. It is repeated here so that this module does
   not depend on that one.

2. `absoluteCorestriction_absoluteRestriction K L q y`: for fields `K`, `L`
   in universe `u` with `CharZero K`, a finite extension `L/K`, a supplied
   compatible closure embedding, every degree `q` and every
   `y : absoluteCohomology K q`,

   ```
   absoluteCorestriction K L q (absoluteRestriction K L q y) =
     Module.finrank K L • y
   ```

   Write `A = absoluteUnitDiscreteModule K`, `H = openSubgroup K L` and
   `T = subgroupCohomologyIso K L q` (all in the namespace
   `AbsoluteRestriction`).
   - The Library theorem
     `AbsoluteRestriction.continuousRestriction_comp_subgroupCohomologyIso`
     gives `absoluteRestriction K L q y = T.hom (continuousRestriction A H q y)`.
   - By definition, `absoluteCorestriction K L q` is `T.inv` followed by
     `continuousCorestriction A H q`. After `unfold` and `change`,
     `Iso.hom_inv_id_apply` cancels `T.inv (T.hom _)`. The left side becomes
     `continuousCorestriction A H q (continuousRestriction A H q y)`.
   - The Library theorem `continuousRestriction_corestriction_index`
     (module `Langlands.Cohomology.Continuous.CorestrictionIndexProof`),
     applied to `y`, says this equals `H.index • y`.
   - `AbsoluteRestriction.index_eq_finrank` replaces `H.index` by
     `Module.finrank K L`.

   The proof sets `backward.isDefEq.respectTransparency false`, as the Library
   module `AbsoluteCorestriction` does for the same isomorphism.

3. `InvariantFamily.absoluteRestriction_surjective_of_absoluteIsomorphisms
   I hIso hRes F E x`: in the setting of the restriction clause, every
   `x : absoluteCohomology E 2` is `absoluteRestriction F E 2 y` for some
   `y : absoluteCohomology F 2`.
   - By item 1, choose `w` with `[E:F] • w = I.absolute E x`.
   - By surjectivity of `I.absolute F`, choose `y` with `I.absolute F y = w`.
   - `AbsoluteRestriction` gives
     `I.absolute E (absoluteRestriction F E 2 y) = [E:F] • w =
     I.absolute E x`. Injectivity of `I.absolute E` gives the claim.

4. `InvariantFamily.absoluteCorestriction_of_absoluteIsomorphisms I hIso
   hRes`: `I.AbsoluteCorestriction`. The clause contains the instance
   `CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier`.
   The proof introduces the same term as a local instance. Given `x`, write
   `x = absoluteRestriction F E 2 y` by item 3. Item 2, `map_nsmul` and
   `AbsoluteRestriction` turn both sides into `[E:F] • I.absolute F y`.

The exact-target theorem introduces `p`, `I` and the two hypotheses and
applies item 4.

## Notes

- Item 2 holds in every degree and for arbitrary fields of characteristic
  zero. It is exported for reuse.
- Axioms used by the target theorem: `propext`, `Classical.choice`,
  `Quot.sound`.
