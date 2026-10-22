# Relative corestriction after restriction

Author: Worker 23.

This module proves the published proposition
`Langlands.ClassFieldTheory.Local.RelativeH2CorestrictionRestrictionStatement`
(module `Langlands.ClassFieldTheory.Local.RelativeH2CorestrictionRestrictionStatement`).
The exact-target theorem is

```
theorem relativeH2CorestrictionRestriction :
    RelativeH2CorestrictionRestrictionStatement.{u}
```

in the namespace `Langlands.ClassFieldTheory.Local`. Unfolded, it says: for
fields `K L M` in one arbitrary universe `u`, with algebra structures
`K → L`, `K → M`, `L → M` forming a scalar tower, `L/K`, `M/K`, `M/L` finite
dimensional and `M` Galois over both `K` and `L`, every
`x : relativeCohomology K M 2` satisfies

```
relativeCorestriction K L M 2 (relativeRestriction K L M 2 x) =
  Module.finrank K L • x.
```

`L/K` is not assumed normal. The theorem uses the Library's actual
`relativeRestriction`, `relativeCorestriction` and `relativeCohomology`; no
statement or imported file is changed.

## Source

Jean-Pierre Serre, *Local Fields*, GTM 67, Springer, 1979 (registered source
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`),
Chapter VII, section 7, printed page 119 / PDF page 125:

> Proposition 6. If n = Card(G/H), then Cor ∘ Res = n.

Serre proves it by shifting from degree 0, where it says that the norm
`N_{G/H}(a) = n a` for `G`-invariant `a`. The Lean proof does not repeat that
argument: it uses the published Tate-cohomology identity
`Langlands.Tate.corestriction_restriction`, which is that proposition for the
constructed Tate restriction and corestriction in every degree, and transports
it to the ordinary relative maps.

## The implemented proof

The module contains three auxiliary theorems in the section `Tower`, where
`K L M : Type u` are fields with the tower structures above (each theorem lists
only the finiteness and Galois instances it uses).

1. `relativeRestriction_comp_subgroupCohomologyIso K L M n` (no finiteness
   hypotheses, every `n : ℕ`):

   ```
   relativeRestriction K L M n ≫ (relativeSubgroupCohomologyIso K L M n).hom =
     groupCohomology.map (relativeGaloisSubgroup K L M).subtype
       (𝟙 (Rep.res (relativeGaloisSubgroup K L M).subtype (unitsRepresentation K M))) n
   ```

   Restriction to `Gal(M/L)` followed by the Library's reindexing of
   `Gal(M/L)` cohomology to the actual subgroup
   `relativeGaloisSubgroup K L M` of `Gal(M/K)` is Mathlib's ordinary
   restriction along the subgroup inclusion. Proof: both sides are
   `groupCohomology.map`, so `groupCohomology.map_comp` merges the left side
   into one map and `groupCohomology.map_congr` reduces the claim to the
   underlying group homomorphisms and coefficient maps. The group maps agree
   because `relativeGaloisSubgroupEquiv K L M` sends `σ` to
   `σ.restrictScalars K` (`relativeGaloisSubgroupEquiv_apply`), so applying
   restriction of scalars to the inverse image of a subgroup element returns
   that element. The coefficient maps are both the identity on `Additive Mˣ`
   and agree by `rfl`.

2. `relativeCorestriction_relativeRestriction K L M n x`, assuming
   `FiniteDimensional K M`, for every `n : ℕ` with `NeZero n` and
   `x : relativeCohomology K M n`:

   ```
   relativeCorestriction K L M n (relativeRestriction K L M n x) =
     (relativeGaloisSubgroup K L M).index • x
   ```

   Write `H = relativeGaloisSubgroup K L M`, `A = unitsRepresentation K M`,
   `eA` and `eB` for the positive-degree Tate/ordinary comparison
   isomorphisms `(TateCohomology.isoGroupCohomology n).app A` and
   `.app (Rep.res H.subtype A)`. The published comparison
   `Langlands.Tate.restriction_groupCohomology H A n` (module
   `Langlands.Cohomology.Tate.PositiveRestriction`, owned by task
   c75747af) states that the constructed Tate restriction equals
   `eA.hom ≫ groupCohomology.map H.subtype (𝟙 _) n ≫ eB.inv`. Applying it
   to `eA.inv x`, cancelling `eA.hom (eA.inv x) = x`, and applying item 1
   to `x` gives the auxiliary equation `key`:

   ```
   Langlands.Tate.restriction H A n (eA.inv x) =
     eB.inv ((relativeSubgroupCohomologyIso K L M n).hom (relativeRestriction K L M n x)).
   ```

   By the definition of `relativeCorestriction` (stated as
   `relativeCorestriction_eq` in `Local.Corestriction`; the proof uses
   `change`, which holds by definitional unfolding), the left side of the goal is
   `eA.hom (Langlands.Tate.corestriction H A n (eB.inv (… (relativeRestriction K L M n x))))`.
   Rewriting with the displayed equation turns it into
   `eA.hom (corestriction H A n (restriction H A n (eA.inv x)))`;
   `Langlands.Tate.corestriction_restriction` (module
   `Langlands.Cohomology.Tate.TransferProof`) replaces the inner composite by
   `H.index • eA.inv x`, `map_nsmul` moves the scalar out of `eA.hom`, and
   `Iso.inv_hom_id_apply` cancels `eA.hom (eA.inv x)`. The finite-type
   instances on `Gal(M/K)`, `H` and the quotient are the same
   `Fintype.ofFinite` instances used in the definition of
   `relativeCorestriction`.

3. `relativeGaloisSubgroup_index K L M`, assuming `FiniteDimensional K L`,
   `FiniteDimensional K M`, `FiniteDimensional L M`, `IsGalois K M` and
   `IsGalois L M`:

   ```
   (relativeGaloisSubgroup K L M).index = Module.finrank K L
   ```

   Start from Mathlib's `Subgroup.index_mul_card`:
   `H.index * Nat.card H = Nat.card Gal(M/K)`. The isomorphism
   `relativeGaloisSubgroupEquiv K L M : Gal(M/L) ≃* H` gives
   `Nat.card H = Nat.card Gal(M/L)`. `IsGalois.card_aut_eq_finrank` turns
   the two Galois-group cardinalities into `finrank L M` and `finrank K M`,
   and the tower law `Module.finrank_mul_finrank K L M` rewrites
   `finrank K M` as `finrank K L * finrank L M`. Cancelling the positive
   factor `finrank L M` (`Module.finrank_pos`, `Nat.eq_of_mul_eq_mul_right`)
   gives the claim. Normality of `L/K` is not used: `H` is only a subgroup,
   and only its index is computed.

The exact-target theorem `relativeH2CorestrictionRestriction` introduces the
statement's fields, instances and class `x`, and rewrites with item 2 at
`n = 2` and then item 3.

## Notes

- Items 1 and 2 hold in every positive degree; item 2 is stated with the
  subgroup index and needs only `FiniteDimensional K M`. They are exported
  because downstream work may use other degrees, but they are not part of the
  target statement.
- The file sets `backward.isDefEq.respectTransparency false`, as do the
  Tate modules it uses (`PositiveRestriction`, `TransferProof`). Without it,
  two `rw` steps fail: the coefficient `LinearEquiv.refl` in
  `relativeSubgroupCohomologyIso` and the class `x` carry the
  `IntegerScalars` ring structure `ULift.ring`, while the expected types use
  the instance path through `ULift.commRing`. The two agree only after
  unfolding, which the option permits during unification.
- Axioms used by the target theorem: `propext`, `Classical.choice`,
  `Quot.sound`.
