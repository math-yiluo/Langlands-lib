# Inflation compatibility of the local invariant family

Author: Worker 272.

This module proves the published proposition
`Langlands.ClassFieldTheory.Local.LocalInvariantFamilyInflationStatement`
(module `Langlands.ClassFieldTheory.Local.LocalInvariantFamilyLawsStatement`).
The exact-target theorem is

```
theorem localInvariantFamilyInflation :
    LocalInvariantFamilyInflationStatement.{u}
```

in the namespace `Langlands.ClassFieldTheory.Local`. Unfolded, it says: for
every proof `hEx : UnramifiedH2Exhaustion.{u}`, every prime `p`, every p-adic
field `F`, every tower `F ⊆ L ⊆ M` with `L/F` and `M/F` finite Galois (all in
universe `u`), and every `x` in `H²(L/F)`,

```
(localInvariantFamily hEx p).relative F M (relativeInflation F.Carrier L M 2 x) =
  (localInvariantFamily hEx p).relative F L x.
```

The module also proves two general lemmas about transport of relative
cohomology along field isomorphisms.

## Source

Jean-Pierre Serre, *Local Fields*, GTM 67, Springer, 1979 (registered source
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`):

- Chapter XI, §2 (printed page 167, PDF page 173): `H²(/E)` is the direct
  limit of the groups `H²(F/E)` along inflation, and inflation is injective in
  degree two. The invariant `inv_E` is defined on this limit, so a class and
  its inflation have the same invariant.
- Chapter XIII, §3, Corollary 2 of Proposition 7 (printed page 194, PDF
  page 199) states the same convention for local fields, with `H²(L/K)` as a
  subgroup of the Brauer group `B_K`.

The Lean family defines the relative invariant of `L` through a closure
embedding: transport, closure inflation, then the absolute invariant. The
proof below shows that inflation commutes with these steps.

## General lemmas

Let `K, L, M, L', M'` be fields in one universe, with towers `K ⊆ L ⊆ M` and
`K ⊆ L' ⊆ M'`, `L/K` and `L'/K` normal. Let `eL : L ≃ₐ[K] L'` and
`eM : M ≃ₐ[K] M'` be compatible with the inclusions:
`eM (algebraMap L M a) = algebraMap L' M' (eL a)` for all `a : L`.

- `restrictNormalHom_relativeAutPullback`: for `s` in `Gal(M'/K)`, restricting
  the pullback `relativeAutPullback eM s` to `L` gives the pullback along `eL`
  of the restriction of `s` to `L'`. Proof: apply the injective map
  `algebraMap L M` and evaluate both sides with
  `AlgEquiv.restrictNormal_commutes`, `relativeAutPullback_apply` and the
  compatibility.
- `relativeH2Equiv_relativeInflation`: for `x` in `H²(L/K)`,
  `relativeH2Equiv eM (relativeInflation K L M 2 x) =
  relativeInflation K L' M' 2 (relativeH2Equiv eL x)`. Proof: reduce to a
  cocycle `z` (`groupCohomology.H2_induction_on`). Then
  `relativeH2Equiv_H2π` and `groupCohomology.H2π_comp_map_apply` move both
  maps onto cocycles. The two cocycles agree at each pair `(s, t)`. The first
  lemma rewrites the group arguments. The values then agree because
  transported unit inclusion equals unit inclusion of the transported unit,
  which is the compatibility hypothesis applied to unit values.

## The implemented proof of the target

After introducing `hEx`, `p`, `F`, `L`, `M` and `x`:

1. Let `fM := closureEmbedding F.Carrier M`. Let `g` be the composite
   `fM.comp (IsScalarTower.toAlgHom F.Carrier L M)`, an `F`-embedding of `L`
   into the algebraic closure. The image `g.fieldRange` lies in
   `fM.fieldRange`. The proof uses the inclusion algebra
   `(IntermediateField.inclusion hle).toAlgebra` and the two scalar towers
   `F → g.fieldRange → fM.fieldRange` and
   `g.fieldRange → fM.fieldRange → AlgebraicClosure F.Carrier`. Both towers hold
   by `IsScalarTower.of_algebraMap_eq' rfl`. The Library instances
   `embeddedImage_finiteDimensional` and `embeddedImage_isGalois` make both
   images finite Galois over `F`.
2. `localInvariantFamily_relative` and `embeddedRelativeInvariant_apply`
   (module `LocalInvariantFamily`) unfold both relative invariants. The
   invariant of `L` is computed through the chosen embedding
   `closureEmbedding F.Carrier L`.
3. The published `closureInflationTransportIndependence` (module
   `ClosureInflationIndependenceProof`) replaces the chosen embedding of `L`
   by `g.equivFieldRange`.
4. `relativeH2Equiv_relativeInflation`, with `eL := g.equivFieldRange` and
   `eM := fM.equivFieldRange`, moves the inflation past the transport. The
   compatibility holds by `rfl`: both sides are the element
   `fM (algebraMap L M a)` of the closure.
5. The published `closureInflationTowerCompatibility` (module
   `ClosureInflationNaturalityProof`) for the tower
   `g.fieldRange ⊆ fM.fieldRange` removes the inflation inside closure
   inflation. The two sides are then equal.

## Notes

- Axioms used by the target theorem: `propext`, `Classical.choice`,
  `Quot.sound`.
