# Reduction of aligned type-`D` spin covers to the vector quotient and Tits's forms

Author: Worker 349.

Module `Langlands.GroupScheme.SimplyConnected.ClassicalTypeDAlignedSpinCoverReduction`. It
contains one proved theorem and states nothing new.

## `classicalTypeDAlignedSpinCover_of_vectorQuotient`

```
TypeDVectorQuotientStatement.{u} →
  Quaternionic.EvenSpecialOrthogonalFormStatement.{u} →
    ClassicalTypeDAlignedSpinCoverStatement.{u}
```

Both premises are explicit hypotheses, so this theorem by itself is conditional. The
Library proves them as `Langlands.GroupScheme.typeDVectorQuotient`
(`SimplyConnected/TypeDVectorQuotient`) and
`Langlands.GroupScheme.Quaternionic.evenSpecialOrthogonalForm` (`EvenOrthogonalForm/Proof`).
The module `ClassicalTypeDAlignedSpinCoverProof` applies this reduction to those two
theorems.

## Proof

Take the data `K, G, d, n, e` and the hypotheses of `ClassicalTypeDAlignedSpinCoverStatement`.

1. The target's star hypothesis is assumed at the vertices `a` with `(e a).val + 2 < n`.
   Since `n ≥ 4`, the vertex with `(e a).val = 0` is one of them (`omega`), so the star action
   fixes the vertex numbered `0`. With the other hypotheses (simply connected, absolutely almost
   simple, numbered as `CartanMatrix.D n`), `TypeDVectorQuotientStatement` gives `H`, a central
   isogeny `p : G ⟶ H`, an isomorphism of `H_{K^s}` with the identity component of the split
   `O_{2n}` over `K^s = SeparableClosure K`, and `d.FundamentalWeightTrivialOnKernel v p` for
   every vertex `v` numbered `0`.
2. `EvenSpecialOrthogonalFormStatement` applied to `H`, `n`, `n ≥ 4` and that isomorphism
   gives a central division algebra `D` over `K`, natural numbers `degree > 0` and `m` with
   `dim_K D = degree²` and `m * degree = 2n`, an involution `σ` of the first kind whose
   symmetric subspace has dimension `degree * (degree + 1) / 2`, a nondegenerate
   `σ`-quadratic form `q` on `D^m`, smoothness of `O(q) = σ.isometryGroup q`, and an
   isomorphism `φ : H ≅ σ.connectedIsometryGroup q = O(q)⁰` (the identity component).
3. These are the algebra, involution and form of the conclusion; the cover is
   `π = p ≫ φ.hom ≫ identityComponentι (σ.isometryGroup q) : G ⟶ O(q)`.
   - `σ.IsSpinCover q π`: `G` is simply connected (hypothesis), `O(q)` is smooth (step 2),
     and `p ≫ φ.hom : G ⟶ O(q)⁰` is a central isogeny (`IsCentralIsogeny.comp_iso`) whose
     composite with the inclusion of the identity component is `π` (associativity).
   - Alignment at every vertex `v` numbered `0`: `FundamentalWeightTrivialOnKernel.comp_iso`
     (module `SpinCoverFundamentalWeightTransport`) transports the alignment of `p` to
     `p ≫ φ.hom`, and `FundamentalWeightTrivialOnKernel.comp_identityComponentι` to
     `(p ≫ φ.hom) ≫ identityComponentι _`, which is `π` after reassociation.

The proof uses only `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

Internal. The theorem only composes the conclusions of the two premises with the published
transport lemmas. The mathematics is that of Tits 1968, §3 (Théorème 1 and Remarque 3), as
cited in `TypeDVectorQuotientStatement.md` and
`Quaternionic/EvenSpecialOrthogonalFormStatement.md`: the vector quotient of the simply
connected group is a form of `SO_{2n}`, every such form is `O(q)⁰`, and composing with the
inclusion `O(q)⁰ ⊆ O(q)` gives the spin cover of the target.
