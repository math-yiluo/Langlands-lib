# Canonical base extension of Galois-fixed geometric components

This derived construction removes the supplied closure embedding from the
base-extension map on the full Galois-fixed component subgroup. It imports
`GeometricComponentFixedBaseChange` and uses the actual geometric component,
coefficient-point and Galois-action constructions already published there and
in its imports.

Let `k` and `K` be arbitrary fields in the same universe, with `Algebra k K`.
Let `H` be an actual group scheme over `Spec k` with `Smooth H.X.hom` and
`IsAffineHom H.X.hom`. Write `H_K = baseChanged k K H`. There is no
algebraicity, separability, perfection or characteristic hypothesis on `K/k`,
and no connectedness or reductivity hypothesis on `H`.

The carrier `GeometricComponents k H` is the connected-component group of the
actual pullback to `AlgebraicClosure k`. Its subgroup
`geometricComponentFixedSubgroup k H` consists of components fixed by every
element of `Field.absoluteGaloisGroup k`. It includes all such components,
whether or not they have representatives over `k`.

For a specified `k`-algebra embedding
`i : AlgebraicClosure k →ₐ[k] AlgebraicClosure K`, the file defines
`geometricComponentBaseChangeEquivOfEmbedding k K H i` and
`geometricComponentFixedBaseChangeOfEmbedding k K H i`. These install the
closure algebra structure induced by `i` and its compatible scalar tower, then
use the published geometric equivalence and full-fixed homomorphism. Write
these maps as `E_i` and `F_i`. The value law
`geometricComponentFixedBaseChangeOfEmbedding_val` is

```text
(F_i(c)).val = E_i(c.val).
```

The theorem `geometricComponentBaseChangeEquivOfEmbedding_conjugate` states
that, for embeddings `i,j` and a source Galois automorphism `sigma` satisfying
`j(sigma(a)) = i(a)` for every source closure coefficient `a`,

```text
E_j(sigma • c) = E_i(c)
```

for every geometric component `c`. The private section comparison proves this
first on actual closure-valued sections. Applying `baseChangeCoeffEquiv` and
`coefficientBaseChangeEquiv` reduces it to affine-point functoriality:
`j` after `sigma` equals `i`. The published point-action formula and
`geometricComponentOfPoint_surjective` then give the component identity.

The private field lemma `embeddings_differ_by_automorphism` supplies such a
`sigma` for any two embeddings of a normal field extension `E/k` into a field
`L`. It uses `AlgHom.restrictNormal'` on the identity of `L`, with the two
algebra structures induced by `i,j`; `AlgHom.restrictNormal_commutes` gives
`j(sigma(a)) = i(a)`. Specializing to the algebraic closure and applying the
full source fixedness condition proves
`geometricComponentFixedBaseChangeOfEmbedding_independent`:

```text
F_i = F_j.
```

This is equality of homomorphisms on the entire fixed subgroup.

The main definition `geometricComponentCanonicalBaseChange k K H` is

```text
geometricComponentFixedSubgroup k H
  →* geometricComponentFixedSubgroup K H_K.
```

It uses the embedding supplied by `IsAlgClosed.lift`.
`geometricComponentCanonicalBaseChange_eq_ofEmbedding` proves that every
compatible closure embedding computes this same homomorphism. In particular,
`geometricComponentCanonicalBaseChange_val` identifies its underlying value
with `E_i(c.val)` for any `i`.
`geometricComponentCanonicalBaseChange_injective` applies the injectivity of
that geometric equivalence after forgetting subgroup membership.

`geometricComponentCanonicalBaseChange_rational` proves, for every
`q : RationalComponentQuotient H`,

```text
geometricComponentCanonicalBaseChange k K H
    (rationalGeometricComponentToFixed k H q)
  = rationalGeometricComponentBaseChangeToFixed k K H q.
```

Here `RationalComponentQuotient H` is the ordinary quotient of rational
sections by those factoring through the identity component. The proof installs
the chosen lift and applies the published rational comparison. It does not
require every fixed component to be rationally represented.

When a compatible closure algebra and scalar tower are already specified,
`geometricComponentCanonicalBaseChange_eq` identifies the canonical map with
`geometricComponentFixedBaseChange k K H` for those instances. It uses the
comparison with the corresponding explicit embedding,
`toAlgebra_algebraMap`, congruence and proof irrelevance for the tower witnesses.

For any actual group-scheme homomorphism `f : H ⟶ H'`, with `H'` also smooth
and affine, `geometricComponentCanonicalBaseChange_naturality` states

```text
B_H' (geometricComponentFixedMap k f c)
  = geometricComponentFixedMap K (baseChange(f)) (B_H(c)),
```

where `B` is the canonical map and
`baseChange(f) = (GroupScheme.baseChange (baseMap k K)).map f`. Installing the
chosen lift and using the instance comparison reduces this to the published
full-fixed naturality law.

The provenance is internal derivation: normal restriction compares embeddings,
actual affine-point functoriality compares their section maps, and full Galois
fixedness removes their difference. The canonical map and its laws then reuse
these comparisons and the published fixed-subgroup construction. The file
introduces no new external structural theorem. It proves injectivity and
embedding independence; it asserts no surjectivity, effective descent,
identification of all fixed components with rationally represented ones, or
comparison with points of an fppf quotient.
