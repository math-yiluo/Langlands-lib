# Frobenius-stable conjugates from Lang's theorem

Author: Worker 1442.

This internal supporting module constructs actual conjugate inclusions with
Frobenius-invariant ranges, conditional on a conjugacy between the specified
inclusion and its Frobenius transform. All schemes and fields use arbitrary
common universe `u`.

For a base map `b : S ⟶ B`, an endomorphism `a : S ⟶ S` over `B`, and a group
scheme `G` over `B`, `descentBasePoint` pulls a rational point of `G_S` back
along `a` and applies the canonical `descentBaseChangeIso`. Its projection to
`G` is coefficient pullback of the original point. Naturality of inner
automorphisms gives `descentBasePoint_innerIso` and
`descent_conjugate_inclusion`: transport of a conjugate inclusion is conjugation
of the transported inclusion by the transported point.

Now let `k` be a finite field with a `Fintype` instance, let `Ω/k` be an
algebraic algebraically closed extension, and let `G/k` be smooth, connected
and affine. Write `F` for canonical descent transport induced by the
cardinality-of-`k` Frobenius automorphism of `Ω`.
`exists_eq_inv_mul_descentBasePoint` proves Lang's equation
`x = g⁻¹ * F(g)` on rational points of the actual pullback `G_Ω`. It transfers
the published `FiniteFieldTorsorPoint.exists_eq_inv_mul_frobenius` across the
multiplicative equivalence between rational points of the pullback and
extension-valued points of the original group. Comparing projections identifies
the two Frobenius actions.

For an arbitrary group scheme `H/Ω` and a specified homomorphism
`i : H ⟶ G_Ω`, assume `SubgroupConjugate F(i) i`. This includes a rational
point `x` and an actual source isomorphism `e` satisfying
`F(i) ≫ innerIso(x).hom = e.hom ≫ i`. Lang supplies `g` with
`F(g) = g * x`. The transport identity and the composition law for inner
automorphisms then give

```
F(i ≫ innerIso(g).hom) = e.hom ≫ (i ≫ innerIso(g).hom).
```

Precomposition by a source isomorphism preserves the range on every relative
test scheme. This proves `exists_frobeniusStableConjugator`.
`frobeniusStableConjugatingPoint` chooses such a point and
`frobeniusStableConjugate` is the actual inclusion
`i ≫ innerIso(g).hom`. The accompanying lemmas retain its conjugacy to `i` and
the exact all-test range equality under Frobenius transport. No closedness or
torus assumption is needed for this construction. When `i` is a maximal-torus
inclusion, `IsMaximalTorus.frobeniusStableConjugate` preserves its maximality
by the published ambient-isomorphism transport theorem.

The provenance is internal: the construction combines the published canonical
pullback, point, inner automorphism, range and Lang interfaces. It does not
supply maximal-torus conjugacy, establish maximality of a Frobenius transform,
or prove finite-field geometric maximal-torus existence. Those inputs remain
separate obligations; in particular, the conjugacy premise is explicit.
