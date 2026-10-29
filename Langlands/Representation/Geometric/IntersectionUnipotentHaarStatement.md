# Haar modulus on the actual unipotent intersection

`Langlands.Geometric.PadicIntersectionUnipotentHaarModulus` states the
identification of the actual intersection Haar character with the explicit
refined block character. This module defines the proposition and proves only
the local compactness needed to state that character.

Fix any prime `p`, actual finite extension `F : PadicField p`, supplied
compatible `T : F.TopologicalData`, natural rank `n`, block shapes `B, C`,
permutation `w`, block refinement `S` of `B`, and
`hS : IsIntersectionRefinement B C w S`. All three equalities in `hS`
are retained. There is no positive-rank or minimality restriction.
The field universe `uF` is arbitrary.

Write

```
M = B.leviSubgroup F.Carrier
N = C.leviSubgroup F.Carrier
V = C.unipotentSubgroup F.Carrier
g = GeneralLinear.permutation n F.Carrier w
L = General.intersectionIn M N g
U = intersectionSource M V g
```

Here `L` is the subgroup `M ∩ g⁻¹ N g`, viewed inside `M`, and `U` is
the literal ambient subgroup `M ⊓ V.comap (conj g)` of `GL_n(F)`.
In particular, membership in `U` means that `u ∈ M` and `g u g⁻¹ ∈ V`.
Every topology is induced by the exact supplied `T.topology`.

The published continuous equivalences

```
eL = refinedLeviIntersectionEquiv F.Carrier B C w S hS
eU = refinedUnipotentIntersectionEquiv F.Carrier B C w S hS
```

identify the actual refined Levi and radical with `L` and `U`. Both maps
send a coordinate element to its literal `B.leviEmbedding` in the ambient
general linear group. Define the action homomorphism by the existing

```
ι = General.intersectionToCorrectionNormalizer M N M V g
      M.le_normalizer
      (C.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier).
```

Thus `HaarModulus.normalizerConj U (ι m)` is conjugation by the ambient
matrix of `m`. No normalizer or action is supplied as an additional premise.

## The proposition

For every `m : L`, every Borel measurable structure on `U`, and every
supplied Haar measure `μ` on `U`, the first conjunct states

```
μ.map (HaarModulus.normalizerConj U (ι m))
  = ((T.refinedLeviModulus B S (eL.symm m) : NNReal)⁻¹) • μ.
```

The Haar measure is not assumed regular, normalized, or constructed from
coordinates. The factor is the inverse modulus because this is a pushforward
under forward conjugation.

The second conjunct is equality of positive homomorphisms on the refined Levi:

```
((HaarModulus.normalizerCharacter U).comp ι).comp eL.toMulEquiv.toMonoidHom
  = T.refinedLeviModulus B S.
```

`normalizerCharacter` uses its published canonical Borel measurable structure.
This equality identifies the actual Haar character, and is independent of the
measurable structure quantified in the first conjunct.

`TopologicalData.intersectionUnipotentLocallyCompactSpace` proves local
compactness of `U` by transporting the published
`T.refinedUnipotentLocallyCompactSpace B S` through the inverse of `eU`.
It uses the open embedding underlying that inverse homeomorphism. Its field
topology is exactly `T.topology`; it adds no local compactness hypothesis.

## Provenance and boundary

The registered original is Bernstein and Zelevinsky, *Induced representations
of reductive p-adic groups I* (1977),
`bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Section 6.3, printed page 468, identifies
`(M ∩ w⁻¹(Q), M ∩ w⁻¹(N), M ∩ w⁻¹(V))` as the source intersection
parabolic triple for its minimal representatives. Section 1.7, printed
pages 443–444, defines the automorphism module with the inverse automorphism
in the integrand. These conventions explain the actual groups and the
inverse pushforward factor above.

The exact proposition, its coordinate packaging, and the broader quantification
over arbitrary permutations with supplied intersection refinements are internal
derivations. They are not asserted verbatim in the original. Their inputs are
the published `PadicRefinedUnipotentHaarModulus`, the canonical continuous
equivalences above, and their published
`refinedUnipotentIntersectionEquiv_normalizerConj` compatibility. This module
imports the refined statement, and does not use an unproved Haar law in its
local compactness proof. A later proof may transport the independently
published refined Haar law through those equivalences.

This statement concerns the radical `M ∩ g⁻¹ V g` of the source intersection
parabolic. The separate BZ77 correction subgroup `U_B ∩ g⁻¹ P_C g`, where
`U_B` is the radical of `P_B`, has a different definition.
This module does not state a quotient-integral comparison, an equivalence of
representations, scalar correction cancellation, or the normalized orbit
natural isomorphism. Project errata searches in the preceding source and
dependency audit found no applicable correction to these conventions.

Author: Worker 76.
