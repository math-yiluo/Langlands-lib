# Actual central quotients and the rational-character valuation image

Author: Worker 200.

This derived construction implements the quotient step in Renard,
*Représentations des groupes réductifs p-adiques*, 9 July 2026 edition,
V.2.6, printed p.108 (PDF p.114), source ID
`renard-2026-representations-groupes-reductifs-padiques`, SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The proposition deduces finiteness of \(G/({}^0G A_G)\) from the preceding
lemma's finite-index assertion about the valuation image of the split center.
The present unit constructs the quotient comparison and proves this implication.
It retains finite index as an explicit premise; it does not prove the preceding
lemma for general reductive groups.

This is a prerequisite for the finite quotient used in Waldspurger,
*La formule de Plancherel pour les groupes p-adiques (d'après Harish-Chandra)*
(2003), III.7.1, printed p.274 (PDF p.40), source ID
`waldspurger-2003-plancherel`, SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
Its character kernel is the one defined in I.1, printed p.239 (PDF p.5).
No representation or spectral finiteness assertion is used.

## Generic quotient comparison

Let \(f:G\to L\) be a surjective group homomorphism, with \(L\) commutative,
and let \(A\) be a normal subgroup of \(G\). The group and target universes
are independent. `quotientKerSupEquivQuotientMap` constructs the
multiplicative equivalence
\[
 G/(\ker f\vee A)\;\simeq\; L/f(A).
\]
Here \(\vee\) is the subgroup join, and `A.map f` is the actual image subgroup.
The normality premises make both sides group quotients.

The proof composes \(f\) with the projection \(L\to L/f(A)\). The kernel
of this composite is the preimage of \(f(A)\), which Mathlib's
`Subgroup.comap_map_eq` identifies with \(A\vee\ker f\).
Commuting the join gives the specified source subgroup. The composite is
surjective, so the first isomorphism theorem supplies the equivalence.
`quotientKerSupEquivQuotientMap_mk` proves that the coset of \(g\) maps
to the coset of \(f(g)\). The forward map is the actual quotient homomorphism.

## Actual rational points and central images

Let \(F:\mathrm{Type}\ u\) carry `Field`, `ValuativeRel`, `TopologicalSpace`
and `IsNonarchimedeanLocalField`, and let \(G\) be the shared actual
`GroupScheme (Spec (CommRingCat.of F))`. There is no characteristic,
connectedness, reductivity or splitness restriction for this construction.
No topology on \(G(F)\) is selected or needed.

Write \(H_G\) for the published `rationalCharacterValuation G`,
\(N_G\) for `rationalCommonNormKernel G`, and \(\Lambda_G\) for
`rationalCharacterValuationImage G`. These are actual rational-character
evaluation and integer order, their common norm kernel, and the actual range.
`rationalSubgroupQuotientEquiv G A` gives, for every normal point subgroup \(A\),
\[
 G(F)/(N_G\vee A)\;\simeq\;
 \Lambda_G/\operatorname{map}_{H_G^{\mathrm{range}}}(A).
\]
The range restriction is surjective. Its kernel is \(N_G\) by the already
proved `MonoidHom.ker_rangeRestrict` and `rationalCharacterValuation_ker`.
The representative formula `rationalSubgroupQuotientEquiv_mk` sends \(g\)
to its actual valuation coset.

For any central morphism \(i:H\to G\),
`centralRationalPointImage_map_eq_range` proves that mapping the existing
`GroupScheme.centralRationalPointImage i hi` through the inclusion of
`schemeCenterPoints G` gives precisely `(rationalPoints.map i).range`.
The proof uses the range-of-composite identity and the defining point map.
This compares the existing objects and introduces no alternative center.
It needs no equality between scheme-center points and the abstract group center.

For a commutative group scheme \(T\), an actual morphism \(s:T\to G\) and
`hs : GroupScheme.IsCentral s`, `rationalCentralQuotientEquiv s hs` gives
\[
 G(F)/(N_G\vee s(T(F)))\;\simeq\;
 \Lambda_G/\operatorname{splitValuationImage}(s).
\]
The target subgroup is the existing `RenardCartan.splitValuationImage s`
from `RenardRepresentativeData`: the range of the composite of the actual
point map and the range-restricted valuation. Its equality with the mapped
point subgroup is Mathlib's `MonoidHom.map_range`.
The published `IsCentral.range_le_center` makes the ambient point subgroup
normal. `rationalCentralQuotientEquiv_mk` sends each point coset to its
valuation coset.

The construction needs only centrality, even though its intended application
has \(T=A_G\) a split component. In that application centrality is the
published `IsSplitComponent.isCentralSplitTorus.isCentral`.
All quotients here are abstract group quotients of actual rational points.
No scheme quotient or assertion about its rational points is involved.

## Conditional finiteness and remaining obligations

`finite_rationalCentralQuotient` takes the explicit premise
`hindex : (RenardCartan.splitValuationImage s).FiniteIndex`.
Mathlib identifies finite index with finiteness of the target quotient, and
the constructed equivalence transfers finiteness to the actual source quotient.
This proves the quotient step of Renard's proposition with that premise visible.

The actual split-component existence and finite-index valuation-image theorem
remain with the structural owners. In particular, finite generation of the
character group or finite cokernel of character restriction alone is not
silently substituted for this premise. No central compactness, abstract-center
comparison, topological quotient equivalence, Haar identity, stabilizer
finiteness, orbit-family finiteness or Plancherel statement is asserted here.
