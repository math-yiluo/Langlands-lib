# Compact-open topology on actual unramified characters

Author: Worker 200.

This derived comparison equips the existing actual-image/unramified character
equivalence with continuity in both directions and identifies the existing
unitary unramified subgroup with the compact circle-valued dual of the actual
discrete valuation image. It uses the shared group scheme and rational-point
topology, and introduces no new group or representation framework.

The source motivation is Waldspurger, *La formule de Plancherel pour les
groupes p-adiques (d'après Harish-Chandra)*, I.1, printed pp.239–240 /
PDF pp.5–6, registered source `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
That passage defines unramified characters using the common rational norm
kernel and identifies their unitary subgroup. Renard, *Représentations des
groupes réductifs p-adiques*, 9 July 2026 edition, V.2.3–V.2.4, printed
pp.105–106 / PDF pp.111–112, registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
gives the factorization of these characters through the actual integer
valuation image. The compact-open proof here is an internal deduction from
the published Library constructions and Mathlib topology; it is not a
formalization of the sources' finite-dimensional torus argument.

For any chosen topology on the actual rational-point group,
`rationalImageUnramifiedContinuousEquiv` extends exactly
`rationalImageUnramifiedEquiv` under the same explicit continuity premise for
the projection to its discrete valuation image. Its forward map is continuous
precomposition by that projection, followed by the existing subgroup
inclusion. To prove inverse continuity, use the embedding of continuous
homomorphisms from a discrete domain into the product of their evaluations.
For each element of the image, surjectivity supplies a rational-point
representative; the published descent formula identifies that evaluation
with evaluation at the representative, a continuous map on the original
character space. This proves continuity in the compact-open topology, since
the discrete-domain homomorphism embedding carries exactly that topology.
No compact lifting or continuous choice of representatives is assumed.

`rationalUnitaryUnramifiedEquiv` restricts the same equivalence to the norm-one
characters. The published pullback norm-one criterion gives the forward
membership condition, and evaluation on representatives gives the inverse
condition. One inverse law uses the original equivalence; the other inverse law
uses the descent formula on representatives, and multiplication is checked
pointwise. `rationalUnitaryUnramifiedContinuousEquiv` proves continuity of
this restriction and its inverse by the corresponding subtype topologies.

The canonical section assumes an actual affine group scheme whose structure
morphism is locally of finite type, over an arbitrary nonarchimedean local
field with its supplied valuation and topology. The field universe is
arbitrary, and neither characteristic zero nor reductivity is required.
Every rational-point space uses exactly `rationalPointTopology F G.X`.
The published `continuous_rationalValuationImageProjection` discharges the
generic continuity premise. Thus
`rationalCanonicalImageUnramifiedContinuousEquiv` extends exactly the published
`rationalCanonicalImageUnramifiedEquiv`, with no extra topology assumption.
Its forward and inverse evaluation formulas are the original formulas.

`rationalCanonicalUnitaryImageUnramifiedContinuousEquiv` composes the published
circle-dual/norm-one comparison with the norm-one restriction above. Its
evaluation formula is the ordinary inclusion of circle values into complex
units, evaluated after the actual image projection.
`compactSpace_rationalUnitaryUnramifiedCharacters` transports the compactness
of the Pontryagin dual of this discrete image to the existing intersection
subgroup of continuous characters on actual rational points.

These conclusions concern the compact-open topology and compactness of the
actual character groups. They do not prove finite rank or full rank of the
valuation image, finite-dimensional torus or Lie group structure, the
finite-kernel split-center restriction, a normalized Haar measure, second
countability of rational points, or a Plancherel theorem. The sources'
remaining algebraic, structural, representation and measure assertions
remain separate obligations.

Local instances use explicit module-specific names to prevent generated-name
collisions under joint imports. Their types, bodies and local scope are
unchanged.
