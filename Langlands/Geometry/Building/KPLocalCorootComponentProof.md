# The local coroot component formula over the maximal unramified field

Module `Langlands.Geometry.Building.KPLocalCorootComponentProof`.
The theorem `Langlands.Geometry.Building.kpLocalCorootComponent` proves exactly
`KPLocalCorootComponentStatement.{u}` at arbitrary universe `u`.

For a nonarchimedean local field `F` of any characteristic, an affine group
scheme `H` over `K = UnramifiedClosure F`, supplied building data `B`, a proof
`hZ` that its whole centralizer is a torus, and any relative root `a`, the
conclusion provides an affine induced torus and a morphism to
`B.centralizerTorus hZ`. These are chosen before the apartment point and root
elements. For every factorization of the specified opposite-root commutator
with positive finite depth sum `r`, its centralizer component is the image of
a rational point `c` of that torus, and every character over
`SeparableClosure F` satisfies the required bound
`r ≤ algebraicExtensionAddValuation F (SeparableClosure F) (χ(c) - 1)`.
The theorem retains all hypotheses and quantifiers of the published statement.

The Lean proof introduces the statement's field, instances, group scheme,
building data, torus-centralizer hypothesis and relative root. It specializes
the published theorem `quasiSplitValuedRankOneCoordinates` from
`QuasiSplitValuedRankOneCoordinatesProof` to `F`, `H`, `B` and `hZ`. This
supplies coherent valued SL2 or SU3 coordinates for every indivisible root,
including the common apartment origin, the original-base-normalized depth
identities, and the actual rank-one homomorphism and coroot morphism.

The proof then applies
`inducedCorootComponentProperty_of_valuedRankOneCoordinates` from
`RankOneCorootReduction` to these coordinates and `a`. Its conclusion unfolds
to the complete existential conclusion of the target. That published reduction
handles arbitrary roots by expressing a positive root as an indivisible root
or its double using actual opposite factor pairs. It uses the SL2, ordinary
SU3 or doubled SU3 coroot result as appropriate. The source is a finite
separable Weil restriction of the multiplicative group; its affine, torus
and induced-torus properties, actual centralizer image and bound for every
geometric character are supplied by the reduction's published dependencies.
In particular, divisible and multipliable roots are included.

This proof is an internal composition of those two published theorems.
The coordinate-existence theorem discharges the coordinate-provider input
of the reduction; no additional premise is assumed. The proof changes no
statement or imported pair and adds no characteristic restriction.
The source provenance of the extracted KP Proposition 7.1.1 formula is
documented in `KPLocalCorootComponentStatement.md`; the algebraic,
valuation, matrix and geometric-character arguments are documented in
the paired Markdown of the imported results. This module cites no
additional literature.
