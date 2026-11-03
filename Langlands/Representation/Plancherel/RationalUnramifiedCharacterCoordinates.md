# Finite coordinates on actual unramified characters

Author: Worker 200.

This derived consumer equips the actual unramified complex characters and
their unitary subgroup with finite coordinates, using their existing
compact-open topologies. It composes the valuation-image comparison with
basis coordinates. The field can have any characteristic and universe;
the group is any actual connected reductive group scheme over that field.

## Sources and provenance

Renard, *Représentations des groupes réductifs p-adiques*, 9 July 2026
edition, V.2.3–V.2.4, printed pp.105–106 (PDF pp.111–112), defines the
integer valuation map `H_G`, its image `Λ(G)`, the common norm kernel,
and unramified characters. V.2.4 identifies these characters with
`Hom(Λ(G), ℂ×)` and uses finite freeness of the image to construct a
complex algebraic torus. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, I.1, printed pp.239–240 (PDF pp.5–6),
defines `G¹`, `X(G) = Hom(G/G¹, ℂ×)` with continuous homomorphisms,
and the unitary subgroup `Im X(G)`. Its normalization satisfies
`|χ(g)|_F = q^(-⟨χ,H_G(g)⟩)`. The imported valuation image uses this
positive valuation convention. Registered source:
`waldspurger-2003-plancherel`, SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

The Lean file implements a compact-open topological consequence of the
image description. Its proof composes existing continuous multiplicative
equivalences; it does not implement Renard's group-algebra spectrum
construction or Waldspurger's exponential parametrization.

## Actual objects and hypotheses

Let `F : Type u` have instances `Field F`, `ValuativeRel F`,
`TopologicalSpace F` and `IsNonarchimedeanLocalField F`. Let
`G : GroupScheme (Spec (CommRingCat.of F))`, and let
`hG : GroupScheme.IsConnectedReductive G`. No splitness, quasisplitness
or characteristic-zero premise is imposed.

The group of points is the shared `GroupScheme.rationalPoints G`.
The local point topology in the coordinate definitions is exactly
`rationalPointTopology F G.X`. The source character space is
`unramifiedCharacters (fun χ => (rationalNormCharacters G χ).toMul)`:
continuous characters into `ℂˣ` trivial on the actual common kernel
of all rational norm characters. Its unitary subgroup is the existing
`unitaryUnramifiedCharacters` for the same family. Their topologies
are the existing subspace topologies inherited from compact-open
continuous homomorphisms.

The private helper `rationalReductive_isAffine` derives affineness of
`G.X.left` from `hG.isAffineHom`. Each coordinate definition installs
this proof before elaborating `rationalPointTopology`; the same local
instances appear in the definition's result type and proof. In the
body, `hG.smooth` supplies local finite type for the imported canonical
image comparison. These are consequences of `hG`, rather than extra
mathematical hypotheses.

Write `r = rationalImageRank G`. This is the rank of the actual
valuation image, not a rank identified here with a split component.
`rationalReductiveValuationBasis G hG` is the same chosen integer
basis `rationalImageBasis G`, with its finiteness premise supplied by
the published theorem `GroupScheme.rationalCharacterLattice F G hG`.
It is indexed by `Fin r`, includes the rank-zero case, and introduces
no new choice of image or coordinates.

## Coordinate equivalences

`rationalCanonicalUnramifiedCharacterCoordinates G hG` gives

```text
unramifiedCharacters (fun χ => (rationalNormCharacters G χ).toMul)
  ≃ₜ* (Fin r → ℂˣ).
```

Its first factor is the inverse of
`rationalCanonicalImageUnramifiedContinuousEquiv G`, which descends
a character on actual rational points to the actual discrete image.
The second factor is `rationalReductiveImageCharacterCoordinates G hG`,
which evaluates that descended character on the chosen image basis.
Thus the inverse reconstructs an image character from its basis values
and pulls it back along `rationalValuationImageProjection G`.

`rationalCanonicalUnitaryUnramifiedCharacterCoordinates G hG` gives
the corresponding equivalence

```text
unitaryUnramifiedCharacters (fun χ => (rationalNormCharacters G χ).toMul)
  ≃ₜ* (Fin r → Circle).
```

It composes the inverse of
`rationalCanonicalUnitaryImageUnramifiedContinuousEquiv G` with
`rationalReductiveUnitaryImageCoordinates G hG`. The target products
have their ordinary finite product topology. Continuity,
multiplicativity and the inverse laws in both constructions follow
from the corresponding properties of the composed equivalences.

## Laurent evaluation and unitary compatibility

For a tuple `c : Fin r → ℂˣ` and an actual point `g`,
`rationalCanonicalUnramifiedCharacterCoordinates_symm_apply` proves

```text
χ_c(g) = ∏ i, c(i) ^ (b.repr (Additive.ofMul (v(g))) i),
```

where `b = rationalReductiveValuationBasis G hG` and
`v = rationalValuationImageProjection G`. The integer exponents are
the coordinates of the actual image of `g`; negative powers are
allowed. After unfolding the composition, the proof is the imported
`rationalImageCharacterOfCoordinates_apply` formula.

`rationalCanonicalUnitaryUnramifiedCharacterCoordinates_symm_apply`
proves the identical formula for a circle-valued tuple, after
including both sides in `ℂ`. It uses that same image formula and the
definition of the unitary pullback.

Finally, `rationalCanonicalUnitaryUnramifiedCharacterCoordinates_coe`
proves that forgetting a character's unitary membership and using
the complex coordinates agrees, coordinate by coordinate in `ℂ`,
with including the circle coordinates. Both constructions descend
the same function and evaluate it on the same basis, so the
implemented proof is definitional equality.

## Scope

This unit supplies finite topological multiplicative coordinates on
the actual unramified character groups in the canonical point topology.
It does not construct a character group scheme, a complex manifold
structure, the polynomial coordinate ring, or a proof that evaluation
is a regular function. The Laurent formula is a concrete input for
such later constructions.

It does not identify `r` with `dim a_G`, prove finite index in the
whole integer dual, establish restriction to a maximal split central
torus, or choose Haar measures. Twist orbits, stabilizers, orbit
measures and the representation-theoretic and Plancherel conclusions
remain separate obligations.
