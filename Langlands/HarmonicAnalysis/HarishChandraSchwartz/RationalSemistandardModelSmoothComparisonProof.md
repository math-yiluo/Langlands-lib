# Smoothness of the semistandard model comparison

`Langlands.HarishChandraSchwartz.RationalSemistandard.modelSmoothComparison`
proves `ModelSmoothComparisonStatement.{u, uV}` from
`RationalSemistandardOrbitSections`. It works for every intrinsic index,
two supplied Levi models, two supplied compact pictures, an actual
irreducible admissible representation, and a raw orbit section. The field
and representation-carrier universes are independent. The theorem retains
the statement's local-field, affine and locally finite type assumptions.

## Canonical coordinates on the literal Levi

The proof lifts each vector of `rationalReductiveValuationBasis` to a
rational point of the model by
`rationalValuationImageProjection_surjective`, then carries that point to
the literal Levi by `LeviModel.pointHomeomorph`. Unfolding the inverse
of `LeviModel.unitaryCoordinates` reconstructs the character at the
valuation image of this point. By `rationalImageCharacterOfCoordinates_basis`,
evaluation at this lift recovers the corresponding circle coordinate.

For models \(m\) and \(n\), `unitaryCoordinateChange` takes a tuple in
the \(n\) chart, reconstructs the actual character, transports it by
`n.unitaryCharactersEquiv m`, and reads its \(m\) coordinates. The
transport fixes the underlying continuous character by the definition
of `LeviModel.unitaryCharactersEquiv`, as recorded by
`LeviModel.unitaryCharactersEquiv_val`. Each output coordinate is
therefore evaluation at its lifted Levi point. Applying
`LeviModel.unitaryCoordinates_hasLaurent` in the \(n\) chart at those
points gives the integer exponents of a `finiteTorusMonomial`. The
pointwise equality uses the circle inclusion into \(\mathbb C\), which
commutes with the finite product.

## Coefficients and compact pictures

For a fixed compact picture, `compactOrbitValue` evaluates the raw
section at the actual twist and applies `productInducedCompactEquiv`.
The definitions of `LeviModel.representativeModelEquiv` and
`LeviModel.orbitSectionsModelEquiv` keep the actual inducing object and
its coefficient value. Together with the equality of actual characters
this makes `compactOrbitValue_modelChange` a reflexive equality of the
full compact coefficient vectors. The compact family in the \(n\) chart
is thus the compact family in the \(m\) chart precomposed with the
coordinate change. `mem_finiteSmoothFamilies_comp_monomial` transports
the finite scalar-smooth sums with their fixed coefficient vectors.
`LeviModel.orbitSectionsModelEquiv_coherent_iff` transports coherence
under every actual inducing equivalence, including the full tensor
action of self-twists.

In a fixed Levi model, `productInducedSmoothOrbitSections_le_changeCompact`
compares the two supplied compact pictures. The parabolic decomposition
and closedness are provided by `decomposition`, `isClosed_radical`
and `isClosed_parabolic`. Each `CompactData` supplies its compact open
subgroup, compactness and factorization. The proof uses projection
continuity from the starting picture and the model's continuous norms
and Laurent evaluations from `LeviModel.continuous_normCharacters`
and `LeviModel.unitaryCoordinates_hasLaurent`. From the \(m,d\) side
the proof changes models in \(d\), then changes compact pictures in
\(n\). From the \(n,e\) side it changes models back in \(e\), recovers
the original section using `LeviModel.orbitSectionsModelEquiv_trans`
and `LeviModel.orbitSectionsModelEquiv_refl`, and changes compact
pictures in \(m\).

## Source and provenance

This is a comparison derived from the Library's rational-point
realization. Waldspurger's I.1, printed pp. 238–239 (PDF pp. 4–5),
supplies the semistandard setting and the unitary character parameter
space. VI.1, printed pp. 295–296 (PDF pp. 61–62), defines smoothness
using restriction to a compact picture and includes the self-twist
action on tensor coefficients. The Lean proof implements the comparison
using the two canonical chart reconstructions and the published
compact-change theorem. The registered source is
`waldspurger-2003-plancherel`, SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
[J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques (d'après Harish-Chandra)* (2003)](https://doi.org/10.1017/S1474748003000082).
