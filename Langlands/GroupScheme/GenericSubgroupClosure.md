# Schematic closure of a generic subgroup

Worker 671. This module constructs the schematic closure of a closed subgroup
of the generic fibre of an arbitrary group scheme over a Dedekind domain. All
constructions and results are in
`Langlands.GroupScheme.GenericSubgroupClosure`, in an arbitrary universe `u`.

## Data and construction

Let `R` be a Dedekind domain, let `K` be its specified fraction field, and put
`β = Spec.algebraMap R K`. The inputs are an actual group scheme
`G : GroupScheme (Spec R)`, a group scheme `H : GroupScheme (Spec K)`, and a
homomorphism `j : H ⟶ (baseChange β).obj G` whose underlying scheme morphism is
a closed immersion. There is no affineness, finite type, separatedness,
smoothness, connectedness or reductivity premise on `G` or `H` in this
construction.

The principal definition `closureGroup G j` is an actual group scheme over
`Spec R`. The accompanying definitions and results give:

- `closureInclusion G j : closureGroup G j ⟶ G`, whose underlying scheme
  morphism is the closed immersion `inclusionOver G j`;
- `flat_closureOver`, flatness of the structure morphism of this group;
- `genericToClosureIso G j : H ≅ (baseChange β).obj (closureGroup G j)`;
- `genericToClosureIso_hom_comp`, the identity
  `genericToClosureIso.hom ≫ (baseChange β).map closureInclusion = j`;
- `inclusionOver_ker`, equality of the kernel ideal sheaves of the closed
  inclusion and the original generic map to `G`.

Here `genericOver G j` is the pullback-adjunction transpose of `j`, with
underlying scheme map `j.hom.hom.left ≫ pullback.fst G.X.hom β`.
`closureOver G j` is its scheme-theoretic image over `Spec R`,
`inclusionOver` is `imageι`, and `projectionOver` is `toImage`.
`projectionOver_fac` gives their factorization of `genericOver`.
The equality of kernel ideal sheaves states the schematic-closure property,
rather than just a factorization through some larger closed subscheme.

The structure morphism of `closureOver` inherits `IsAffineHom`,
`LocallyOfFiniteType`, `QuasiCompact` and `IsSeparated` whenever the structure
morphism of `G` has the respective property, by composition with the closed
immersion. Thus a separated finite type ambient group has a flat, separated,
finite type closure. These inheritance instances do not impose their
additional hypotheses on the principal construction. The raw image and its
inclusion are defined even without the Dedekind-domain or closed-subgroup
hypotheses; the group structure and the stated generic identification use
the data above.

## Provenance

This is a derived construction motivated by Conrad, *Reductive group
schemes* (2014), proof of Theorem 5.3.5, printed/PDF p.166. That proof replaces
a possibly nonaffine target over a discrete valuation ring by the schematic
closure of the generic-fibre image, obtaining a flat finite type group before
applying Raynaud's criterion. The registered source is
`conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.

The implemented construction adapts the published Library module
`Langlands.GroupScheme.IntegralModel.SchematicClosureProof`, especially
`IntegralModel.SchematicClosureConstruction.flat_of_appTop_injective` and
its restrictions of the group operations. That module already treats
Dedekind domains internally but assumes an affine finite type ambient
integral model. This module removes the affine and finite type assumptions
on the ambient group, and takes the subgroup of its actual generic fibre as
input directly. Its Dedekind-domain scope is an internal strengthening of
the discrete-valuation-ring application in Conrad, justified by the
flatness argument below. It does not assert that Conrad states this exact
construction or this larger scope.

## Implemented proof

`flat_of_generic_dominance` is the new flatness input. Suppose a scheme
`X → Spec R` receives a quasi-compact schematically dominant morphism
`t : Y → X` from a scheme over `Spec K`, compatibly with the structure maps.
Pull `t` back along every member of the affine cover of `X`. Flat base
change along these open immersions preserves schematic dominance and
quasi-compactness, so the resulting map injects the sections on each affine
chart into the sections of its inverse image. Every nonzero element of `R`
becomes a unit in the latter ring, since the inverse image is over `K`.
The imported `flat_of_appTop_injective` proves that the affine chart is flat:
its sections are torsion-free over `R`, hence flat over a Dedekind domain.
Flatness is local on the source, which proves flatness of `X → Spec R`.

For the image construction, `genericOver` is quasi-compact: it is a closed
immersion followed by the base change of the affine morphism `β`.
Its projection onto the image is quasi-compact and schematically dominant.
The latter fact uses
`Langlands.AlgebraicGeometry.toImage_schemeTheoreticallyDominant` from
`Picard.GenericSectionSchematicClosure`, which applies to arbitrary targets.
Applying the new chartwise flatness lemma to this projection proves
`flat_closureOver`.

The three operations of `G` restrict to the image by
`exists_over_factor_of_schematic_precomp` from the Library's
`ImageGenerationDominant`. For the unit, precompose with the schematically
dominant map `β`. For the inverse, precompose with `projectionOver`.
For multiplication, precompose with the tensor square of `projectionOver`,
after the comparison from the product over `Spec K` to the product over
`Spec R`. This comparison is an isomorphism because `β` is a monomorphism.
The tensor square of the projection is schematically dominant by
`ImageGeneration.isSchemeTheoreticallyDominant_tensorHom`: both its source
and target are flat over `Spec R`. The source is a scheme over the field
`K` followed by the flat localization map `β`; the target is flat by the
preceding paragraph. Naturality and multiplicativity of
`baseChangePointsEquiv` turn the three factorization equations into the
group-homomorphism identities for `j`.

`GroupObjectDescent.grpObjOfMono` equips `closureOver` with the resulting
group structure; its companion theorem makes `inclusionOver` a
homomorphism. This defines `closureGroup` and `closureInclusion`.

Finally, transpose `projectionOver` to obtain `genericToClosureOver`.
Its composite with the base-changed inclusion is `j`, by the point
adjunction. It is a homomorphism by cancellation of that monomorphic
inclusion. It is a closed immersion because the composite is a closed
immersion and the inclusion is separated. It is also schematically
dominant: the square with `projectionOver`, the generic-fibre projection
and the identity on `H` is cartesian, and the generic-fibre projection is
flat. A schematically dominant closed immersion has zero kernel ideal and
is therefore an isomorphism. `genericToClosureIso` packages this as a
group-scheme isomorphism. `inclusionOver_ker` is Mathlib's kernel equality
for `ker.subschemeι`.

## Scope of the contribution

This construction supplies the schematic-closure step for the
reductive-monomorphism argument. It proves neither Raynaud's affineness
criterion nor the reductive-monomorphism closed-immersion theorem. It does
not assert smoothness, reductivity or connectedness of the closure. The
published target statements and their imports are unchanged.
