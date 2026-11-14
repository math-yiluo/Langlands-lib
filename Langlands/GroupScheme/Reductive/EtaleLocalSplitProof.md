# Reductive group schemes split étale-locally on the base

Worker 587, with the root-line contribution of Worker 634.

`Langlands.GroupScheme.etaleLocalSplitReductive` proves exactly the published
`Langlands.GroupScheme.EtaleLocalSplitReductiveStatement.{u}` for every universe
`u`. It adds no hypotheses and leaves the target and its imports unchanged.
For each point of any base scheme, it constructs an affine étale neighbourhood,
a closed coordinate split torus maximal on every residue fibre, one finite
reduced coordinate root datum on every supplied field algebra, and linear
isomorphisms from the actual relative root weight spaces to the coefficient
ring.

## Implemented proof

First, `exists_etale_affine_split_maximalTorus` supplies an affine étale
neighbourhood `f : Spec R → S`, a point `p` above the chosen base point, and a
closed coordinate split torus `i` in `G' = f*G` that is maximal on every residue
fibre. Reductivity is preserved by this base change, so `G'` is smooth and
affine.

Next, `exists_open_coordinateRootDatum` supplies a finite root index type `J`,
a reduced root datum `P` on the full coordinate lattices, and an open
neighbourhood `U` of `p`. Every root weight has rank one at `p`; moreover, for
every supplied field algebra whose point lies in `U`, the field realization of
this same `P` is the actual full root datum of the torus inclusion. This uses
the published neighbourhood construction, including its constancy of coroots
and its normalizer-reflection witnesses.

The published `splitTorus.exists_principal_exponentWeightLines` applies to the
finite family of actual weight modules indexed by `P.root`. It gives one
element `r` outside `p`, with `D(r)` contained in `U`, and linear isomorphisms
from all the actual root weight modules after base change to
`A = Localization.Away r` to `A`. The freeness here concerns the actual
relative Lie weight modules, rather than only their field fibres.

The helper `fibrewiseRootDatumOf_principalRestriction` proves that the same full
`P` is fibrewise valid over `A`. Given any supplied `A`-algebra field `k`, it
installs the composite `R`-algebra structure and its scalar tower. The image
of `Spec A → Spec R` is `D(r)`, so the field point lies in `U`. The
neighbourhood datum therefore applies to this particular `R`-algebra structure.
`IsRootDatumOf.baseChangeHom_scalarTower` transfers that datum from the direct
field pullback to the successive pullback. Finiteness and reducedness are
retained. This argument includes every supplied field algebra in the target;
it does not restrict the quantifier to residue fields or algebraically closed
fields. The helper allows a separate root-index universe `v`.

Finally, write `a : Spec A → Spec R`. Base change preserves closedness and
fibrewise maximality of the coordinate torus. The actual ambient isomorphism
`(baseChangeCompIso f a G).symm` identifies `a*(f*G)` with `(a ≫ f)*G`.
The proof transports the inclusion, its closedness, its fibrewise maximality,
and the full datum through this isomorphism. Each free-line isomorphism is
composed with `splitTorus.exponentWeightAmbientEquiv` in the required direction
to give a linear isomorphism for the final actual weight space. The map `a` is
an open immersion, so `a ≫ f` is étale. Since `r` is outside `p`, the image
formula for localization lifts `p` to `Spec A`, giving a point above the
original chosen point of `S`.

All rings, the coordinate type, and the root index type in the final construction
are in `u`; localization does not enlarge that universe. The empty base is
handled by the universal quantification over its points.

## Source and provenance

The result is the Library formulation of Brian Conrad, *Reductive group
schemes* (2014), Lemma 5.1.3 and its proof, printed/PDF pp. 136–137, with
splitness as in Definition 5.1.1, p. 136. The source is registered as
`conrad-2014-reductive-group-schemes`; its readable file is
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.

Conrad first obtains and splits a maximal torus étale-locally, then shrinks
Zariski-locally to make weights, rank-one root spaces, and coroots constant.
This implementation follows that local strategy through the published affine
torus and root-datum neighbourhood theorems, then performs one simultaneous
principal localization for the free root lines. The scalar-tower helper and
ambient transport are internal comparisons required by the Library's actual
pullback and weight-space constructions. The exact target's source comparison,
including the full root-datum formulation, is recorded in
[EtaleLocalSplitStatement](EtaleLocalSplitStatement.md).
