# Etale neighbourhoods realizing prescribed finite separable residue extensions

Author: Worker 1683.

`Langlands.AlgebraicGeometry.etaleResidueExtension.{u}` constructs an
actual etale neighbourhood realizing a specified finite separable extension
of a scheme's actual residue field. It implements The Stacks Project,
More on Morphisms Lemma 37.35.2, Tag 02LF, using the algebraic construction
of Algebra Lemma 10.144.3, Tag 00UD. The registered source is
`stacks-etale-residue-extensions-00UD-02LF-2026-11-05`, files `02LF.html`
and `00UD.html`, full statements and proofs.

## Constructed data and exact scalar comparison

For an arbitrary scheme `S : Scheme.{u}`, a point `s`, and a specified
field `K : Type u` equipped with a finite-dimensional separable
`S.residueField s`-algebra structure, the constructor returns
`EtaleResidueExtensionData S s K`. Its fields are

- a scheme `neighbourhood` and morphism `projection : neighbourhood → S`;
- an actual point `point` of the neighbourhood;
- an isomorphism `residueIso : neighbourhood.residueField point ≅ K`;
- etaleness of the projection and its exact equation `projection point = s`;
- the equation that `Spec.map residueIso.hom`, followed by the canonical
  residue-point morphism of the neighbourhood and its projection, equals
  `Spec.map (algebraMap (S.residueField s) K)` followed by the canonical
  residue-point morphism of `S` at `s`.

The residue isomorphism identifies the actual scheme residue field with the
specified `K`. The last equation retains the original scalar embedding
from `κ(s)` into `K`, including its action as a scheme morphism. The
construction does not merely produce an arbitrary `K`-valued point above
`s`. No Noetherian, domain, reducedness, or characteristic assumptions
are made. All scheme and field carriers share the arbitrary universe `u`.
The existence proof uses the affine witness `Spec A`. The exported
`etaleResidueExtension` chooses from a data type with no affineness field,
so it does not guarantee that its chosen neighbourhood is affine. Global
surjectivity of its projection is not required.

## Implemented proof

The existence theorem `exists_etale_residue_extension` proves these data
exist; `etaleResidueExtension` then uses classical choice to construct the
data structure. Its fields contain all the proved equations, rather than
requiring any additional lifting or comparison assumption.

Choose an affine chart `j : Spec R → S` and a point `q` mapping to `s`.
The open immersion induces an isomorphism on scheme residue fields.
Compose it with `Scheme.Spec.residueFieldIso` to obtain an isomorphism
from `S.residueField s` to `q.asIdeal.ResidueField`. Naturality of the
canonical residue-point morphisms proves that this isomorphism agrees
with the original chart map; this is the equality `hbase` in Lean.

Transport the specified scalar structure on `K` across that isomorphism.
Finite dimensionality and separability are preserved by the corresponding
field equivalence. Apply the algebraic theorem
`Langlands.CommutativeAlgebra.exists_etale_residue_extension` to obtain
an etale `R`-algebra `A`, a prime `q'` over `q`, and an isomorphism
`κ(q') ≃ K` compatible with the original map on `R`. That theorem's
companion explains the primitive-element and standard-etale construction.

Take the neighbourhood to be `Spec A` and its projection to be
`Spec A → Spec R → S`. Its first factor is etale and its second is an
open immersion, so the composite is etale. The ideal equation that `q'`
lies over `q` gives the equation on underlying points. Compose
`Scheme.Spec.residueFieldIso` for `q'` with the algebraic residue-field
equivalence to obtain the data's actual scheme residue isomorphism.

The canonical morphism from `Spec K` defined by that isomorphism equals
`Spec` of the ring map `A → κ(q') → K`. To prove this, precompose the
canonical spectrum residue-field comparison with its inverse and cancel.
The ring equation on `R`, the transported scalar maps, and `hbase` then
prove the exact scalar comparison in the data. Thus both the point and
its full residue-field structure recover the prescribed extension.

## Scope and provenance

The affine-chart reduction is the one in Tag 02LF. The algebraic proof
keeps the chosen primitive element fixed and lifts its coefficients over
a principal base localization; Tag 00UD instead scales the primitive
element to lift its coefficients directly. Both give an etale algebra
over the original ring. The construction uses only `propext`,
`Classical.choice`, and `Quot.sound`.

This unit supplies the residue-extension realization used when arranging a
split maximal torus near a point. It does not construct that maximal
torus, prove relative split-torus lifting or centralizer spreading, or
establish openness of the reductive geometric identity-component locus.
