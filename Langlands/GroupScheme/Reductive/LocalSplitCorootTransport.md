# Transport of coordinate normalizing points between field fibres

Authors: Worker 239.

This module reduces
[`LocalSplitFibrewiseRootDatumExistenceStatement`](LocalSplitRootDatumExistenceStatement.md)
to two inputs that it does not prove:

1. the field root-datum existence theorem
   [`RootDatumExistenceStatement`](RootDatumStatement.md);
2. the lifting property of flat schemes over a local ring,
   `LocalSplitCorootTransport.FlatClosedPointLiftProperty`, defined here.

The final theorem `localSplitFibrewiseRootDatumExistence_of_rootDatumExistence`
takes both as hypotheses. The module does not prove the local statement itself,
and it adds no axioms. Along the way it defines a linear-algebra construction,
`Langlands.LinearAlgebra.rootDatumEquivOfFiniteOrderReflections`, which may be
used independently.

The main problem is that the coroots must be constant. Pairings and root ranges
of the field-fibre root data agree already by published results
(`CoordinateRootDatum.pairing_eq_of_fields`, `rootRange_eq_of_fields`). Here
the coroots are compared without an integral representation, unlike the
published `CoordinateRootDatum.equivOfRepresentation`. A residue-field Weyl
reflection is spread to every field fibre through the smooth transporter
scheme. On each fibre it then lies in a finite Weyl image together with that
fibre's own reflection.

## Normalizing points as transporters

Throughout, `IsNormalizingPoint i n σ` means
`i ≫ (G.innerIso n).hom = groupHom σ.hom ≫ i`. The transporter relation
`PointwiseSchemeAction.IsTransporter i₁ i₂ g` says that
`i₁(t) · g = g · i₂(t)` for all points `t` of the source after any base change.

- `IsNormalizingPoint.of_isTransporter` and `isNormalizingPoint_iff_isTransporter`:
  a base point `n` normalizes `i` through `σ` exactly when it transports
  `groupHom σ.hom ≫ i` to `i`. One direction is published as
  `IsNormalizingPoint.isTransporter`. The converse evaluates the transporter
  relation at the identity point of `T` over `T.X`.
- `PointwiseSchemeAction.isTransporter_precomp_iso_iff`: precomposing both
  homomorphisms with an isomorphism `e : H' ≅ H` does not change the
  transporter relation.

## Exponent automorphisms of the coordinate split torus

For an integral automorphism `C` of `I → ℤ`, the published
`splitTorus.exponentCommIso S I C` is the torus automorphism induced by `C`.

- `splitTorus.exponentCharacter_single`: the fixed-exponent character of the
  basis vector `Pi.single j 1` is the coordinate projection `proj S I j`.
- `splitTorus.eq_exponentCommIso_symm`: suppose an automorphism `σ` of the
  split torus acts on fixed-exponent characters by `C`, that is
  `characterAut σ (exponentCharacter m) = exponentCharacter (C m)` for all `m`.
  Then `σ = (exponentCommIso S I C).symm`. The proof compares `σ.inv` with
  `(exponentCommIso S I C).hom` on the coordinate projections.
- `splitTorus.characterAut_exponentCommIso_symm`: `(exponentCommIso S I C).symm`
  acts on fixed-exponent characters by `C`.

## Realized coordinate automorphisms

Fix a commutative ring `R`, a finite type `I`, a group scheme `G` over
`Spec R`, a homomorphism `i : splitTorus (Spec R) I ⟶ G` and an integral
automorphism `C` of `I → ℤ`.

- `exponentIso_inv_comp_baseChangeHom` and `isTransporter_baseChangeHom_iff`:
  the twisted homomorphism `(exponentIso C).inv ≫ i` commutes with base change
  to an `R`-algebra `K`. A point `n` of the base change of `G` to `K`
  transports the twisted coordinate homomorphism to
  `splitTorus.baseChangeHom G I i` exactly when the corresponding point of `G`,
  under the published `baseChangePointsEquiv`, transports
  `(exponentIso C).inv ≫ i` to `i`.
- `IsRealizedAt I G i C K` (a `Prop`-valued definition): some `K`-point
  `g : Spec K ⟶ G` over `Spec R` transports `(exponentIso C).inv ≫ i` to `i`.
  The auxiliary `overComparison K` and `overComparisonInv K` are the identity
  morphisms between the two descriptions of `Spec K` as an object over
  `Spec R`.
- `isRealizedAt_iff`: for a field `K` over `R`, `C` is realized at `K` exactly
  when some `K`-rational point of the fibre `G_K` normalizes the coordinate
  torus `splitTorus.baseChangeHom G I i` through
  `(exponentCommIso C).symm`.
- `IsRealizedAt.restrict`: a realization at `l` gives a realization at every
  `l`-algebra `L` with `R → l → L` a scalar tower. The proof composes the point
  with `Spec L → Spec l`.

## The flat lifting property

`FlatClosedPointLiftProperty.{u}` is the following proposition, quantified over
universe `u`. Let `R : Type u` be a commutative local ring, `X` a scheme,
`f : X ⟶ Spec R` a flat morphism and `x` a point of `X` with
`f x = IsLocalRing.closedPoint R`. Then for every field `l : Type u` with an
`R`-algebra structure there are a field `L : Type u`, an `l`-algebra structure
on `L` and a morphism `g : Spec L ⟶ X` with
`g ≫ f = Spec(l → L) ≫ Spec(R → l)`.

This is the usual consequence of going down for flat morphisms. The image of
`Spec l` is a generalization of the closed point, so it is the image of some
generalization `x'` of `x`. A field quotient of `κ(x') ⊗ l` over the residue
field of that image point then gives `L`. This module only defines the
proposition and uses it as a hypothesis; it proves no part of it. A separate
contribution proves it, and this module does not import that contribution.

## Spreading a residue-field realization

`IsRealizedAt.exists_extension` assumes that `R` is local, that `G` is affine
and smooth over `Spec R`, and `FlatClosedPointLiftProperty`. If `C` is
realized at the residue field of `R`, then for every field `l` over `R` there
is a field `L` over `l`, with compatible `R`-algebra structure, at which `C`
is realized.

Proof. Transport `(exponentIso C).inv ≫ i` and `i` along the published
identification `Diagonalizable.splitIso` of the diagonalizable group on
`I → ℤ` with the split torus. This gives `j₁` and `j₂`; by
`isTransporter_precomp_iso_iff` this changes no transporter relation. Then:

- The residue-field point factors through the published relative transporter
  scheme `relativeTransporterScheme j₁ j₂` (`exists_relativeTransporter_factor_iff`).
  The resulting point `y` lies over the closed point of `Spec R`.
- The transporter scheme is smooth over `Spec R` (`smooth_relativeTransporterScheme`),
  hence flat. The lifting property gives `L` and a point `Spec L ⟶`
  transporter scheme over `Spec l ⟶ Spec R`.
- Composing with `relativeTransporterHom j₁ j₂`, which satisfies the
  transporter relation (`relativeTransporterHom_isTransporter`), gives the
  required `L`-point of `G`.

## Finite order on one field fibre

- `coordinateConj I K` is the group homomorphism from the automorphisms of the
  character lattice of `𝔾_m^I` over `K` to the integral automorphisms of
  `I → ℤ`, given by conjugation with the published
  `splitTorus.characterLatticeEquiv K I`.
  `coordinateConj_characterAut` shows that it sends
  `characterAut (exponentCommIso C).symm` to `C`.
- Two local instances record that the field fibre of `G` is affine, and that
  it is locally of finite type when `G` is.
- `isOfFinOrder_characterAut_mul`: let `H` be an affine group over a field `k`
  with structure morphism locally of finite type, and `j : T ⟶ H` a closed
  subgroup from a split torus. If `n₁` normalizes `j` through `σ₁` and `n₂`
  normalizes it through `σ₂`, then `characterAut σ₁ * characterAut σ₂` has
  finite order. Both factors lie in `weylImage j`, which is finite by the
  published `splitTorusWeylImageFinite`.
- `isOfFinOrder_mul_of_isRealizedAt`: let `G` be affine and locally of finite
  type over `Spec R`, and let the coordinate torus be closed on the field fibre
  `K`. If `C₁` and `C₂` are both realized at `K`, then `C₁ * C₂` has finite
  order. The proof applies `isRealizedAt_iff`, the previous lemma and
  `coordinateConj`.
- `isRealizedAt_reflection`: suppose the field realization of a coordinate
  root datum `P` on `I → ℤ` is a root datum of the coordinate torus on the
  field fibre `k` (`IsRootDatumOf`). Then each reflection `P.reflection j` is
  realized at `k`. The normalizing point supplied by `IsRootDatumOf` has
  automorphism `(exponentCommIso (P.reflection j)).symm`, by
  `eq_exponentCommIso_symm` and the published
  `fieldRealization_reflection_exponentCharacter`.

## Identity-lattice equivalences from finite-order reflection products

In namespace `Langlands.LinearAlgebra`, let `P : RootDatum J M N` and
`Q : RootDatum J' M N` be root data on the same additive groups. The index
types `J` and `J'` are arbitrary, with independent universes.

- `coroot_eq_of_isOfFinOrder_mul`: assume `P.toLinearMap = Q.toLinearMap`,
  `P.root j = Q.root j'`, and that `P.reflection j * Q.reflection j'` has
  finite order. Then `P.coroot j = Q.coroot j'`. The proof applies the
  published `eq_functional_of_finiteOrder_reflections` to the two functionals
  `⟨-, P.coroot j⟩` and `⟨-, Q.coroot j'⟩` on `M`, which both take the value 2
  at the common root. Perfectness of the pairing then identifies the coroots.
  This is the finite-order form of the published
  `coroot_eq_of_common_generators`, whose proof it follows. That lemma derives
  the finite order from a common finite generating set.
- `rootDatumEquivOfFiniteOrderReflections` (a definition): assume equal
  pairings, equal root ranges, and finite order of
  `P.reflection j * Q.reflection j'` whenever `P.root j = Q.root j'`. It
  constructs a full `RootPairing.Equiv P Q` whose weight map and coweight map
  are both `LinearMap.id`. Its index equivalence is the published
  `rootIndexEquivOfRangeEq`, so corresponding roots are equal. Corresponding
  coroots are equal by `coroot_eq_of_isOfFinOrder_mul`. The simp lemmas
  `rootDatumEquivOfFiniteOrderReflections_weightMap` and `_coweightMap` record
  that both lattice maps are the identity. There is no finiteness,
  reducedness or generation hypothesis.

## Assembly over a local base

Let `R` be local and `G` smooth and affine over `Spec R`.

- `isRootDatumOf_of_residueField`: assume `FlatClosedPointLiftProperty` and
  that the coordinate torus is a closed subgroup on every field fibre. Suppose
  the field realization of `P : RootDatum J (I → ℤ) (I → ℤ)` is a root datum of
  the torus on the residue-field fibre. Suppose also that the field realization
  of some `Q : RootDatum J' (I → ℤ) (I → ℤ)` is a root datum of the torus on
  the fibre over a field `l`. Then the field realization of `P` is also a root
  datum of the torus on the fibre over `l`.

  Proof. Pairings and root ranges of `Q` and `P` agree
  (`pairing_eq_of_fields`, `rootRange_eq_of_fields`). Suppose
  `Q.root j' = P.root j`. Then `P.reflection j` is realized at the residue
  field (`isRealizedAt_reflection`). By `IsRealizedAt.exists_extension` it is
  realized at some field `L` over `l`. `Q.reflection j'` is realized at `l`,
  hence at `L` (`IsRealizedAt.restrict`). By
  `isOfFinOrder_mul_of_isRealizedAt` on the fibre over `L`, their product has
  finite order. `rootDatumEquivOfFiniteOrderReflections Q P` then gives an
  identity-lattice equivalence. The published
  `CoordinateRootDatum.isRootDatumOf_of_identityEquiv` transfers the
  root-datum property from `Q` to `P` on the fibre over `l`.

- `localSplitFibrewiseRootDatumExistence_of_rootDatumExistence`: assuming
  `RootDatumExistenceStatement.{u}` and
  `FlatClosedPointLiftProperty.{u}`,
  `LocalSplitFibrewiseRootDatumExistenceStatement.{u}` holds.

  Proof. Given the data of the local statement, `IsReductive G` gives
  smoothness. The published `splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise`
  makes the coordinate torus a maximal torus of every field fibre `G_k`.
  `IsReductive.isConnectedReductive_algebraMap` makes `G_k` connected
  reductive. The field theorem then gives a finite reduced root datum on the
  actual lattices of the residue-field fibre. Its coordinate expression
  `CoordinateRootDatum.ofField` is the required `P`: it is reduced by
  `ofField_isReduced`, and it is realized on the residue-field fibre by
  `isRootDatumOf_fieldRealization_ofField`. For an arbitrary field `l` over
  `R`, the field theorem gives a datum `Q` on the fibre over `l`, and
  `isRootDatumOf_of_residueField` shows that `P` is realized there too.

## Provenance

The construction and all proofs are internal. They are a route to the local
statement chosen for this Library, not a translation of a proof in the
literature; the provenance of the target proposition is described in
[`LocalSplitRootDatumExistenceStatement.md`](LocalSplitRootDatumExistenceStatement.md).
`FlatClosedPointLiftProperty` is a hypothesis introduced here to separate a
general fact about flat morphisms from the group-scheme argument. It is a
standard consequence of going down for flat ring maps, but the module neither
cites nor proves it. `rootDatumEquivOfFiniteOrderReflections` is the
finite-order variant of the published `rootDatumEquivOfCommonGenerators`. Only
named published Library results and Mathlib are used.
