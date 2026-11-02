# Extending an étale equivalence relation from an open by the identity

Let `E` be an étale equivalence relation, and let `ι : E.U ⟶ V` be an
open immersion. This module constructs an étale equivalence relation on `V`
which agrees with `E` over this open and has only identity arrows elsewhere.
The arrow scheme is the actual scheme pushout

`R⁺ = V ⊔_{E.U} E.R`,

where the two maps out of `E.U` are `ι` and the identity section `E.unit`.
Both are open immersions. All schemes and test schemes have an arbitrary
universe `u`. No affineness, separation, quasi-compactness, quotient
representability, or Noetherian hypothesis is imposed.

The namespace of the extension declarations below is
`Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.OpenExtension`.
The principal definition is `relation E ι`. Its restriction to `E.U`
is identified with `E` by the proved `isCartesianHom` assertion.
This is a helper for the pushout step of absolute Noetherian
approximation. It does not prove the FL statement or assert affineness of
the new arrow scheme.

## Provenance

This is internal derived content. The mathematical ingredients are the
existing structural maps of an étale equivalence relation, Mathlib's
colimits of locally directed diagrams of open immersions, and the sheaf
property for morphisms of schemes on open covers.

The application is the pushout in the proof of Stacks Project,
Proposition 70.8.1, Tag 07SU, in the registered source
`stacks-noetherian-approximation-2026-11-01`, file `07SU.html`, at the
paragraph beginning with the application of Limits, Lemma 32.5.3.
There the old relation is `W_i ×_{U_i} W_i`, the enlarged diagonal is
`V_i`, and the common open is `W_i`. The present construction applies
to any étale equivalence relation on an open scheme. Its local proofs
justify the relation assertion in that construction directly, without
assuming absolute approximation or forming a quotient algebraic space.
The cartesian inclusion proved here is restriction along the original
open; it does not assert the later comparison between different
approximation levels.

## Gluing and the arrow charts

- The imported `Langlands.AlgebraicGeometry.exists_lift_of_openCover` from
  [the generic gluing module](Morphisms/OpenCoverLift.md) says that local lifts of a scheme morphism
  through a monomorphism glue to a global lift. After choosing local
  lifts, their composites agree on overlaps; cancellation of the
  monomorphism makes the lifts themselves agree. `glueMorphisms`
  and cover extensionality finish the proof.
- `span_isOpenImmersion` establishes that every morphism of the
  span diagram `span ι E.unit` is an open immersion. Cases on its
  morphisms reduce this to identities, `ι`, and `E.unit`.
- `arrows` is the pushout scheme. `unit` and `inclusion` are its
  inclusions from `V` and `E.R`. The two following instances prove
  that these inclusions are open immersions using Mathlib's
  locally directed gluing construction.
- `unit_inclusion` is the pushout equation
  `E.unit ≫ inclusion E ι = ι ≫ unit E ι`.
- `cover` is a binary open cover of `arrows E ι`, indexed by
  `WalkingPair`, with chart schemes `V` and `E.R` and the preceding
  two inclusion maps. Joint surjectivity of the colimit inclusions
  proves coverage. A point from the common-open vertex also lies
  in the `V` chart by the colimit compatibility equation.

## Endpoints and uniqueness

- `t` and `s` are pushout descents of the identity on `V` and the
  morphisms `E.t ≫ ι` and `E.s ≫ ι`. The unit laws of `E` give the
  required compatibility.
- `unit_t`, `unit_s`, `inclusion_t`, and `inclusion_s` compute these
  endpoints on the two charts. Reassociated forms are generated.
- `chart_hom_ext` proves that two maps into arbitrary charts have
  the same composite into the pushout whenever both endpoints agree.
  There are four chart pairs. On the diagonal chart this follows
  from its target endpoint. On the relation chart it follows from
  `E.hom_ext` after cancelling `ι`. In either mixed case the arrow
  in `E.R` has equal endpoints, hence equals the corresponding
  unit arrow; the pushout equation then identifies the maps.
- `hom_ext` proves endpoint uniqueness for arbitrary maps into
  `arrows E ι`. Pull back `cover` along the first map, and then
  along the second map on each resulting chart. The pullback
  equations put both maps in charts, where `chart_hom_ext` applies.
  Two applications of cover extensionality give the global equality.
- `mono_pair` packages endpoint uniqueness as monicity of
  `prod.lift (t E ι) (s E ι)`. Composing a cancellation equation
  with the two product projections reduces it to `hom_ext`.

## Equivalence relation operations

- `inverse` is a pushout descent which fixes the enlarged diagonal
  and applies `E.inverse` on the old arrow chart. The identity
  `E.unit ≫ E.inverse = E.unit`, proved using `E.hom_ext`, supplies
  compatibility.
- `unit_inverse` and `inclusion_inverse` compute the reversal on
  the two charts. `inverse_t` and `inverse_s` show that reversal
  exchanges the endpoints, by pushout extensionality.
- `exists_endpoints_of_openCover` glues an arrow with prescribed
  endpoints when such an arrow exists on an open cover. It applies
  `exists_lift_of_openCover` to the monic endpoint map and the
  product of the two prescribed endpoints.
- `chart_trans` proves transitivity for arrows lying in two
  specified charts. If both are diagonal arrows, their endpoints
  coincide. If just one is diagonal, the other arrow is the
  composite. For two old arrows, cancellation of `ι` gives their
  composability in `E`, and `E.compose` gives the composite.
- `trans` proves global transitivity. Pull back the binary cover
  along the first arrow and then the second, use `chart_trans`,
  and apply `exists_endpoints_of_openCover` twice. Thus the proof
  constructs actual scheme morphisms and retains their endpoint
  equations.
- `etale_t` and `etale_s` are instances proving that the extended
  endpoints are étale. Étaleness is local at the source. On the
  binary cover the maps are respectively identities and composites
  of the old étale endpoints with the open immersion `ι`.
- `relation` packages `V`, `arrows`, the endpoints, monicity, and
  these operations as an `EtaleEquivalenceRelation`. Reflexivity
  uses `unit`; symmetry uses `inverse`; transitivity uses `trans`.

## Cartesian restriction

- `exists_lift_of_source` proves that an arrow `a : T ⟶ arrows E ι`
  with source `b ≫ ι`, for `b : T ⟶ E.U`, comes uniquely from an
  old arrow, with source `b`. Existence is local on the pullback
  of the binary cover along `a`. On the old arrow chart there is
  already a lift. On the diagonal chart the source equation
  factors the diagonal point through `ι`, and the lift is the
  corresponding old unit. The lifts glue through the monic open
  inclusion. Cancelling `ι` proves the old source equation.
- `isPullback_source` constructs the limiting pullback cone from
  these lifts. Uniqueness follows by cancellation of `inclusion`.
  Its square has top map `inclusion E ι`, left map `E.s`, right
  map `s E ι`, and bottom map `ι`.
- `isCartesianHom` combines this square with `inclusion_t`.
  It proves exactly
  `IsCartesianHom E (relation E ι) ι (inclusion E ι)`.
