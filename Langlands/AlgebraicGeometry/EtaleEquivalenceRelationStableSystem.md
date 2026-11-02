# Cofiltered systems of stable finite levels

Author: Worker 706. The imported ring-groupoid and stable-subalgebra constructions
are by Worker 266.

This module supplies an inverse-system interface for the stable finitely generated
subalgebras of an algebra with a multiplicative groupoid coaction. It then applies
that interface to an actual cartesian morphism of affine étale equivalence
relations. All types and indexing categories are in an arbitrary universe `u`.

## Ring-level construction

In namespace `RingEtaleGroupoid.StableSystem`, fix a ring étale groupoid
`hE : RingEtaleGroupoid t₀` on `B₀` with relation ring `C₀`, a `B₀`-algebra
`B`, and a multiplicative coaction `θ` on `B`.

- `Index θ` is the partially ordered subtype of `B₀`-subalgebras of `B` that
  are finitely generated and stable under `θ`. `subalgebra θ` is its monotone
  inclusion into all subalgebras.
- `exists_ge` says that, when `B₀` is Noetherian, every finitely generated
  subalgebra is contained in one in `Index θ`. Apply the imported
  `RingEtaleGroupoid.exists_fg_stableSubalgebra` to a finite generating set.
  Its containment property implies containment of the generated subalgebra.
- `indexNonempty` applies this to the bottom subalgebra. `indexDirected`
  applies it to the join of two finitely generated subalgebras.
  `indexCofiltered` makes the opposite of this nonempty directed poset a
  cofiltered category. These are lemmas with the groupoid and
  multiplicativity hypotheses, not unconditional instances.
- `exhaustive` applies finite stable containment to the singleton of an
  arbitrary element of `B`, proving that the family has union `B`.
- The indexed rings have instances of `Algebra.FiniteType B₀` and, when
  `B₀` is Noetherian, `IsNoetherianRing`. These follow from the subalgebra's
  finite generation and the Hilbert basis theorem in Mathlib.
- `level hE θ hθ i` is the imported action groupoid of the restricted
  coaction: its object scheme is `Spec i.1`, its relation scheme is
  `Spec (C₀ ⊗[B₀] i.1)`. Both are affine; the object scheme is Noetherian
  if `B₀` is Noetherian. `finiteType_int` says the indexed ring is of finite
  type over `ℤ` if `B₀` is, by transitivity of finite type.
- `inclusion_equivariant` is equivariance of a subalgebra inclusion between
  two stable levels. Apply the injective tensor inclusion into `C₀ ⊗[B₀] B`
  and use the two restricted-coaction inclusion identities; the composite
  of the subalgebra inclusions is the original inclusion into `B`.
- `transition` applies `Spec` to this inclusion and its tensor product with
  `C₀`. The imported equivariant-map lemma proves that the two maps form an
  actual cartesian morphism of relations. `diagram` is the contravariant
  functor from `Index θ`: its identity and composition laws follow from
  functoriality of `Spec`, equality of subalgebra inclusions, and
  extensionality on the two tensor factors.
- `coneMorphism` applies the same construction to the inclusion into `B`.
  `cone` has point the full coaction relation on `Spec B` and those
  cartesian morphisms as legs. Naturality again follows from the tensor
  inclusions and functoriality of `Spec`.
- `isLimitObject` proves that the image of this cone under
  `EtaleEquivalenceRelation.objectFunctor` is a limit cone. It reuses the
  published proof
  `P2MW.S_AlgebraicGeometry_SubalgebraStages_nonempty_isLimit_cone.LimBC.nonempty_isLimit_specCone`
  for a nonempty directed exhaustive family of subalgebras, with precisely
  `subalgebra θ` and `exhaustive`. It asserts an object-scheme limit and
  does not assert a limit of relation schemes.

## The original affine relation

In namespace `EtaleEquivalenceRelation.IsCartesianHom`, fix
`h : IsCartesianHom E E₀ f g` with `E.U`, `E₀.U` and `E₀.R` affine. Let
`B₀ = Γ(E₀.U, ⊤)`, `C₀ = Γ(E₀.R, ⊤)`, `B = Γ(E.U, ⊤)`; the algebra
structures are given by `E₀.s.appTop` and `f.appTop`.

- `stableIndex` and `stableDiagram` are the above index and diagram for
  the actual coaction `h.coaction` and the ring form `E₀.ringEtaleGroupoid`.
  `stableIndex_isCofiltered` applies the previous cofilteredness lemma when
  `B₀` is Noetherian. The affine instances for its object and relation
  schemes, and the Noetherian instance for its object schemes, specialize
  the ring-level instances.
- `toFullStableRelation` is the cartesian morphism from `E` to its full
  coordinate-ring model. Its object map is `E.U.isoSpec.hom`; its relation
  map is `E.R.isoSpec.hom` followed by `Spec.map h.relationIso.hom`.
  Affineness of `E.R` follows from the given cartesian square. The
  imported `h.isCartesianHom_toScheme` proves cartesianness. The full
  restricted coaction is definitionally the target ring map used there.
- `stableCone` extends the ring-level cone along this morphism, so its
  point is the original relation `E`, with its actual schemes.
- `stableCone_isLimitObject` transports the ring-level object limit along
  `E.U.isoSpec`. It explicitly constructs the cone isomorphism whose
  vertex map is `E.U.isoSpec.inv`; the leg identities are the inverse-hom
  identities of this spectrum isomorphism. Thus the limit is the actual
  object scheme `E.U`.

## Provenance and limits of the result

This is an internal construction from the imported exhaustion and level
relations. The exhaustion is the affine ring form of Stacks Project Lemmas
39.15.1, 39.15.3 and 39.15.4 (Tags 07TR, 07TT and 07TU), registered in
`stacks-noetherian-approximation-2026-11-01`. The use of stable finite levels
for étale equivalence relations is motivated by Proposition 70.8.1 (Tag 07SU),
from the same registered collection. The imported modules describe their
own derivations. This module adds the ordered index, the functor, the cone
and the limit comparison; it uses no new source axiom or unproved source
statement.

The first level `E₀` and the cartesian morphism to it are inputs. The module
does not construct the first Noetherian level of an arbitrary relation,
descend a finitely presented object, or prove the full FL statement. These
are subsequent uses of this system.
