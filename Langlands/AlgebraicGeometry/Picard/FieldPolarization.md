# Polarizations over a field via ample Mumford maps

`IsFieldPolarization` is a predicate on an actual homomorphism `lambda` from
an abelian scheme `A` over `Spec k` to its constructed dual abelian scheme.
It requires two conditions:

- `lambda` is an isogeny: its underlying scheme morphism is finite, flat and
  surjective, using the existing group-scheme predicate.
- After some field extension `k → K`, its actual scheme pullback, composed
  with the canonical Poincare-compatible comparison of dual schemes, equals
  the normalized Mumford classifier of an ample line bundle on `A_K`.

The second condition is also exposed for a scheme map as
`HasFieldAmpleMumfordPresentation`. It existentially quantifies a field `K`
in the same universe and a unital ring homomorphism `k → K`. Such a map of
fields is injective, so it is a field extension; no finiteness, separability,
or algebraic-closure hypothesis is imposed. Its scheme map is the actual
contravariant `Spec.map` of this ring homomorphism.

The line bundle and the two inverse/evaluation witnesses are quantified by
`HasAmpleMumfordAfterBaseChange`. The inverse of the unit pullback first
normalizes the line bundle; the inverse of that normalized bundle enters the
actual rigidified Mumford family. Ampleness is required of the original line
bundle on `A_K`. The equality uses the canonical dual comparison determined
by the actual base-changed Poincare family, not an arbitrary scheme
isomorphism. The imported fixed-data equivalence with a rigidified Poincare
pullback isomorphism explains the classifier equality.

The target of `lambda` is exactly `dualAbelianSchemeFromEvaluation`. Its group
law was constructed from tensor classification, and its geometry is the
explicit predicate `DualSchemeGeometry A hA`. This module neither takes an
unconstrained putative dual as a new field nor constructs a polarization from
an ample line bundle. All existence, inverse evaluation and named coherence,
Picard-zero, theorem-of-the-square and base-change-universality proof inputs
required by the imported constructions remain explicit. In particular, no
unconditional existence or base-change theorem is established here.

`IsPrincipalFieldPolarization` adds `IsIso lambda` in the category of abelian
schemes to the polarization condition. It makes no degree calculation and
does not identify all isomorphisms to a dual as polarizations.

## Source correspondence

Edixhoven–van der Geer–Moonen, *Abelian Varieties*, Chapter XI,
Corollary (11.5)(b1) and Definition (11.6), printed p.160 (PDF164), define a
polarization as an isogeny satisfying the equivalent polarization criteria.
This module selects exactly the criterion that, after some field extension,
the map equals `phi_L` for an ample `L`. Definition (11.6) calls a
polarization principal when it is an isomorphism. The surrounding discussion
begins on printed p.159 (PDF163).

The presentation is derived only in its explicit handling of normalization,
inverse choices and the actual base-change comparison. The imported
Mumford-map and dual definitions fix these choices mathematically. This
module does not prove the equivalences with symmetric isogenies, diagonal
Poincare ampleness, or finite separable extension criteria, and it makes no
claim about polarizations over a general base or rational quasi-isogenies.
