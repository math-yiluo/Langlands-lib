# Actual Tits indices of semisimple field groups

The source is J. Tits, *Classification of algebraic semisimple groups* (1966),
§§2.1–2.3, printed pp.38–39 (proceedings PDF pp.43–44), with the orbit
terminology of §2.5.1, printed p.40 (PDF p.45). Registered source:
`tits-1966-classification-algebraic-semisimple`; PDF SHA-256:
`962203f9e47e9c3c43fc1049a38e28c751aa42beb7ee5250a095a132e215a5d4`.
Worker 168 checked these original pages. No corresponding errata file was found.

Every declaration is in `Langlands.GroupScheme`. The field `k : Type u` is
arbitrary, and `u` is arbitrary. There is no local-field, perfectness or
characteristic restriction, including in characteristic two. Ambient groups
have the explicit typeclass hypotheses `IsAffineHom G.X.hom` and
`LocallyOfFiniteType G.X.hom`. The latter follows from smoothness for a
semisimple group; it is explicit because the existing star-action interface
uses it. The definitions compare groups in the same universe over `k`.

`absoluteRootRestriction p S hS f a` starts from actual
`GaloisPinningData k (SeparableClosure k) G`, a split commutative torus `S`
over `k`, and a morphism `f : S ⟶ p.torus`. It composes the base change of
`f` with the actual root character `p.rootDatum.root a`. The inverse of
the published character-lattice base-change equivalence for a split torus
descends that character uniquely to `X*(S)`. No root character or
restriction map is supplied as arbitrary data.

`TitsIndexData G` consists of:

- Semisimplicity of the actual group, Galois pinning data over its separable
  closure, and maximality of that pinning's torus over `k`.
- An actual maximal split torus inclusion `S → G`, and a map `S → T`
  whose composite with `T → G` is that inclusion.
- A cocharacter of `S` generic for the Library's actual relative roots,
  and agreement between its positive signs and the chosen absolute base
  on every absolute root whose restriction is nonzero.

The last condition is a finite-root formulation of the compatible orders
chosen in §2.1. A generic integral cocharacter specifies the relative
positive chamber. Absolute roots restricting to zero are ordered by the
chosen absolute base. Extending the relative order across the restriction
kernel gives the compatible-order interpretation; the interface does not
choose total orders on all lattice elements. Existence of these compatible
choices is a separate unproved structural target, not a field of a
purported classification.

For `d : TitsIndexData G`, the namespace `TitsIndexData` provides:

- `Vertex`: the subtype of the actual base's simple-root support. Its
  finiteness follows from the existing finite absolute root index.
- `cartan`: the actual integral root/coroot pairings on these vertices,
  retaining the complete Dynkin diagram, including root-length orientation.
- `rootRestriction`: the preceding actual character restriction for
  every absolute root.
- `zeroVertices`: `Δ₀`, the simple vertices with zero restriction.
  `distinguishedVertices` is its complement.
- `star`: evaluation of the Library's `GaloisPinningData.starAction` on
  each simple vertex, for each actual element of `Gal(k_s/k)`. Support
  preservation is part of a based root-datum automorphism.
- `star_one` and `star_mul`: the action laws, obtained by applying the
  existing star-action monoid-homomorphism laws to root indices.
- `distinguishedOrbitSetoid`: two distinguished vertices are related
  exactly when some element of this same Galois group carries one to the
  other. Reflexivity uses the identity, symmetry the inverse, and
  transitivity the product. Restricting the orbit equivalence relation
  to the complement makes this definition independent of the later
  proof of invariance.
- `DistinguishedOrbit`: the finite quotient by that relation;
  `orbitClass` is its quotient map. This quotient does not replace the
  full action stored in the data.

`TitsIndexEquiv d e` compares indices of any two such groups over `k`.
It is a vertex equivalence preserving every Cartan pairing, zero
restriction, and the action of each absolute Galois element individually.
In particular, it preserves more information than orbit cardinalities.
It does not assert that the groups are isomorphic. The universe and the
affine and locally-finite-type hypotheses apply to both ambient groups.

The packaging, the character descent, the cocharacter encoding of
compatible positivity, and this explicit equivalence structure are
implementation choices derived from the source definition. Tits §2.3
defines the same mathematical index as the diagram, `Δ₀`, and full star
action, and explicitly cautions that a diagram displaying only orbits
loses information. This module proves only the action laws and
finiteness needed to form the orbit quotient. Existence, independence,
invariance, comparison with the existing relative simple roots and
`splitRank`, and the actual anisotropic-kernel comparison remain
separate structural propositions.
