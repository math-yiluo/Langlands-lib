# The unitary central part of a complex representation

Author: Worker 19.

`Langlands.unitaryCentralPart ρ` is the actual invariant subspace obtained
by summing the generalized central-character spaces whose characters have
absolute value one. This is an algebraic construction for any group `G` and
complex representation `ρ` on any complex vector space `V`. It prepares the
unitary-exponent portion of the discrete-series Jacquet multiplicity statement.
It does not identify this subspace with a maximal tempered submodule in this
generality.

## Construction and quantifiers

A character in the indexing set is a group homomorphism
`χ : Subgroup.center G →* ℂˣ` satisfying
`∀ z, ‖(χ z : ℂ)‖ = 1`. This is the full group center. No topology, open-kernel
condition, smoothness, admissibility, finite length or central finiteness is
assumed. The group and vector-space universes `uG` and `uV` are independent.

The imported `generalizedCentralCharacterSpace ρ χ` consists of the vectors
`v` for which

```
∃ k : ℕ, ∀ z : Subgroup.center G,
  (ρ(z) - χ(z) • id)^k v = 0.
```

The power is uniform over all central elements for each vector. The unitary
central part is the supremum of these actual submodules over the displayed
indexing set. This supremum is their algebraic sum: its vectors are finite
sums from the indexed spaces. It is not a set union, a topological closure,
a supplied direct-sum decomposition or a chosen list of constituents.
Different central characters can occur in it, so its center need not act by
one scalar character.

The Lean structure proves invariance under `ρ(g)`. For each indexed summand,
the imported invariance theorem maps it into itself; the least-upper-bound
property then maps the whole supremum into itself. This argument is encoded
as containment in the linear preimage of the same supremum under `ρ(g)`.
Thus `unitaryCentralPart` returns a genuine `Subrepresentation ρ` with its
intrinsic invariant-subspace field proved.

## Implemented laws

- `generalizedCentralCharacterSpace_le_unitaryCentralPart` includes every
  generalized space with unitary character.
- `unitaryCentralPart_le_iff` proves the universal property: an invariant
  subspace contains the part if and only if it contains every indexed space.
  The proof is the supremum's least-upper-bound property. No decomposition
  theorem is used.
- `unitaryCentralPart_eq_top_of_scalar_action` proves that the part is the
  whole representation if a specified unitary character acts by its scalars
  on every vector. Every vector then lies in its generalized space with
  exponent one. This requires neither irreducibility nor smoothness.
- `map_mem_unitaryCentralPart` proves that an ambient intertwiner preserves
  the part, by applying the imported generalized-character mapping theorem
  to each summand and then using the supremum's universal property.
- `unitaryCentralPartMap` is the restricted intertwiner. Its additive,
  complex-linear and equivariance laws are proved by restriction of those
  of the original map. `unitaryCentralPartMap_apply` identifies its underlying
  value, and `unitaryCentralPartMap_id` and `unitaryCentralPartMap_comp` prove
  preservation of identities and composition by extensionality.
- `unitaryCentralPartInclusion` is the actual inclusion intertwiner. The
  inclusion is injective, and `unitaryCentralPartInclusion_natural` proves
  that inclusion commutes with restriction of an intertwiner.
- `unitaryCentralPartEquiv` restricts an ambient equivariant linear
  equivalence and its inverse. Its two inverse laws follow from those of
  the ambient equivalence. Source and target carrier universes are independent;
  composition also permits a third independent carrier universe.

These are proved intrinsic construction laws. The file introduces no axiom,
chosen composition series, theorem hypothesis, or assumed analytic conclusion.

## Original sources and derived provenance

The construction is derived from the existing generalized central-character
spaces; it is not a literal definition asserted in the sources for arbitrary
groups.

1. W. Casselman, *Introduction to the theory of admissible representations
   of p-adic reductive groups*, draft 1 May 1995, section 2.1, printed/PDF
   p.21. Literature ID `casselman-1995-admissible-representations`, retained
   PDF SHA-256
   `78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`.
   That page defines unitary characters and the uniform-power spaces
   `V_{ω,n}` and their union `V_{ω,∞}`. Its original setting is smooth and
   center-finite. The imported `Exponents.Central` provides the actual
   algebraic generalized spaces without imposing those additional hypotheses.
   This file takes their sum over norm-one characters. The omission of
   smoothness and central finiteness is deliberate: the expression and all
   the proved laws make sense without them. Casselman's direct-sum and finite
   decomposition results in Proposition 2.1.9 are neither assumed nor proved.
2. A. J. Silberger, *Introduction to harmonic analysis on reductive p-adic
   groups* (1979), section 4.5, p.187, especially the weak-exponent definitions
   and Lemma 4.5.6; section 5.4 and Theorem 5.4.1.1, p.287. Literature ID
   `silberger-1979-harmonic-analysis`, retained PDF SHA-256
   `b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`.
   PDF page numbers are the printed pages plus six. Silberger selects unitary
   exponents of a tempered representation to define its weak exponents,
   relates weak class exponents to their central exponents under the stated
   tempered hypotheses, and uses the maximal tempered submodule in the
   discrete-series alternative of Theorem 5.4.1.1. These passages motivate
   the construction and its intended consumer. They do not claim that
   unitary central characters imply temperedness for an arbitrary
   representation.

The cited Casselman page was reread in extracted text. Both cited Silberger
pages were reread in text and page images, including the brackets limiting
the discrete-series formula to the maximal tempered part. No errata file for
these sources is present in the supplied Library.

A later GL_n statement must apply this construction to actual normalized
Jacquet representations, justify the comparison between full-center and
split-center characters, and retain the tempered-induction and discrete-series
hypotheses needed to compare it with Silberger's maximal tempered part. It
must then state the finite length and multiplicities of that part. None of
those conclusions is part of this definition contribution. In particular,
this module changes no induction, Jacquet or modulus normalization.

## Dependencies

The only project import is the published
`Langlands.Representation.Exponents.Central`. The second import is the pinned
Mathlib complex-number norm theory. All subspaces, linear maps, representations,
intertwiners and equivalences are the actual published constructions.
