# Finite-Galois conductor inflation and common-refinement independence

Worker 48 states a single family concerning the published rational Artin and
Swan sums of actual finite p-adic Galois representations. The complete target is
`Langlands.Ramification.Padic.FiniteGaloisConductorInflationAndIndependenceStatement`.
All four declarations in this module are `def`s returning `Prop`. This module
states the results; it does not prove them.

## Fields, towers, and representations

The target quantifies over every prime `p` and actual finite extensions of
`Padic p`, represented by `PadicField p`. The two-field inflation clause uses
`E` and `L`; the common-refinement clause uses `E`, `E'`, and `L`. Each has its
own supplied `TopologicalData`. This data certifies a valuation extending the
p-adic valuation, the canonical topology of a finite-dimensional p-adic vector
space, and the nonarchimedean local-field property.

The common base `K` is an actual field with an algebra structure over `Padic p`.
The algebra structures and scalar towers explicitly describe `Padic p → K → E → L`,
and, for common refinement, `Padic p → K → E' → L`. They include compatibility
of each direct map from `Padic p` and each direct map from `K` with the
corresponding composite. Field algebra maps are injective. Since `L` is finite
dimensional over `Padic p`, its intermediate base `K` and all the indicated
extensions are finite dimensional. No independent topology on `K` is needed by
the imported conductor definitions.

The supplied local-field structures use the same base p-adic valuation and
canonical module topologies; compatible scalar embeddings preserve these
valuation rings. No arbitrary filtration or integer-ring action is supplied.
The conductor functions use exactly the integer rings, residue actions, and
lower groups constructed in the published `Ramification.Galois` module.

Every component explicitly quantifies `IsGalois K E.Carrier` and
`IsGalois K L.Carrier`; common refinement also quantifies
`IsGalois K E'.Carrier`. These retain normality and separability in the
proposition itself. In a compatible field tower they also imply the needed
Galois property of `L/E` and `L/E'`. The extension fields have characteristic
zero through their embeddings of `Padic p`.

The representation coefficients are specifically `ℂ`, and the vector spaces
are finite dimensional. The base field, both intermediate fields, common
refinement field, and both representation spaces have independent universe
parameters `uK`, `uE`, `uE'`, `uL`, `uV`, and `uW`. No irreducibility,
faithfulness, positive dimension, or equality of the vector-space carriers
is assumed.

## The actual maps and sums

For `E ⊆ L`, the map denoted by `π` is
`AlgEquiv.restrictNormalHom (F := K) (K₁ := L.Carrier) E.Carrier`.
Its source is `L.Carrier ≃ₐ[K] L.Carrier` and its target is
`E.Carrier ≃ₐ[K] E.Carrier`. It is the actual field-automorphism restriction
map. Normality is supplied by the Galois hypothesis. Its surjectivity is a
field-theoretic fact, not an arbitrary map parameter or an assumed equality of
conductors.

Inflation is written `ρ.comp π`: its action on `g` is exactly `ρ (π g)`, on the
same vector space. In the pinned Mathlib, `Representation` is an abbreviation
for a monoid homomorphism to linear endomorphisms, so this composition elaborates
to `MonoidHom.comp`. It is the representation-composition operation, with no
new inflation constructor.

The values compared are exactly `Padic.artinConductor` and
`Padic.swanConductor`, taking values in `ℚ`. For the actual lower groups `G_i`
of the relevant extension, these are

`a(ρ) = Σ_{i≥0} (|G_i| / |G_0|) · (dim V − dim V^{G_i})`,

`Sw(ρ) = Σ_{i≥1} (|G_i| / |G_0|) · (dim V − dim V^{G_i})`.

The imported construction proves finite support. Both denominators are the
cardinality of actual inertia, and the Swan expression is the positive-index
tail of the same sum.

## The three components

`FiniteGaloisInertiaInflationStatement` states equality of the two actual
submodules of `V` fixed by `inertia TL K` acting through `ρ.comp π` and
`inertia TE K` acting through `ρ`. It also explicitly states equality of their
natural-number codimensions, using the published `fixedCodimension`.
The codimension clause follows from the submodule equality and supplies the
tame comparison needed for Swan invariance.

`FiniteGaloisConductorInflationStatement` states, for every such representation,
both `a(L/K, ρ.comp π) = a(E/K, ρ)` and
`Sw(L/K, ρ.comp π) = Sw(E/K, ρ)`.

`FiniteGaloisConductorCommonRefinementStatement` supplies actual fields
`E`, `E'`, and `L` over the same `K`, with both compatible towers and the
Galois hypotheses. It takes representations `ρ` and `σ` on possibly different
spaces and a genuine `Representation.Equiv (ρ.comp π) (σ.comp π')` on
`Gal(L/K)`. This is an invertible linear intertwiner, not a bare vector-space
equivalence. The conclusions are equality of the original Artin sums and
equality of the original Swan sums for `E/K` and `E'/K`. The `L.TopologicalData`
argument is retained explicitly as `_TL`: it certifies an available common
local-field realization, although only the endpoint conductor values occur
in this conclusion.

The combined declaration universally quantifies the inflation clause and the
common-refinement clause separately. Thus inflation has no dependence on an
unneeded second presentation.

## Original source and derivation

Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg,
Graduate Texts in Mathematics 67, Springer, 1979:

- Literature ID: `serre-1979-local-fields`.
- Retained file: `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.
- SHA256: `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
- Chapter VI, section 1, printed page 97 / PDF page 104 fixes the
  finite-dimensional complex representation convention.
- Chapter VI, section 2, Proposition 2 and Corollary 1', printed pages
  100–101 / PDF pages 107–108 give the weighted fixed-space formula.
- Chapter VI, section 2, Proposition 3 and its Corollary, printed page
  101 / PDF page 108 give invariance under inflation from a quotient group.
- Chapter I, section 7, Proposition 22(b), printed pages 22–23 / PDF pages
  30–31 gives exactness of inertia restriction in a Galois tower.

These original passages were read for this contribution. There is no source
errata file for this source in the supplied public notes.

The Artin clause translates the Corollary to VI.2 Proposition 3, specialized to
actual finite p-adic Galois fields and to the character of `ρ`. For the normal
subgroup `Gal(L/E)`, Galois restriction identifies the quotient with `Gal(E/K)`;
inflating the character is exactly taking the character of `ρ.comp π`.
The fixed-space formula identifies Serre's character conductor with the
published rational sum. Proposition 4 on that page concerns induction and
the discriminant; it is not the source of this inflation statement.

The inertia clause is a derived formulation of I.7 Proposition 22(b).
Restriction carries actual inertia of `L/K` onto actual inertia of `E/K`.
A vector is therefore fixed by all elements in the former group acting
through `π` exactly when it is fixed by all elements in the latter group.
This proves the mathematical subspace comparison and hence its codimension
comparison.

Swan invariance is a derived consequence of Artin invariance and that tame
comparison. The published
`Langlands.Ramification.artinConductor_eq_tame_add_swan`, specialized to the
actual integer-ring action, together with
`Langlands.Ramification.Padic.lowerRamificationGroup_zero`, identifies the
index-zero term with the codimension of inertia invariants. Subtracting these
equal tame terms from the equal Artin values gives equal Swan values.

Common-refinement independence is another derived consequence. Apply
inflation invariance to each tower. At `L`, apply the already proved
`Langlands.Ramification.Padic.artinConductor_equiv` and
`Langlands.Ramification.Padic.swanConductor_equiv` to the supplied equivalence.
Transitivity gives the two equalities at the original presentations. These
existing equivalence invariance results are reused, not restated as new
obligations.

This explanation records the mathematical provenance of the statements,
not Lean proofs in this module. No equality of lower-numbering ramification
groups at the same index is assumed or asserted. Serre IV.1, printed page 64 /
PDF page 71 explicitly notes the need to change numbering for general
quotients. The direct conductor corollary avoids needing a quotient
ramification formula in these statements.

## Scope and validation

This family supplies a finite-Galois inflation bridge. It neither constructs
an intrinsic conductor for every Weil representation nor proves existence of a
finite inertia presentation. It does not compare arbitrary inertia-only
quotient presentations, supply missing restriction or descent maps, choose a
common refinement, or assume generic equivalences of filtered groups. It
retains characteristic-zero coefficients and the finite-Galois field setting;
the more general local-ring action conductor constructors do not justify a
broader assertion here.

The pinned environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`,
Lean 4.34.0, Lean commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`,
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
Compilation and whole-target inspection are distinct from independent
semantic acceptance and current Library publication.
