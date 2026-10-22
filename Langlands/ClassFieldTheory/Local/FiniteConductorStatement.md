# Finite-character conductor transport under local reciprocity

Worker 10 authored the proposition family
`Langlands.LocalClassField.FiniteCharacterConductorTheorems.{u}` and its
elementary representation helper. This is a statement contribution.
It neither proves local reciprocity nor proves the conductor comparison.

## Actual objects and scope

The base is every `PadicField p` in universe `u`, for every prime `p`,
with arbitrary supplied `T : F.TopologicalData`. The published
`PadicField.canonicalTopologicalData` supplies such data for every field.
Each `L : LocalFiniteAbelianExtension F` is an actual finite abelian
intermediate extension in `AlgebraicClosure F.Carrier`, not an abstract
finite group. Its existing `asPadicField` construction retains those field
operations and gives a finite p-adic field. `S` is any of its topological
realizations. This parametrizes the actual subextensions of the chosen
closure; an isomorphism transport is needed to apply this formulation to
another presentation of the same finite extension. The base carrier
universe is unrestricted, and no universe-zero restriction is imposed on
its algebraic closure or finite intermediate fields.
The local algebra and scalar-tower instances on `L.asPadicField.Carrier`
are explicitly the existing instances on `L.field`, via
`inferInstanceAs`. This only exposes the definitional wrapper to instance
search; it neither chooses another embedding nor changes the field or
Galois group operations.

The continuous map `r : F^x -> G_F^ab` is quantified, and the four transport
assertions are conditional on the explicit
`GeometricProfiniteReciprocityRelation F T r`. That relation requires
density, the actual finite norm kernels and surjectivity, restriction
compatibility, and geometric residue normalization. It does **not** assume
unit images, ramification transport, or a conductor equality.
The unconditional existence and uniqueness of such an `r` is the
separate `ProfiniteReciprocityExistenceUniqueness` target. This family is
therefore a consequence layer of that target; it does not replace the
existence target with a hypothesis or claim that the combined local CFT
assignment is complete.

For each actual finite abelian `L`, `finiteFamilyOfHom r L` is the existing
composition of `r` with actual finite Galois restriction. A finite
character `chi : L.galoisGroup -> continuous Complex^x` transports to
the continuous character `chi.comp (finiteFamilyOfHom r L)` of `F^x`.
Its finite image follows from the finite source Galois group. Faithfulness
of `chi` is not required. This family does not identify arbitrary
infinite-image quasicharacters with characters of the profinite group;
that broader transport uses the Weil formulation.

`rankOneCharacterRepresentation` specializes the published
`Langlands.characterRepresentation` to the complex line, where the
character acts by scalar multiplication. Its proved evaluation lemma is
`rho(g)(z) = chi(g) * z`. This is an internal conversion between existing
objects, not a new character type or a representation supplied as a
desired-conclusion certificate.

## The five assertions

1. `UnitFiltrationComparison` identifies the existing quotient-kernel
   filtration `T.unitFiltration n` with the existing valuation filtration
   `T.principalUnits n`, for every natural `n`. The former comes from
   reduction of integer-ring units modulo the `n`th maximal-ideal power;
   the latter requires `v(a)=1` and `v(a-1)<=exp(-n)`. Both have the full
   valuation-unit group at zero. This is an intrinsic comparison
   proposition between the two imported constructions, not a new choice
   of filtration.

2. `FiniteReciprocityInertiaImages` states that the image of the actual
   unit subgroup under the finite reciprocity map is the actual inertia
   kernel `Ramification.Padic.inertia S F.Carrier`. The image of the first
   principal-unit level is the existing first lower group
   `lowerRamificationGroup S F.Carrier 1`. In a finite abelian extension,
   this is wild inertia, and it also equals the first upper group.
   The equality uses the abelian ramification theorem; there is no claim
   that upper and lower groups coincide at all positive indices.

3. `FiniteReciprocityConductorTransport` compares the imported
   `T.multiplicativeConductor` with
   `Ramification.Padic.artinConductor S F.Carrier` on the actual
   one-dimensional representation. The first is a natural number chosen
   as the least principal-unit level of triviality after its existence
   was proved in the conductor construction. The second is the original
   rational sum
   `sum_{i>=0} (|G_i|/|G_0|) codim V^(G_i)`,
   whose finite support is already proved from the actual integer-ring
   action. Lean casts the natural number into the rationals and asserts
   equality. It does not redefine the Artin sum to be an integer.

4. `FiniteReciprocityConductorLevels` says that this rational Artin sum
   is at most `n` exactly when the transported character is trivial on
   `T.unitFiltration n`. This is a useful derived formulation of the
   equality and the already constructed least-level conductor property.

5. `FiniteReciprocityUnramifiedTameCharacters` identifies conductor zero
   with triviality on the actual inertia group. It identifies conductor
   at most one with triviality on the actual first lower group.
   Thus the unramified case has exponent zero, a ramified character
   trivial on wild inertia has exponent one, and a character nontrivial
   on wild inertia has larger exponent. The statement uses “at most one”
   so that the trivial and all unramified characters remain included.

The closing proposition is the conjunction of these five assertions.
No upper-numbering constructor is added here. Higher ramification
transport will use the separately assigned actual Herbrand construction.

## Original sources and derivations

Jean-Pierre Serre, *Local Fields*, English translation, GTM 67 (1979):

- Chapter VI, Section 2, Proposition 2 and Corollary 1', printed pages
  100-101 / retained PDF pages 107-108, gives the weighted fixed-space
  formula. Proposition 3 and its corollary on printed page 101 establish
  compatibility with quotient characters. Proposition 5 and its
  corollary, printed page 102 / PDF109, express a degree-one conductor
  through the last ramification break and Hasse-Arf integrality.
- Chapter XV, Section 2, Theorem 1 and Corollaries 1-3, printed pages
  227-228 / PDF232-233, identifies the least unit level in a norm subgroup
  and identifies unit levels under reciprocity with upper ramification.
  Theorem 2, printed page 228 / PDF233, extends the filtration statement
  to general abelian extensions. For finite residue fields the images
  are equal, not merely dense.
- Chapter IV, Section 3, printed pages 73-76 / PDF80-83, fixes the
  Herbrand and upper-numbering convention and states Hasse-Arf. This
  explains why in the finite abelian case the first upper group is the
  first lower group: no positive upper break lies strictly between
  zero and one.

Worker 10 read the complete original PDF pages 106-111, 231-234 and
78-86. For a character with a kernel, the conductor comparison first
passes to its cyclic quotient extension; the quotient-character
compatibility in VI.2 and the norm-kernel characterization supply the
general, not necessarily faithful, case. Items 4 and 5 are explicit
derived consequences of this comparison and the unit/inertia
identifications. They are not attributed to separately numbered theorems
with exactly the displayed Lean syntax.

The integer-valued multiplicative conductor convention is also J. Tate,
*Number theoretic background*, Corvallis Part II (1979), Section 3.2.6,
printed page 13 / retained PDF page 22, which Worker 10 read directly.
It is zero for an unramified character and otherwise the least positive
unit-congruence level on which the character is trivial.

The comparison of the two actual unit filtrations in item 1 is an
internal derived identification: membership in the maximal-ideal power
is the normalized valuation bound. Neither that identity nor the
conductor equality is assumed as part of supplied field data.

Serre uses arithmetic reciprocity. The relation in this project uses
its inverse, with geometric Frobenius corresponding to order one.
Inversion preserves each ramification subgroup and character kernel,
so it preserves these unit-image and conductor assertions.

Registered originals:

- `serre-1979-local-fields`,
  `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`,
  SHA256 `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
- `tate-1979-number-theoretic-background`,
  `/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part II.pdf`,
  SHA256 `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.

## Dependencies and development status

All imports are published in the Library: `Langlands.ClassFieldTheory.Local.Units`,
`Langlands.HarmonicAnalysis.Conductor`,
`Langlands.LocalFactor.Ramification.Galois`,
`Langlands.Representation.Twist.Definitions`, and
`Langlands.ClassFieldTheory.Local.ProfiniteReciprocityStatement`, together
with their construction dependencies. The separate proposition family
in `UpperReciprocityStatement` uses the published actual Herbrand groups.

The environment is Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`,
environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`.
Development compilation and exact inspection of
`FiniteCharacterConductorTheorems` succeeded with zero errors or warnings
and confirmed that it returns `Prop`. Independent semantic review and
publication remain separate requirements. No conductor theorem is claimed
as proved.
