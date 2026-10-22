# Arithmetic statements for actual Herbrand functions

Worker 60 authored the initial statement draft. Worker 70 repaired its intrinsic
fixed-field instances, audited the original source and complete declaration types,
and prepared this paired module. The eight separately named proposition
families and their aggregate are statements for later proof tasks. None is an
assumption in the construction of phi, psi, or the upper ramification groups.

## Fields, embeddings, and realizations

All names below lie in `Langlands.Ramification.Padic`. The prime `p` is arbitrary
with `[Fact p.Prime]`. The base `K`, intermediate field `E`, and extension `L`
are actual `PadicField`s in independent universes `uK`, `uE`, and `uL`.
Their finite-dimensional structures over `Padic p` are intrinsic to these
objects. Algebra structures specify the actual embeddings, and scalar-tower
instances express their compatibility. The Galois hypotheses refer to these
embeddings. Thus the module covers all finite p-adic Galois extensions and
compatible finite Galois towers; it specializes Serre's more general complete
discrete valuation setting to finite p-adic fields, whose residue fields are
finite and hence perfect.

Each component has an explicit `IsGalois K.Carrier L.Carrier` parameter. The
three tower components also have `IsGalois K.Carrier E.Carrier` and
`IsGalois E.Carrier L.Carrier`. The latter is redundant for a compatible tower
inside a Galois `L/K`, but is retained explicitly in the interface. No arithmetic
compatibility conclusion is supplied as a parameter.

The supplied `T : L.TopologicalData` and, when needed,
`S : E.TopologicalData` are arbitrary legitimate realizations. Such data include
a valuation extending the p-adic valuation and the canonical module topology.
The published `PadicField.canonicalTopologicalData` realizes every `PadicField`,
including each fixed field. Thus quantifying over these realizations does not
restrict the family to fields for which an additional existence certificate
has been supplied. For a fixed tower the aggregate quantifies first over `T`,
then `S`; the fixed-field quotient clauses quantify additionally over the
realization of each fixed field.

## Intrinsic fixed fields

`fixedPadicField K L H` is a reducible abbreviation packaging exactly
`IntermediateField.fixedField H`. It retains the subtype carrier, field
operations, p-adic algebra structure, and inherited embeddings. Its body first
obtains `FiniteDimensional K.Carrier L.Carrier` by restriction of scalars from
the intrinsic p-adic finiteness, then obtains finiteness of the intermediate
field over `Padic p` by transitivity. The record literal makes its carrier
visible to typeclass search; there is no transport to a replacement carrier.

`fixedFieldPadicScalarTower K L H` supplies the intrinsic tower
`Padic p → fixedField H → L.Carrier`. Its proof is
`IsScalarTower.of_algebraMap_eq` with the defining algebra-map equality proved
by reflexivity. Mathlib supplies the other intermediate-field algebras and
towers, and `IsGalois.of_fixedField_normal_subgroup` supplies Galoisness of the
fixed field over `K` whenever `H` is normal. These two helper declarations
are internal packaging and instance proofs, not extra arithmetic hypotheses.

## Source correspondence

Write `G = Gal(L.Carrier/K.Carrier)` and `E_H = L^H` for the actual fixed field.
The imported `lowerRamificationGroupReal` uses `G_ceil(u)`, matching Serre IV.3,
printed page 73. `herbrandPhi` is the constructed cardinality polygon, equal to
the identity on `[-1,0]`; `herbrandPsi` is its genuine inverse.
`upperRamificationGroup T K.Carrier v` is the actual lower group at `psi(v)`.
Every component with a free real index requires that index to be at least `-1`.

- `LowerSubgroupCompatibility K L T` quantifies over every subgroup `H`,
  without a normality hypothesis, and every `u ≥ -1`. The image of the lower
  group for `L/E_H` under `AlgEquiv.restrictScalarsHom K.Carrier` equals
  `G_u ⊓ H`. This is the ramification-group equality of IV.1, Proposition 2,
  printed page 62, extended to real indices by the ceiling convention on
  page 73. The scalar restriction forgets the requirement of fixing `E_H`;
  it does not restrict the automorphism's domain to the fixed field.
- `HerbrandNormalSubgroup K L T` quantifies over `H`, `[H.Normal]`, every
  `S : (fixedPadicField K L H).TopologicalData`, and `u ≥ -1`. The image of
  `G_u` under the actual `AlgEquiv.restrictNormalHom` to `E_H` equals the
  lower group of `E_H/K` at `phi_(L/E_H)(u)`. This is IV.3, Lemma 5
  (Herbrand's theorem), printed page 75. The source writes this image as
  `G_u H/H`; the field-theoretic restriction identifies the quotient with
  `Gal(E_H/K)`. Both sides here use lower numbering.
- `UpperQuotientCompatibility K L T` has the same subgroup, normality and
  realization quantifiers, followed by `v ≥ -1`. Under that same normal
  restriction, the image of `G^v` is the upper group of `E_H/K` at `v`.
  This is IV.3, Proposition 14, stated on page 74 and proved on page 75.
- `HerbrandPsiIntegral K L T` states that for every `n : ℕ` there is `m : ℕ`
  with `psi_(L/K)(n) = m` as real numbers. Proposition 13(d), printed pages
  73–74, gives integral output at integral input. For nonnegative input,
  the inverse is nonnegative because it is increasing and fixes zero,
  so a natural witness is appropriate. The remaining integer in Serre's
  domain, `-1`, is already covered by the imported `herbrandPsi_neg_one`.
- `HasseArfIntegrality K L T` assumes `IsMulCommutative G` and asserts that
  every `i : ℕ` with `G_i ≠ G_(i+1)` has `phi_(L/K)(i) = n` for some `n : ℤ`.
  This is the bracketed finite-break formulation of the Hasse–Arf theorem
  on printed page 76. Commutativity concerns the actual Galois group.
  The possible break at `-1` already has integral phi by
  `herbrandPhi_neg_one`; the natural-index formulation captures every
  remaining lower break. No proof from Chapter V, section 7 is claimed here.
- `HerbrandPhiTower K L E T S` states, for every `u ≥ -1`,
  `phi_(L/K)(u) = phi_(E/K)(phi_(L/E)(u))`.
  `HerbrandPsiTower K L E T S` states, for every `v ≥ -1`,
  `psi_(L/K)(v) = psi_(L/E)(psi_(E/K)(v))`.
  These are the two formulas of IV.3, Proposition 15, stated on page 74
  and proved on page 75. The compositions have opposite orders.
- `UpperRestrictionCompatibility K L E T S` states, for every `v ≥ -1`,
  that the image of `G^v` under the actual normal restriction to `E.Carrier`
  equals the upper group of `E/K` at `v`. This expresses Proposition 14 for
  independently presented compatible carriers. The field embedding identifies
  `E` with its image in `L`; neither a subtype presentation nor an arbitrary
  replacement group homomorphism is required.

`FiniteHerbrandArithmetic K L E` is the conjunction of these eight components
for every `T` and `S`. It is an internal organization of the cited statement
families; it introduces no additional mathematical assertion beyond them.

## Complete declaration audit

The first five components have outer parameters in this order:
`{p}`, primality, `K`, `L`, the algebra `K → L`, the tower `Padic p → K → L`,
Galoisness of `L/K`, and `T`; their result is `Prop`. The subgroup, normality,
fixed-field realization, real-index, commutativity, and break hypotheses occur
inside the corresponding proposition as described above.

For the two composition components and the aggregate, the complete outer
parameter order is `{p}`, primality, `K`, `L`, algebra `K → L`, tower
`Padic p → K → L`, `E`, algebras `K → E` and `E → L`, towers
`Padic p → K → E` and `Padic p → E → L`, tower `K → E → L`, and the three
Galois hypotheses in the order `L/K`, `E/K`, `L/E`. The composition components
then take `T`, `S` and return `Prop`; the aggregate returns `Prop` with `T`, `S`
quantified inside it. `UpperRestrictionCompatibility` has the same order
except that it does not take the unused `Padic p → E → L` instance: it uses
only the lower and upper groups over `K`, and the other tower compatibilities
already force compatibility of `E → L` with the p-adic embeddings.

The full unapplied declaration types were inspected with universe printing,
including every instance binder. The composition laws explicitly retain the
`K → E → L` compatibility parameter. The aggregate was also checked by the
Lean service's exact declaration inspection: it returns `Prop` with independent
universe parameters `uK`, `uE`, `uL` and only the standard foundational axioms.
Compilation and declaration inspection do not constitute proofs of the
arithmetic proposition families.

## Original source and scope

Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg,
GTM 67, Springer (1979), Chapter IV, section 1, Proposition 2, printed
page 62 (PDF 69), and section 3, Proposition 13(d), Propositions 14–15,
Lemma 5, and the Hasse–Arf statement, printed pages 73–76 (PDF 80–83).
The surrounding hypotheses on printed pages 61–62 and the real-index
conventions on pages 73–77 were read; formula-sensitive page images were
inspected directly. No source-specific errata note was found in the project.

Registered source: `serre-1979-local-fields`, retained file
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

The imported project modules supply the actual lower/upper ramification groups,
integer-ring actions, and inverse Herbrand functions. Mathlib supplies the
actual fixed fields and scalar/normal restriction maps. Absolute ramification,
local reciprocity, conductor transport, and proofs of these arithmetic families
are outside this statement module.
