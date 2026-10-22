# CM character globalization and finite-unit prescription

Author: Worker 35. Statement contribution to task
`91266440-3276-48dc-ab77-8d1c1fa386e8`, revision 1.
All declarations are proposition definitions.
No existence theorem is proved or assumed by defining them.

## Actual objects and normalization

The namespace is `Langlands.Global`. The field `K : Type u` is a number
field with Mathlib's `NumberField.IsCMField` instance. Complex conjugation
is the actual arithmetic involution `IsCMField.complexConj K`. Its action
on the actual idele-class quotient is the constructed continuous
equivalence `AdelicFunctoriality.ideleClassComplexConj`. Self-duality is
written explicitly as

\[
  \chi(c(x))=\chi(x)^{-1}
\]

for every idele class. No unspecified action or self-duality predicate
is supplied as a hypothesis.

`InfinityType K` is the integer-valued function on actual complex
embeddings. Its anticyclotomic condition says that conjugate embeddings
have opposite weights. `InfinityType.toCharacter` is the constructed
continuous character of the full infinite idele factor. At a chosen
complex coordinate it has the formula
\[
  z^{a_\sigma}\overline z^{\,a_{\overline\sigma}}
  =(z/\overline z)^{a_\sigma}.
\]
The sign agrees with Henniart's displayed infinity component. Using the
other embedding of a conjugate pair swaps the weights and conjugates
the coordinate, leaving the character unchanged.

All finite places are actual nonzero prime ideals, their completions
are the actual adic completions, and their integral units are the units
of the actual valuation integer rings. Restrictions to these units use
`Units.map` of the subring inclusion.

## Unramified realization of infinity weights

`CMUnramifiedInfinityRealizationStatement` quantifies an anticyclotomic
integral infinity type and asks for one natural number `m > 0` and one
Hecke character satisfying all three conditions:

1. conjugate self-duality;
2. the infinity character with weights `m * a`;
3. unramifiedness at every finite place.

The same positive multiplier applies to every weight. Neither a separate
multiplier at each place nor a loss of finite-place unramifiedness would
state the required result.

This is the embedding-independent formulation of Henniart 2000,
Section 3.5, Lemma 1, printed p.450. The source has already fixed a CM
field containing a chosen imaginary-quadratic field, so its weights
are indexed by embeddings extending one embedding of that subfield.
Opposite weights extend this indexing to all embeddings. The target's
first clause permits an arbitrary CM number field and an anticyclotomic
weight function: this is a derived generalization of that lemma, not
a claim that the source quantifies over that larger class verbatim.
The source's proof uses finiteness of the ideal class group and finite
index of the units of the maximal real subfield inside the CM units.
Those facts hold for a CM field without an imaginary-quadratic subfield.
Its norm-killing argument therefore has the same conclusion for this
formulation. A future proof must supply these facts, the relevant
topological character extension, and the common positive multiplier;
none is an input field of the target.

## Finite-order conjugate-self-dual prescription

`CMFiniteCharacterPrescriptionStatement` takes a finite set `S` disjoint
from its image under the actual conjugation of finite places. For any
finite-order local characters on `S`, it asks for a finite-order global
character with those exact local components, trivial infinity component,
and conjugate self-duality.

The place map is `finitePlaceEquiv (complexConj K).toRingEquiv`, the
pullback of prime ideals along the arithmetic involution. Since that
involution is its own inverse, its pullback is also the conjugate-place
involution. Disjointness excludes fixed places and pairs of conjugate
places both in `S`. This retains the splitting/separation needed by the
source; arbitrary incompatible prescriptions at conjugate places are
not permitted.

This clause generalizes the two-place prescription of Henniart's
Section 3.6, Lemma 2, pp.450–451, to a finite separated set. Prescribe
a finite-order character `lambda` on `S` and the trivial character on
the conjugate set, and put `chi = lambda / (lambda composed with c)`.
Henniart's Lemma 2 does not mention the infinity component. Its
triviality is automatic: `K` is totally complex, so the archimedean
idele factor is a finite product of copies of the connected group of
nonzero complex numbers, and a continuous character of finite order
on it takes values in a finite discrete set containing one. The clause
is kept explicit so that a later product with the Lemma 1 realization
has exactly the stated infinity component. The Grunwald–Wang
existence assertion used in this argument has its unconditional
period-doubling allowance; no bound on the final character's order is
asserted here. The published finite-order prescription statement
`FiniteOrderCharacterPrescriptionStatement` (module
`Langlands.Global.Arithmetic.CharacterPrescriptionStatement`) is a
separate, unproved theorem obligation, not an imported proof of this
clause.

## Characters of integral units

`IntegralUnitCharacterExtensionStatement` quantifies an arbitrary
continuous complex character of the actual integral-unit group and
asks for a finite-order continuous extension to the local
multiplicative group. Agreement on units is an explicit pointwise
equality after the actual inclusion.

Henniart uses this local step at the beginning of the proof of
Section 3.6, Lemma 3, p.451. The standard derived justification is that
the compact profinite integral-unit group has finite image under a
continuous character into complex units: the target has a neighborhood
of one containing no nontrivial subgroup, and the source has an open
subgroup inside its preimage. The character therefore factors through
a finite quotient. Extend by assigning one to a uniformizer in the
valuation decomposition of the local multiplicative group. Compactness,
the principal-unit neighborhood basis, and that decomposition are
mathematical proof obligations, not data assumed by the definition.
The Serre passages cited below give the decomposition, the compactness
and the neighborhood base.

## Regular infinity weights and prescribed finite units

`CMRegularUnitPrescriptionStatement` combines the preceding clauses.
It retains an imaginary-quadratic number field `E : Type v` through
the explicit assumptions `IsTotallyComplex E` and
`Module.finrank ℚ E = 2`, an embedding `ι : E →+* K`, and a fixed
complex embedding `τ : E →+* ℂ`. The universes `u` and `v` are independent.
The weight function is anticyclotomic and injective on the actual
embeddings of `K` extending `τ` along `ι`.

For continuous integral-unit characters at a finite separated set,
the conclusion provides a conjugate-self-dual Hecke character and
a common positive scaling of the given infinity weights. The scaled
weights remain injective on those extending embeddings. The finite
prescriptions hold on integral units. The conclusion does not require
a fixed value on each uniformizer: multiplying by the everywhere
finite-unramified character from Lemma 1 can change those values.
This distinction is essential in Henniart's Lemma 3 and Section 3.7.

The derived argument extends each unit character to finite order,
uses the finite self-dual prescription, and multiplies by the
unramified infinity realization. Positive integer multiplication
preserves distinct integer weights. This target generalizes the
assembly step to a separated finite set. It does not assert that an
arbitrary prescribed auxiliary character has the local general-position
property of Section 3.4, condition 3.

`CMCharacterGlobalizationStatement` is the conjunction of these four
complete targets, preserving their quantifiers. The local norm-pullback
and stabilizer existence assertion behind Section 3.4, condition 3, is
the separately published `AuxiliaryCharacterStatement` (module
`Langlands.Global.Arithmetic.AuxiliaryCharacterStatement`), stated over
the project's p-adic field objects. Condition 3 depends only on the
restriction of the local character to integral units, so a unit
prescription at the auxiliary place can carry it. Transport between a
number-field completion and those p-adic field objects is not part of
this pair, and the Harris weak-induction output with its supercuspidal
condition also remains separate.

## Original sources

- Guy Henniart, *Une preuve simple des conjectures de Langlands pour
  GL(n) sur un corps p-adique* (2000), Sections 3.3–3.4, p.449;
  Section 3.5, Lemma 1 and its proof, p.450; Section 3.6, Lemmas 2–3
  and proofs, pp.450–451; Section 3.7, p.451.
  The retained original was read directly, including the displayed
  infinity formula, the norm quotient argument, and the distinction
  between equality on units and equality of whole local characters.
  Source `henniart-2000-simple-proof`, SHA256
  `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
- Artin–Tate, *Class Field Theory*, AMS Chelsea edition (2009),
  Chapter X, Sections 1–2, pp.73–80, especially Theorem 5, p.80.
  This supplies the underlying finite-order prescription with the
  possible doubling of the common period. It does not by itself state
  the CM or regular-infinity conclusions.
  Source `artin-tate-2009-class-field-theory`, SHA256
  `af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
- Serre, *Local Fields*, English translation (1979): Chapter I,
  Section 1, p.5 (every nonzero element is a power of a uniformizer
  times a unit); Chapter II, Section 1, Proposition 1, p.27 (a complete
  field with finite residue field has compact valuation ring, the
  projective limit of finite quotients); Chapter IV, Section 2, p.66
  (the higher unit groups form a neighborhood base of one in the unit
  group) and Proposition 6. These are the local ingredients of the
  derived unit-character extension.
  Source `serre-1979-local-fields`, SHA256
  `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

## Dependencies and acceptance boundary

Every imported project module is published at Library commit
`30ceb5a0d89d8094c1663fc19f35416519b9a125`. The module imports
`Langlands.Global.HeckeCharacter`, `Langlands.Global.InfinityType` and
`Langlands.Global.AdelicFunctoriality.Isomorphism`; the other three
modules below enter through these imports. The compiled sources are
byte-identical to the Library files:

| Module | Author | Lean SHA256 |
| --- | --- | --- |
| `Langlands.Global.Adelic` | Worker 2 | `b1b7213c47725ac26e0ce09b0e483e548c8a4e1f3fd4a4972cedb64b7ce8258e` |
| `Langlands.Global.HeckeCharacter` | Worker 2 | `68525fbd6a536afefdb696f83491c0ddd60d506390cf7dcb9682c7688c3de18f` |
| `Langlands.Global.InfinityType` | Worker 2 | `11287e03f4ac10451fc4a33d11e5aba337e2b5993cb1a9c96b9ff71ee5bae7c2` |
| `Langlands.Global.AdelicFunctoriality.Infinite` | Worker 50 | `7fb0269ebb82579748b236b65ed5e48c332d08238db90c8df3602005e78c86a9` |
| `Langlands.Global.AdelicFunctoriality.Finite` | Worker 50 | `e11f6163511b52a80ac95e88bb7101156aedcf08fe0ee29623a5d6ecc097bbc1` |
| `Langlands.Global.AdelicFunctoriality.Isomorphism` | Worker 50 | `f9c46bd3c0ed01073c73cf748e279fd5393c479b587673e6c350440c7e73c749` |

The field, completion, idele and quotient transport is constructed
in those dependencies with intrinsic algebraic and continuity proofs.
No supplied map in this statement stands in for that construction.

The module compiled with no errors or warnings under Lean 4.34.0 and
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`, in the project
environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`. Inspection of
`CMCharacterGlobalizationStatement` reports a `Prop`-valued definition
with level parameters `u` and `v` and only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`. All five definitions were
printed with explicit universes. Each returns `Prop`, and the final
target keeps the independent universes `u` and `v` and every hypothesis
described above.

These development checks provide neither independent semantic
acceptance nor proofs of the existence assertions.
