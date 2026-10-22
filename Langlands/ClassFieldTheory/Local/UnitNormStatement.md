# Unit norms and the unramified character quotient

Worker 10 authored these proposition definitions. The closing declaration is
`Langlands.LocalClassField.UnitNormTheorems.{u,v}`. This is a statement
contribution, not a proof of the listed assertions or of local class field
theory.

## Objects and quantifiers

Every assertion quantifies over every prime `p`, arbitrary independent
universes for finite p-adic fields `F` and `E`, a compatible algebra structure
`F.Carrier -> E.Carrier`, its scalar tower over `Padic p`, and supplied
topological realizations `T` and `S`. The explicit finite-dimensionality
hypothesis is the actual finite-extension certificate, not a replacement
field or an abstract norm map. The published constructor
`Langlands.PadicField.canonicalTopologicalData` realizes the topological data
for every such field. Thus the supplied-data formulation leaves no field
excluded and does not assume a reciprocity system.

The norm is the published `normUnits F.Carrier E.Carrier`, namely
`Units.map (Algebra.norm F.Carrier)`. Its actual image is `normSubgroup`,
and `NormQuotient` carries the quotient topology from the original units
topology. The unit groups are the published `T.unitSubgroup` and
`T.unitFiltration n`. The latter is the image, in the field units, of the
kernel of reduction of integer-ring units modulo the `n`th maximal-ideal
power. Consequently it is `U^0 = O_F^x` at zero and `1 + m_F^n` at positive
indices. No alternate filtration is introduced.

For the first four assertions the condition is
`T.ramificationIndex = S.ramificationIndex`. These are the positive absolute
indices measured by the normalized orders of `p`. In a compatible finite
extension they satisfy `e(E/Q_p) = e(E/F) e(F/Q_p)`, so equality says precisely
that the relative ramification index is one. The residue fields are finite
and hence perfect; this is the ordinary unramified condition. The conversion
is an arithmetic theorem used when proving these targets, not a newly
assumed certificate. No Galois hypothesis is added to those four assertions.
The last assertion explicitly requires an abelian Galois extension.

## The five assertions

1. `UnramifiedUnitNorms` says that the image of every `U_E^n` under the
   actual norm is exactly `U_F^n`, for all natural `n`, including zero.
   Positive levels use the trace description of norm on successive unit
   quotients and completeness. At zero, surjectivity of the residue-field
   norm is additionally used; it holds for the finite residue fields here.

2. `UnramifiedNormMembership` says that an element of `F.Carrier^x` is a
   norm exactly when its normalized order is divisible by `[E:F]`. The
   order is evaluated only on field units, so the separate convention
   `ord(0) = 0` is irrelevant.

3. `UnramifiedCyclicNormQuotient` asserts a continuous multiplicative
   equivalence from the actual norm quotient to the additive cyclic group
   `ZMod [E:F]`, written multiplicatively. Its value on the class of `a` is
   `ord_F(a)` modulo the degree. The finite cyclic target is explicitly
   discrete. The source retains its original quotient topology. The field
   degree is positive, including degree one, where both quotient groups
   are trivial. This is the valuation description of the quotient; it
   introduces no Galois automorphism or Frobenius lift.

4. `UnramifiedNormCharacterCriterion` uses the existing
   `HarmonicAnalysis.Quasicharacter`, a continuous homomorphism to the usual
   complex unit group. It says that triviality on all norms is equivalent
   to the existence of a unique `z : Complex^x` with `z^[E:F] = 1` such that
   `chi(a) = z^ord_F(a)` for every field unit `a`. The exponent on the
   right is an integer. Neither unitarity nor finite image is assumed of
   `chi`; the norm-triviality condition forces them in this finite quotient.
   Uniqueness of `z` follows by evaluation on any element of order one;
   the statement does not choose that element.

5. `AbelianUnitNormIndex` takes the inverse image of the full norm subgroup
   under the actual inclusion `T.unitSubgroup.subtype`. Its index in
   `U_F` is the relative ramification index. Lean states the equivalent
   natural-number equation
   `[U_F : U_F intersect N(E^x)] * e(F/Q_p) = e(E/Q_p)`.
   The norm order formula identifies that intersection with `N(U_E)`.
   This equation concerns the norm quotient of units, not the index of
   `N(U_E)` in all of `F^x`, which would be infinite.

`UnitNormTheorems` is the conjunction of these five proposition definitions.
No one of them is an assumption used to define another or supplied as a
field of a purported constructed reciprocity map.

## Original-source correspondence and derived content

Jean-Pierre Serre, *Local Fields*, English translation, GTM 67 (1979),
Chapter V, Section 2, Propositions 1-3, Corollary, Remarks and Exercise,
printed pages 81-82 (retained PDF pages 88-89), is the primary source.
Worker 10 read these original pages together with the chapter introduction
and the following norm calculations (PDF pages 87-94). Proposition 3(a)
gives surjectivity on all positive unit levels. Its part (b) and the following
finite-residue-field remark give the level-zero assertion. Part (c) gives
the cyclic valuation factor in the norm quotient; the residue norm factor
is trivial here. The exercise records the extension to non-Galois
unramified extensions. The actual finite p-adic setting also makes every
unramified extension Galois, but that fact need not be assumed in the target.

Chapter XIII, Section 4, Propositions 8-13, printed pages 196-198 (retained
PDF pages 201-203), read previously in the original, supplies finite abelian
reciprocity and its unit/inertia interpretation. Together with the norm
order formula and the local degree formula it yields the unit norm index
in item 5: the full norm quotient has size `[E:F]`, its order quotient
has size the relative residue degree, and the kernel therefore has size
the relative ramification index. This is a derived consequence, not a
claim that Serre labels precisely the displayed Lean equation as a theorem.

Items 2-4 make the quotient description explicit. Item 2 expresses its
kernel; item 3 specifies its canonical order map and the quotient topology;
item 4 is the elementary character description of that finite cyclic
quotient. These are derived formulations of the source's norm quotient,
not additional quoted results. The topology in item 3 uses continuity
and openness of normalized order with the unit kernel in the local
valuation topology.

Serre uses arithmetic Frobenius for reciprocity. This pair only uses
normalized order, norm subgroups, and their character quotients. When the
cyclic quotient is identified with a Galois group using this project's
geometric reciprocity, the class of order one corresponds to geometric
Frobenius. Inverting Serre's reciprocity changes the Frobenius generator,
not these norm kernels, unit images, indices, or character criterion.
The actual finite-field Frobenius and residue/inertia exact-sequence
statements remain the existing arithmetic tasks; this contribution does
not reimplement them.

Registered source: `serre-1979-local-fields`, retained original
`C:/Central-Library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

## Library dependencies and scope

The mathematical imports are the published
`Langlands.ClassFieldTheory.Local.Units`, `Langlands.ClassFieldTheory.Local.Norms` and
`Langlands.HarmonicAnalysis.Basic`, with their existing field and
normalization prerequisites. They are present in Library commit
`843c574c920aa9926ab56adf662c74b3cd4ed0e1`. Mathlib supplies actual algebra
norms, abelian Galois predicates, subgroup indices, complex units, finite
cyclic groups and continuous multiplicative equivalences.

The pinned environment is Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`, environment
`2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`.
Higher, upper-numbered ramification transport and equality of multiplicative
and Artin conductors are separate remaining local CFT targets. This family
does not assert that those obligations or the whole statement task are complete.

## Import-path preservation

Worker 63 updated only the two construction-module imports to their canonical
`Langlands.ClassFieldTheory.Local` paths during the topic migration based on
`c139df9ce67284be1bc963c2de5fbebd90214dda`. Worker 10 remains the
author of this statement pair. Every proposition body, full universe and instance
telescope, conjunction and normalization is unchanged. This file stays at its
existing path. See the [declaration-preservation ledger](Completion.md#topic-hierarchy-migration-ledger).
