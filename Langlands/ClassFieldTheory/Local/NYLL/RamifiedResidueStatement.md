# Finite ramified residue bridge targets

Worker 384 authored these derived statement targets. Worker 109 contributed
the explicit relative unramifiedness interface. Worker 70 contributed the
same-family restriction requirement and downstream interface coordination.
The imported constructions retain their existing authorship. This pair
defines propositions; it proves none of the bridge assertions.

All five declarations are in `Langlands.LocalClassField.NYLL`. The prime is
arbitrary, and the base and extension are `PadicField.{u} p` and
`PadicField.{v} p` with independent universes. Their actual `Algebra` and
compatible `Padic p` scalar tower are explicit. Finiteness over the base
follows from `FiniteDimensional.right (Padic p) F.Carrier E.Carrier`;
there is no extra finiteness certificate in these statements. Every
topological realization supplied to a target is arbitrary.

## Actual field, maps, and structural targets

Write `U = finiteInertiaPadicField F E TF`. This is the literal subtype
`finiteInertiaField F E TF` inside `E.Carrier`, the fixed field of the actual
`finiteInertiaSubgroup F E TF`. The latter uses the spectral residue action
obtained from the norm constructed from `TF`; its definition is unchanged.
The statements quantify over `TU : U.TopologicalData` and, where used,
`TE : E.TopologicalData`.

`FiniteInertiaFieldUnramifiedStatement` asserts

```text
letI := PadicField.TopologicalData.relativeIntegerAlgebra TF TU
(IsLocalRing.maximalIdeal TU.Integers).ramificationIdx TF.Integers = 1.
```

The scalar structure is that of the actual restricted field inclusion
`F.Carrier → U.Carrier`. Thus this is the relative index `e(U/F) = 1`.
The residue fields are finite, hence their extension is separable, so this
index condition is the unramifiedness condition in this setting. It is not
an equality between the absolute ramification indices of `TF` and `TU`.
No residue isomorphism, compatibility of chosen valuations, or reciprocity
normalization is an input.

`FiniteInertiaResidueMapBijectiveStatement` asserts bijectivity of

```text
finiteInertiaResidueMap F E TF TU TE : TU.ResidueField →+* TE.ResidueField.
```

This is exactly `relativeResidueMap TU TE`, induced by the actual integer
inclusion `finiteInertiaIntegerMap`. Its bijectivity says that this specific
map is a residue-field isomorphism; the proposition does not quantify over
a replacement isomorphism or choose an inverse map. Its representative law
is the existing `relativeResidueMap_residue`, and the integer map has the
existing `relativeIntegerMap_coe` law.

`FiniteInertiaResidueRestrictionStatement` states the action square

```text
j(res_U(restrict σ)(y)) = res_E(σ)(j(y)).
```

Here `j` is exactly the displayed supplied residue map,
`restrict = finiteInertiaRestriction F E TF`,
`res_U = finiteInertiaResidueAction F E TF TU`, and
`res_E = Ramification.Padic.residueHom TE F.Carrier`. Both actions come
from the actual field automorphisms on their supplied integer rings and
their actual residue quotients. The statement needs no chosen lift of a
residue element.

## Supplied action and valuation comparison

`SuppliedInverseResiduePowerStatement` is the missing concrete comparison
between the supplied residue action and the supplied discrete valuation.
For every natural number `q` and actual `σ : Gal(E.Carrier/F.Carrier)`,
it says that inverse action by `res_E(σ)` is `y ↦ y^q` on
`TE.ResidueField` if and only if

```text
∀ x : E.Carrier, TE.discreteValuation x ≤ 1 →
  TE.discreteValuation (σ.symm x - x^q) < 1.
```

This comparison does not require abelian or Galois hypotheses. The
automorphism group and scalar tower suffice. It does not require `TF`,
because its exponent is an arbitrary natural number and the supplied
action uses the actual base-field algebra structure.

The underlying generic residue-equality criterion belongs to the separate
statement task `ced69a72-6b38-4ee1-af85-28233ec4f9ee`, intended declaration
`SuppliedResidueCongruenceStatement`. This pair does not duplicate that
criterion or claim that its task is already published. Its later proof
should reuse that criterion and
`PadicField.TopologicalData.mem_integers_iff_discreteValuation_le_one`
from `Langlands.HarmonicAnalysis.Conductor`, together with the actual
representative formula for `residueHom` and `map_pow`. Inversion in
`RingAut` corresponds to `σ.symm` because `residueHom` is a group
homomorphism. These facts explain the proposed comparison, rather than
assuming it as a compatibility certificate.

## One-family normalization transfer

`RamifiedGeometricNormalizationTransferStatement` quantifies over one
parameter `Artin`. For each `D : PadicField.{v} p` equipped with an
`F.Carrier` algebra, its compatible p-adic tower and an abelian Galois
certificate, and each `TD : D.TopologicalData`, its value is a homomorphism

```text
Artin D TD : F.Carrierˣ →* Gal(D.Carrier/F.Carrier).
```

The same parameter supplies every value below, with the same base `F`
and supplied `TF`. The family's first premise is its geometric
normalization at all relatively unramified such `D`, with the displayed
relative index equal to one and exponent `TF.residueCardinality`.
The second premise is the equality of homomorphisms

```text
(finiteInertiaRestriction F E TF).comp (Artin E TE) = Artin U TU.
```

The abelian Galois instance for this actual `U` is the published
`finiteInertiaField_isAbelianGalois F E TF`, installed locally. The
conclusion is exactly

```text
∀ (a : F.Carrierˣ), TF.ord (a : F.Carrier) = 1 →
  ∀ x : E.Carrier, TE.discreteValuation x ≤ 1 →
    TE.discreteValuation
      ((Artin E TE a).symm x - x ^ TF.residueCardinality) < 1.
```

There is no unramifiedness premise on `E/F` in this conclusion. The
unramified premise is applied to `U/F` using the structural target, and
the residue inclusion and restriction square carry the resulting power
formula to `E`. Surjectivity of the actual residue inclusion permits an
arbitrary residue class of `E` to be represented from `U`. The supplied
action/valuation comparison converts between the power formula and the
displayed inequality. This describes the intended derived proof route;
no such proof is implemented here.

The parameter is not a pair of unrelated maps, and no clause assumes the
ramified conclusion. The structural assertions and the action/valuation
comparison are separate unconditional targets, rather than extra
assumptions in this transfer proposition. The final specialization to the
named NYLL family belongs to the later proof unit. The family's universe
is the same `v` for `E` and its actual subtype `U`, with independent base
universe `u`; its Type 0 specialization is available to the NYLL port.
The index premise matches Worker 109's coordinated unramified interface.

## Existing results and remaining gaps

The defining adapter
`Langlands.ClassFieldTheory.Local.NYLL.FiniteInertiaField` supplies all
maps in these statements, including the actual field restriction law
`finiteInertiaRestriction_apply`. No new comparison map is needed to
form these supplied-data targets.

The following published results are reused in the architecture:

- `Langlands.LocalGalois.residueHom_restrict` in
  `Langlands.Galois.Local.AbsoluteProof` is already the restriction square
  for the spectral integer and residue fields and any normal intermediate
  field. This pair does not restate it. The supplied square above has
  different rings and actions and remains to be proved.
- `Langlands.LocalClassField.ResidueNormalization.hasGeometricResidueAction_iff_inverse_power`
  in `Langlands.ClassFieldTheory.Local.ResidueNormalization` already
  identifies geometric Frobenius with inverse-cardinality power action
  on the spectral residue field. This pair does not duplicate that
  geometric-Frobenius theorem or assume an identification of its residue
  field with `TE.ResidueField`.
- `relativeIntegerMap`, `relativeResidueMap`, their representative and
  composition laws, their explicit scalar structures, and their
  canonical specializations are already in
  `Langlands.LocalField.RelativeIntegers`.
- `Ramification.Padic.integerAutHom` and `Ramification.Padic.residueHom`
  already construct the actions on arbitrary supplied realizations.

The proof of the structural targets must still justify why the field
defined using the spectral inertia kernel has the asserted properties
for all supplied `TU` and `TE`. This pair does not silently identify
spectral and supplied objects. A proof may compare their valuation
rings using existing uniqueness and integral-closure results, or prove
the supplied statements directly. Any additional map actually needed
for a proof must first have its own accepted definition.

The generic congruence task and these five targets are separate proof
obligations. There is no construction or proof of an Artin map here.
This pair makes no assertion about a common algebraic closure, a
coherent absolute reciprocity system, class formations, or the
cohomological reciprocity construction.

## Original-source correspondence

These are derived interfaces for the finite supplied-data host clauses,
not a port or literal translation of an external Lean declaration.
Worker 384 read the following originals in Jean-Pierre Serre,
*Local Fields* (1979), registered `serre-1979-local-fields`, SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`,
retained at `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`:

- II.2, Proposition 3 and Corollaries 1–4, printed pages 28–30,
  PDF pages 36–38: the unique prolongation of a complete discrete
  valuation, finite integral closure, and invariance under conjugation.
- III.5, Theorems 1–3 and Corollaries 1–3, printed pages 53–55,
  PDF pages 60–62: unramified extensions, their residue embeddings,
  and the maximal unramified subextension. The residue fields here
  are finite, so the full residue extension is separable.
- XIII.4, Propositions 8, 10, 12, 13 and the corollary to Proposition 13,
  printed pages 196–198, PDF pages 201–203: finite reciprocity,
  the functorial diagrams, unramified Frobenius normalization, and
  the use of the inertia fixed field in the ramified case.

Worker 384 also read the Local Fields entries of the registered author
corrections `serre-book-corrections-2019`, PDF pages 2–3, retained at
`/home/taskhub/pilot/literature/Jean-Pierre Serre — Corrections to J-P. Serre's books (2019).pdf`.
None of those corrections changes the passages cited above.

Serre uses arithmetic reciprocity. The host convention inverts its
values; hence the inverse automorphism in the host formula acts by
the `q_F` power, with `q_F = TF.residueCardinality`. This pair keeps
that convention and the arbitrary supplied data exactly.

The approved environment is Lean 4.34.0 with Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`,
environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`.
Compilation and complete declaration inspection are development checks;
independent statement acceptance and Integrator publication remain
required before a proof child may name these targets.
