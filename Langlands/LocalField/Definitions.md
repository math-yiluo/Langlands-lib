# P-adic fields as finite extensions

This definition layer packages arbitrary finite extensions of Mathlib's
`Padic p`, for every prime `p`. The algebraic interface and a certified
topological realization are separate. It asserts no local reciprocity or
Langlands correspondence.

## Algebraic data

`Langlands.PadicField p`, under `[Fact p.Prime]`, contains a carrier in an
arbitrary universe, a `Field`, an `Algebra (Padic p)` structure, and
`FiniteDimensional (Padic p)` on that carrier. The specified algebra map is
the embedding of the base field. A field is nontrivial, so its dimension over
the base cannot be zero. The field, algebra, and finiteness projections are
instances; there is no global topology or norm instance.

`PadicField.ofField K` packages any already supplied field, algebra, and finite
dimensionality instances. No Galois, normality, unramifiedness, or restriction
on the degree is imposed. The interface retains the base embedding rather
than quotienting fields by isomorphism.

## Canonical norm and topology

`canonicalNorm` is Mathlib's `spectralNorm (Padic p) F.Carrier`.
`canonicalNormedField` and `canonicalNormedAlgebra` reuse
`spectralNorm.nontriviallyNormedField` and `spectralNorm.normedAlgebra`.
These constructions already apply to every algebraic interface object.
They are explicit data; callers can install them with `letI`.

The norm convention is the extension of the usual base norm, so the image
of `p` has norm `p` to the power `-1`. This is the norm appropriate for a
normed algebra over `Padic p`. Mathlib proves its multiplicativity,
nonarchimedean inequality, existence, and uniqueness.

`canonicalTopology` is `moduleTopology (Padic p) F.Carrier`, the canonical
finite-dimensional vector-space topology. A choice of basis identifies it
with the product topology on a finite power of `Padic p`. The spectral norm
induces this topology by the existing finite-dimensional topology results
listed below; this module does not add a theorem expressing that equality.

`F.TopologicalData` explicitly contains a topology, a `ValuativeRel`, a
`ValuativeExtension (Padic p) F.Carrier` certificate, an
`IsModuleTopology (Padic p) F.Carrier` certificate, and an
`IsNonarchimedeanLocalField F.Carrier` certificate. `IsModuleTopology` says
that the supplied topology equals `canonicalTopology`. The local-field
certificate requires that the topology is valuative, is locally compact,
and has a nontrivial valuation. The valuative relation records a valuation
up to equivalence, without choosing a numerical value-group normalization.
`ValuativeExtension` requires the comparison relation on the base to be
exactly the pullback along the specified algebra map. Thus the valuation
data explicitly prolong the usual p-adic valuation.

Given `T : F.TopologicalData`, install its fields locally in this order:
`letI := T.topology`, `letI := T.valuativeRel`,
`letI := T.valuativeExtension`, `letI := T.moduleTopology`,
`letI := T.localField`. The resulting carrier works directly with Mathlib's
topological-field, integer-ring, and residue-field interfaces. The package
does not globally select one `T` when several are in scope.

The local-field certificate is a visible hypothesis of this data package.
It is not an axiom or a result derived in this module from finite
dimensionality. There is no construction of `F.TopologicalData` for general
`F` here. The separate spectral norm construction must not be mistaken for
such a construction.

`PadicField.rational p` is the degree-one algebraic example `Padic p` with
its identity algebra. `rationalTopologicalData p` uses the existing usual
topology, p-adic valuative relation, module-topology instance, and
`IsNonarchimedeanLocalField (Padic p)` instance. The identity base embedding
has valuative compatibility by reflexivity. Its other fields are supplied
by existing Mathlib instances, without new mathematical proof claims.

## Normalization

Serre's normalized local-field absolute value sends a uniformizer to
`q` to the power `-1`, where `q` is the residue-field cardinality. This
differs in general from `canonicalNorm`. If `e` is the ramification index,
`f` the residue degree, and `n = [F : Q_p] = e*f`, then the extended base
norm is `p^(-v_F(x)/e)`, whereas the normalized local-field absolute value
is `q^(-v_F(x))`, its `n`-th power. Here `v_F` is normalized to send a
uniformizer to `1`, and the displayed formulas concern nonzero `x`.
Both norms give the same topology.

These formulas explain conventions; this module does not formalize
ramification indices, residue degrees, their degree formula, or the
conversion between the two norms. In particular, it does not identify the
base-extending norm with the normalized absolute value for a general
extension. For `Q_p` the two conventions agree.

## Audit of the pinned Mathlib

The exact environment is `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`:
Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`,
and Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
There are no project mathematical dependencies.

| Topic | Existing pinned Mathlib support | Boundary of this contribution |
| --- | --- | --- |
| Extension norm | `Analysis/Normed/Unbundled/SpectralNorm.lean`: `spectralNorm_extends`, `isNonarchimedean_spectralNorm`, `spectralAlgNorm_mul`, `spectralMulAlgNorm`, `spectralNorm_unique`, `NormedAlgebra.norm_eq_spectralNorm`, and the explicit spectral normed structures. | The definitions directly reuse the constructors. No norm-existence or uniqueness theorem remains to be invented. |
| Completeness | `spectralNorm.completeSpace` proves completeness of the spectral uniform space for finite extensions. `FiniteDimensional.complete` in `Topology/Algebra/Module/FiniteDimension.lean`, re-exported by `Analysis/Normed/Module/FiniteDimension.lean`, handles finite-dimensional normed spaces over a complete base. `PadicNumbers.lean` has `CompleteSpace (Padic p)`. | No blanket completeness instance is installed on the bare algebraic carrier, which has no uniform space. |
| Canonical topology | `Topology/Algebra/Module/FiniteDimension.lean`: `isModuleTopologyOfFiniteDimensional`, `continuous_equivFun_basis`, and `LinearMap.continuous_of_finiteDimensional`. `IsModuleTopology.eq_moduleTopology'` and `eq_moduleTopology` identify the topology. | The topological package requires the module-topology certificate. No new equality theorem between the module and spectral topologies is submitted. |
| Local compactness | `NumberTheory/Padics/ProperSpace.lean` gives properness of `Padic p`. `FiniteDimensional.proper` proves properness for finite-dimensional normed spaces over a locally compact nontrivially normed field; it is deliberately not a general instance. | Thus local compactness for the spectral norm already follows from an existing theorem. Assembly of a compatible valuative relation and all fields of `TopologicalData` for arbitrary `F` remains unimplemented here. |
| General local fields | `NumberTheory/LocalField/Basic.lean`: `IsNonarchimedeanLocalField` and its instances for a topological division ring, compact integer ring, discrete valuation ring, discrete rank-one value group, and finite residue field. Completeness follows with a compatible additive uniformity. `valueGroupWithZeroIsoInt` gives the ordered value group with zero. | These consequences require the local-field certificate; this contribution does not use them to justify that certificate circularly. |
| Base field | `NumberTheory/Padics/LocalField.lean` supplies `IsNonarchimedeanLocalField (Padic p)`. `Padics/ValuativeRel.lean` supplies the relation from `Padic.mulValuation`, its compatibility, nontriviality, rank one, and valuative topology. | These instances construct `rationalTopologicalData`. |
| Valuation compatibility | `RingTheory/Valuation/ValuativeRel/Basic.lean` defines `ValuativeExtension` by reflection and preservation of comparisons along the algebra map. | This is an explicit field of `TopologicalData`; its arbitrary-extension construction remains to be assembled. |
| Residue field | The general local-field interface gives `Finite` for its residue field. `NumberTheory/Padics/RingHoms.lean`, `PadicInt.residueField`, identifies the residue field of `PadicInt p` with `ZMod p`. | The latter concerns the named p-adic integer ring. No transport identifying it with every integer-ring presentation is claimed. General `F` still needs the topological realization and residue-characteristic/degree identifications. |
| Normalization | `Padic.norm_p`, `Padic.valuation_p`, `Padic.norm_eq_zpow_neg_valuation`, `Padic.addValuation`, and `Padic.mulValuation` are in `PadicNumbers.lean`. General local fields have `valueGroupWithZeroIsoInt`; the spectral module also has `spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow`. | Integer value-group normalization already exists abstractly. This module provides no comparison with ramification/residue degrees or a `q`-normalized absolute value for arbitrary `F`. |

The remaining work is interface assembly and explicit comparison results,
not an assertion that Mathlib lacks norm extension, completeness, or
finite-dimensional local compactness. This is a source audit, not a claim
that no other relevant declarations exist anywhere in Mathlib.

## Original sources and correspondence

1. Guy Henniart, *Une preuve simple des conjectures de Langlands pour GL(n)
   sur un corps p-adique*, Inventiones mathematicae 139 (2000), 439-455,
   Section 1.1, page 439, opening two sentences.
   `literature_id`: `henniart-2000-simple-proof`.
   `content_sha256`: `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
   Source file: `C:/Central-Library/Henniart--Une preuve simple des conjectures de Langlands pour GL(n) sur un corps p-adique--2000.pdf`.
   Henniart fixes an arbitrary prime and a finite extension of `Q_p`.
   This is precisely the algebraic domain packaged by `PadicField`.
   His mention of the residue cardinality is not a supplied proof of
   residue-field finiteness in Lean.
2. Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg,
   Graduate Texts in Mathematics 67, Springer, 1979.
   `literature_id`: `serre-1979-local-fields`.
   `content_sha256`: `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
   Source file: `C:/Central-Library/Serre--Local Fields--1979.pdf`.
   Locators: Chapter II, Section 1, pages 26-28, especially Proposition 1,
   its `Q_p` example, and the normalization preceding Proposition 2;
   Section 2, Proposition 3 and Corollaries 1-4, pages 28-30;
   Section 5 opening, page 36.
   Section 1 supplies the valuation topology and the local compactness
   criterion. Section 2 identifies the finite-extension topology with the
   finite-dimensional product topology, establishes completeness and
   uniqueness of the prolonged valuation, and gives the degree and norm
   relations. Section 5 explains the absolute ramification index and
   `q = p^f`. These establish the mathematical conventions documented above.

The bundled interfaces are an implementation choice, not a verbatim
definition attributed to either author. The spectral construction and
module-topology representation come from the exact Mathlib modules cited
in the audit. This file states their role and the limits of their reuse.

## Validation boundary

The Lean file contains data definitions and constructors using existing
instances. It introduces no theorem statements, project axioms, or proof
placeholders. There is consequently no new proposition target to fingerprint.
Native compilation and the development `lean_check` for the entry declaration
`Langlands.PadicField` succeeded with no errors or warnings. The inspection
reported no declared or disallowed axioms, and only `propext`,
`Classical.choice`, and `Quot.sound` as module axioms.

Private usage diagnostics also checked installation of the spectral structures
against the existing completeness, properness, and module-topology results,
and installation of the topological package against the topological
division-ring, discrete valuation-ring, and finite residue-field instances.
The properness diagnostic additionally imports
`Mathlib.Analysis.Normed.Module.FiniteDimension`; the base residue-field
identification additionally imports `Mathlib.NumberTheory.Padics.RingHoms`.
These checks establish elaboration in the pinned environment. Independent
semantic review and publication establish acceptance of this definition layer.
