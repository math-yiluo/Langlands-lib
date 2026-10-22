# Residue field of the actual finite-place completion

Author: Worker 65. Task `a50968a2-52c5-44dd-b391-2c43b1abfafc`, revision 1.

## Objects, universes and instances

Let `K : Type u` be any number field and let
`v : Langlands.Global.FinitePlace K` be a nonzero prime ideal of its ring of
integers. The completion is the published actual type
`Langlands.Global.FiniteCompletion K v`, namely Mathlib's `v.adicCompletion K`.
Its norm is the canonical adic norm. The norm valuation ring is precisely
`Langlands.LocalGalois.baseIntegers (FiniteCompletion K v)`; no independent
valuation ring or residue field is supplied as data.

The module opens the `Valued` scope to expose Mathlib's canonical
nontrivially normed field instance and the corresponding ultrametric instance.
It does not install an alternative topology or rescale the norm. Mathlib's
normalization uses `Ideal.absNorm v.asIdeal` as the exponential base: a
uniformizer has norm the inverse of this cardinality. The global field has
no additional topology. All carriers, including the completed residue field
and the quotient of global integers, retain universe `u`.

## Construction and intrinsic proofs

`norm_algebraMap_le_one` applies Mathlib's actual adic norm bound to a global
integer. This is the membership proof for `integersMap`, the ring homomorphism
from global integers into the completed norm valuation ring. Its underlying
value is the actual algebra map into the completion (`integersMap_coe`).

`residueMap` composes `integersMap` with `IsLocalRing.residue`.
The maximal ideal of the norm valuation ring consists exactly of the elements
of norm less than one. Mathlib's `NumberField.FinitePlace.norm_lt_one_iff_mem`
therefore proves `residueMap_eq_zero_iff` and the exact identity
`ker_residueMap : RingHom.ker (residueMap K v) = v.asIdeal`.

For surjectivity, `exists_integer_norm_sub_lt_one` first approximates an
integral completed element `x` by a field element `b` with error of norm
less than one, using density of the actual field embedding. The ultrametric
inequality implies that `b` is integral at `v`. The Dedekind-domain
approximation theorem `exists_valuation_sub_lt_of_integer` then supplies a
global integer `a` whose difference from `b` has valuation less than one.
The comparison between the adic valuation and canonical norm converts this
bound into a norm bound. A second ultrametric inequality gives
`norm (x - a) < 1`. Hence `x` and `a` have the same residue. Applying this to
an arbitrary residue representative proves `residueMap_surjective`.
All membership, kernel and surjectivity obligations are proved in the file.

`residueEquiv` composes quotient transport along the proved kernel identity
with Mathlib's first isomorphism theorem for a surjective ring homomorphism.
Its domain is exactly `RingOfIntegers K ⧸ v.asIdeal` and its codomain is exactly
`IsLocalRing.ResidueField (LocalGalois.baseIntegers (FiniteCompletion K v))`.
The evaluation theorem `residueEquiv_mk` states on every global integer that
this equivalence agrees with embedding and reduction. Thus the construction
identifies the prescribed maps, rather than choosing an unspecified finite-field
isomorphism.

The instance `finite_residueField` is transported from the known finite
quotient through this equivalence. The cardinality identity
`card_residueField` uses `Nat.card` and `Ideal.absNorm`, with no chosen
enumeration of the residue field.
`ringChar_residueField` transports the characteristic through the constructed
ring equivalence. The cardinality bound `one_lt_card_residueField` reuses
Mathlib's bound for the ideal norm. `prime_ringChar_residueField` and
`absNorm_eq_ringChar_pow` reuse Mathlib's characteristic and cardinality
theorems for finite fields. They introduce no characteristic or cardinality
assumptions. Every proof is given in this module, with no proof holes and no
added axioms.

## Source correspondence

Jean-Pierre Serre, *Local Fields*, Springer, 1979, Chapter II, Section 1,
printed pp.26-27 (PDF pp.34-35), in the paragraphs preceding Proposition 1:
the valuation ring of the completion is the closure of the original discrete
valuation ring; the quotients by powers of a uniformizer agree, in particular
the residue fields agree ("In particular, the residue fields of A and Â
coincide", printed p.27). Worker 65 read these pages directly in the retained
original `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, the
file of the registered source `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

The Lean construction is a derived specialization and explicit realization.
Serre's assertion is about the local discrete valuation ring before and after
completion. Here the source is the quotient of global integers; the explicit
Dedekind-domain approximation argument and kernel computation supply that
additional identification. The proof does not import an assumed residue
comparison from Serre as an axiom.

Pinned Mathlib sources used directly:

- `NumberTheory/NumberField/Completion/FinitePlace.lean`,
  `NumberField.FinitePlace.norm_le_one`, `norm_lt_one_iff_mem`,
  `NumberField.HeightOneSpectrum.one_lt_absNorm`, and the canonical norm
  `NumberField.HeightOneSpectrum.instNormedFieldValuedAdicCompletion`;
- `RingTheory/DedekindDomain/AdicValuation.lean`,
  `IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap`,
  `algebraMap_adicCompletion`, `exists_valuation_sub_lt_of_integer` and
  `valuedAdicCompletion_eq_valuation'`;
- `Topology/Algebra/Valued/NormedValued.lean`, the scoped instances
  `Valued.toNormedField` and `Valued.toNontriviallyNormedField`, the
  ultrametric instance, and `Valued.toNormedField.norm_le_one_iff` and
  `norm_lt_one_iff`;
- `Analysis/Normed/Group/Ultra.lean`, `IsUltrametricDist.norm_add_le_max`;
- `RingTheory/Valuation/ValuationSubring.lean`,
  `Valuation.mem_maximalIdeal_iff`;
- `RingTheory/LocalRing/ResidueField/Basic.lean`, the residue map, the kernel
  criterion `IsLocalRing.residue_eq_zero_iff` and
  `IsLocalRing.residue_surjective`;
- `RingTheory/Ideal/Quotient/Defs.lean`, `Ideal.quotEquivOfEq`;
- `RingTheory/Ideal/Quotient/Operations.lean`,
  `RingHom.quotientKerEquivOfSurjective` and its evaluation on quotient classes;
- `RingTheory/Ideal/Norm/AbsNorm.lean`, the definition of `Ideal.absNorm` as
  quotient cardinality;
- `Algebra/CharP/Algebra.lean`, `RingHom.charP_iff`, and
  `Algebra/CharP/Lemmas.lean`, `CharP.prime_ringChar`;
- `FieldTheory/Finite/Basic.lean`, `FiniteField.card`, for the positive
  prime-power exponent.

These source declarations and their proofs were inspected. They are reused
from Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.

## Published dependencies and remaining boundaries

The project imports are the published `Langlands.Global.Adelic` and
`Langlands.Galois.Local.SpectralDefinitions`, read at Library commit
`30ceb5a0d89d8094c1663fc19f35416519b9a125`. Dependency map to published Lean
names:

- `Langlands.Global.FinitePlace K`, an abbreviation of
  `IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)`, and
  `Langlands.Global.FiniteCompletion K v`, an abbreviation of
  `v.adicCompletion K`, both from `Langlands/Global/Adelic.lean`, SHA256
  `b1b7213c47725ac26e0ce09b0e483e548c8a4e1f3fd4a4972cedb64b7ce8258e`;
- `Langlands.LocalGalois.baseIntegers`, the valuation subring of
  `NormedField.valuation`, from
  `Langlands/Galois/Local/SpectralDefinitions.lean`, SHA256
  `7b05ea4f6904f852d6870c3c323a42939d98c8e03bfc08fb7aa37a58d46e8d9a`.

No other project constructions or theorem assumptions are imported.

Development check record: in the project Lean service with environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), this module, with Lean source
SHA256 `d2ae565f5ad144e7002fdd17cd1fda9990934fa81de39ec6cae5fde502ac0f10`,
builds with no errors and no warnings. A private inspection file printed the
elaborated types of all sixteen declarations of the module, each with the
single universe parameter `u` of `K`. For `residueEquiv`, `residueEquiv_mk`,
`card_residueField`, `ringChar_residueField` and `absNorm_eq_ringChar_pow`,
`#print axioms` reports only `propext`, `Classical.choice` and `Quot.sound`.
The same file checks by `rfl` that the nontrivially normed field found under
`open scoped Valued` has as underlying normed field Mathlib's canonical
`NumberField.HeightOneSpectrum.instNormedFieldValuedAdicCompletion K v`. It
also checks that `residueEquiv K v` has exactly the type
`(NumberField.RingOfIntegers K ⧸ v.asIdeal) ≃+* IsLocalRing.ResidueField
(Langlands.LocalGalois.baseIntegers (Langlands.Global.FiniteCompletion K v))`.
These are development checks, not acceptance.

Downstream, the published `Langlands.GaloisRepresentation.residueCardinality v`
and `residueCharacteristic v` of `Langlands.Galois.CompatibleFamily` are by
definition `Ideal.absNorm v.asIdeal` and
`ringChar (NumberField.RingOfIntegers K ⧸ v.asIdeal)`. These are the
right-hand sides of `card_residueField` and `ringChar_residueField`. This
module does not import that file.

This module does not assert surjectivity of the absolute-Galois residue
homomorphism, choose a Frobenius lift, construct a Weil group, or prove the
existence of a compatible Galois family. Completion functoriality, completed
tensor products, norms and idele-class descent remain in the separate
`Langlands.Global.AdelicFunctoriality` scope, and local Weil-group assembly
for actual finite p-adic fields remains a separate construction. It does not
require or construct a finite-extension presentation over a p-adic field.
