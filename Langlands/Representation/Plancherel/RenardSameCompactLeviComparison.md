# Cartan comparison inside the same compact Levi intersection

Worker 454. This internal definition unit records the comparison obligations
for the standard Levi groups using the fixed geometric compact subgroup of
the ambient group. It constructs the conditional norm-quotient, chamber and
representative equivalences. It does not assert a structural inheritance
theorem for weak apartment data.

## Fixed groups, torus, compact subgroup and valuation

Use any nonarchimedean local field `F`, without characteristic restrictions,
the actual affine group scheme `G`, the actual commutative group scheme `S`,
and `i : S → G` with its monomorphism instance. Fix
`D : KPApartmentData i (localFieldOrder F)`, `x : D.Apartment`,
the cocharacter `ν`, an actual group scheme `Z`, and `s : S → Z` with
`h : Bijective (restrictionEvaluation s)`.

For every character subset `J`, all Levi objects are the existing actual
representatives:

- `M_J = Standard.leviScheme i ν J`, included by `Standard.leviHom i ν J`;
- `iM = Standard.leviTorusHom i ν J`, the same torus factored through that
  representative, whose composite with the inclusion is `i`;
- `KM = D.specialCompactLeviSubgroup ν J x`, the inverse image of
  `K₀ = D.specialCompactSubgroup x` under the actual rational-point inclusion.

The imported `specialCompactLeviSubgroup_map` identifies the image of `KM`
with exactly `K₀ ⊓ standardLeviPoints i ν J` in `G(F)`. No separate subgroup
is chosen in `M_J(F)`. The torus adapter preserves maximal splitness when
`i` is maximal split. These are algebraic adapters and do not prove that
`KM` is a special maximal compact subgroup.
The closed standard Levi inclusion supplies the local affine-group
instance through the existing `IsClosedSubgroup.isAffineHom` lemma.

The local comparison also fixes `jM : Z → M_J`. Write
`ZdomM = dominantCentralizer iM ν s h`. Both the ambient and Levi
chambers use precisely the same `centralizerValuation s h` on the same
`Z(F)`, the same `rationalCommonNormKernel Z = Z(F)^1`, and the same
actual image lattice. Only the positive-root inequalities change.
Their sign remains the corrected positive character order:
`0 ≤ eval S a (centralizerValuation s h z).toAdd`.
The Levi chamber is `dominantValuationImage iM ν s h`; no full
cocharacter parametrization is imposed.

## Comparison properties and conditional equivalences

`HasSameCompactLeviCoverage` requires every point of the actual `M_J(F)`
to have the same `KM` double coset as `jM(z)` for an actual `z ∈ ZdomM`.
`HasSameCompactLeviClassification` requires equality of these double cosets
for `z,z' ∈ ZdomM` if and only if `z' * z⁻¹ ∈ Z(F)^1`.
`SameCompactLeviCartanComparison` conjoins the two requirements.
The induced relation is literal equality of actual double cosets, with no
assertion that coverage alone identifies it with a kernel.

`sameCompactLeviNormEquiv` applies the existing
`RestrictedRightQuotient.doubleCosetEquiv` to that coverage and
classification. Thus it includes well-definedness and bijectivity for
the existing restricted right quotient `DominantNormQuotient iM ν s h`.
Its class formula sends `z` to the double coset of the same `jM(z)`.
`sameCompactLeviChamberEquiv` composes with the inverse of the existing
norm-quotient/chamber equivalence; its value formula sends the actual
value of `z` to that same double coset.

`sameCompactLeviSectionMap` sends any specified actual set `A ⊆ Z(F)`
to its `KM` double cosets under `jM`. Given the comparison and
`IsDominantValuationSection ZdomM A`, its bijectivity lemma proves this
map bijective. Injectivity uses the supplied classification and injectivity
of the valuation section. Surjectivity uses coverage, selects the point of
`A` with the same value, and uses classification to identify the double
cosets. `sameCompactLeviSectionEquiv` packages exactly this map with its
application formula.

The three subset lemmas use an explicit positive-root containment
`positiveRelativeRoots iM ν ⊆ positiveRelativeRoots i ν`. Restricting
the inequalities proves containment of the ambient dominant set and of
the positive uniformizer set in their Levi counterparts. Intersecting
the same `C0 S s * F0` with the two chambers gives the containment of
their `tildeC0Plus` sets. The lemmas do not prove the root containment.

## Standard-Levi compatibility property

`SpecialCompactStandardLeviCompatibility D x ν s h j` quantifies over
every `J ⊆ simpleRelativeRoots i ν` and requires an actual factor
`jM : Z → M_J` satisfying all of the following:

- `jM` is closed and represents the whole actual centralizer of `iM`
  on all test schemes;
- `jM` composed with the standard Levi inclusion is the fixed `j : Z → G`,
  and `s ≫ jM = iM`;
- Levi positive roots are ambient positive roots;
- the exact `SameCompactLeviCartanComparison` above holds;
- `DominantCentralizerLatticeConclusions iM ν s h` holds.

These identities keep the centralizer, torus factor, uniformizer subgroup
`C0 S s`, full lattice, residue quotient and norm kernel identical across
the comparisons. The final lattice predicate retains finite full
transversals, dominant sections of `(C0 S s * F0) ∩ ZdomM`, finite
positive product covers and the separate consequences of a
chamber-compatible transversal. Any full transversal is eligible for
each chamber cut. The property does not require a simultaneous rectangular
transversal for all Levis, or infer one from finite index.
Repeated product classes in a finite cover remain separate from the
bijection supplied by an actual valuation section.

## Scope and provenance

All proofs here are elementary conditional transports of existing Library
definitions. No source-facing Cartan or Levi inheritance theorem is proved.
The comparison constructors reuse the existing restricted quotient and
valuation/chamber equivalence. The section and subset proofs follow the
explicit hypotheses as described above.

The motivating source is David Renard, *Représentations des groupes
réductifs p-adiques*, 9 July 2026 edition, registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
V.3.23, printed page 117/PDF123, defines the full transversal and its
dominant intersection and separately makes a rectangular choice.
V.5.1(4),(5), printed page 122/PDF128, gives the Cartan decomposition
and retains the same `K₀ ∩ M` inside each standard Levi.
The present property isolates its Cartan/lattice comparison obligations;
the other adapted-compact properties remain with the structural sibling.
The positive normalization is inherited from the paired
`CentralizerValuation` modules and their mandatory KP correction sources.

In the intended structural specialization, `G` is connected reductive,
`i` is maximal split, `ν` is generic, `j` represents its actual centralizer
and `s ≫ j = i`, and `x` is an actual special vertex for explicitly
valid corrected building data. These hypotheses and that validity are
not supplied by the weak `KPApartmentData` parameter. A future global
statement must retain them explicitly. This unit asserts neither
universal validity or existence nor compactness, maximality, inherited
apartments, minimal-parabolic comparison or any KP parahoric/`Z(F)^0`
identification. It does not complete the host task.
