# The norm quotient of a separate finite abelian extension

The module `Langlands.ClassFieldTheory.Local.FiniteGeometricQuotient` proves one
supporting theorem,
`Langlands.LocalClassField.FiniteArtinSystemExistence.exists_quotientEquiv_geometricSymbol`.
It is a lemma used by the universe-zero proofs of the finite reciprocity
propositions. It proves no Library statement on its own. Its only import is the
published module `Langlands.ClassFieldTheory.Local.FiniteArtinSystemExistenceProof`.

## Statement

Fix a prime `p`, a field `F : PadicField.{u} p`, and a field `D : Type u` in the
same universe as `F.Carrier`, with `[Algebra F.Carrier D]`,
`[FiniteDimensional F.Carrier D]` and `[IsAbelianGalois F.Carrier D]`. The field
`D` is an arbitrary field, not a subfield of an algebraic closure. Let
`geometricSymbol F D : F.Carrierˣ →* Gal(D/F.Carrier)` be the Library's
geometric finite Artin symbol, the arithmetic `artinSymbol` of the inverse unit.

Take any topology on `F.Carrier`, given as an instance argument, for which
`geometricSymbol F D` is continuous on `F.Carrierˣ` (hypothesis `hc`). Then there
is a continuous multiplicative equivalence

`r : F.Carrierˣ ⧸ (Units.map (Algebra.norm F.Carrier (S := D))).range ≃ₜ* Gal(D/F.Carrier)`

with `r (QuotientGroup.mk a) = geometricSymbol F D a` for every `a : F.Carrierˣ`.
The quotient has Mathlib's quotient topology from the unit group's topology. The
Galois group has the Krull topology.

## Proof

1. **The algebraic equivalence.** The Library theorem `ker_geometricSymbol` says
   the kernel of `geometricSymbol F D` is `normSubgroup F.Carrier D`. That
   subgroup is by definition the range of `normUnits F.Carrier D`, which is the
   range of `Units.map (Algebra.norm F.Carrier)`. So
   `QuotientGroup.quotientMulEquivOfEq` turns the norm quotient into the
   quotient by the kernel. Then `QuotientGroup.quotientKerEquivOfSurjective`,
   with the Library theorem `geometricSymbol_surjective`, gives a
   multiplicative equivalence `e` onto `Gal(D/F.Carrier)`. On the class of `a`
   it takes the value `geometricSymbol F D a`. This holds by `rfl`.
2. **The forward map is continuous.** `QuotientGroup.mk` is a quotient map
   (`QuotientGroup.isQuotientMap_mk`). So `e` is continuous exactly when
   `a ↦ e (QuotientGroup.mk a)` is continuous. By step 1 this map is
   `geometricSymbol F D`, which is continuous by `hc`.
3. **The inverse map is continuous.** `D/F.Carrier` is finite-dimensional, so
   Mathlib's instance `krullTopology_discreteTopology_of_finiteDimensional`
   makes the Krull topology on `Gal(D/F.Carrier)` discrete. Every map out of a
   discrete space is continuous (`continuous_of_discreteTopology`).

The witness `r` is `e` with these two continuity proofs. Its value on classes is
step 1.

## Scope and provenance

This is an internal lemma for the route of Task 7335. The Library's
`Langlands.LocalClassField.finiteNormResidueEquiv` (module `FiniteArtin`) uses the
same construction, but only for an extension `L : FiniteAbelianExtension K`
inside an algebraic closure. This lemma uses it for an extension given as a
separate field, with an arbitrary topology on the base field. It does not show
that `geometricSymbol F D` is continuous: `hc` must be supplied, for example by
the Library theorem `continuous_geometricArtin`. The mathematical content,
finite reciprocity as an isomorphism from the norm quotient onto the Galois
group, is Serre, *Local Fields*, XIII.4, Proposition 8 and its corollary
(source `serre-1979-local-fields`), stated in the geometric convention of the
target [`FiniteReciprocityStatement`](FiniteReciprocityStatement.md).

The module compiled without errors or warnings in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`). Worker 56 authored it.
