# Henselian valuations and unique extension to algebraic extensions

Module `Nyll.ValuedFieldTheory.Valuation.Henselian.UniqueAlgebraicExtensions`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file proves the unique-extension criterion: a nonarchimedean valuation is henselian exactly when its valuation ring extends uniquely to every algebraic extension. Valuations are regarded up to equivalence, so uniqueness is stated as uniqueness of the extended valuation subring.

## Definitions

- `HasUniqueValuationSubringExtension V` (for an extension L of K): there is exactly one valuation subring W of L whose valuation extends that of V (`HasExtension`).
- `HasUniqueAlgebraicValuationSubringExtensions V`: the previous condition holds for every algebraic extension L of K in the same universe as K.

## Main results

- `monicResidualCoprimeFactorLifting_of_unique_algebraic_extensions`: for any valuation subring V, unique extensions imply monic coprime factor lifting. A monic polynomial is factored into monic irreducibles over V, which a partition lemma from an earlier file distributes along the coprime residual factorization.
- `henselFactorization_of_unique_algebraic_valuationSubring_extensions`: for any V, unique extensions imply `HenselFactorizationProperty V`, through the primitive-irreducible reduction property of the file on unique extension and primitive reductions.
- `henselianUniqueExtension_unique_algebraic_valuationSubring_extension_of_henselian` and its version for all L at once: if v is a real-valued absolute value on K, nonarchimedean in the library's sense, and the valuation of its unit ball O satisfies `HenselianValuationByFactorization`, then O has a unique extension valuation subring on every algebraic extension L.
- `henselianUniqueExtension_henselian_of_unique_algebraic_valuationSubring_extensions`: the converse for such v.
- `henselianUniqueExtension_henselian_iff_unique_algebraic_valuationSubring_extensions`: the equivalence.

## Proof

Existence of an extension comes from the norm-formula theorem `normFormula_algebraic_extension`. For uniqueness, the Hensel factorization property shows that for every z ∈ L, z or z⁻¹ is integral over O; any extension valuation ring is then the integral closure of O in L.

## Points to watch

- "Henselian" here is the library's `HenselianValuationByFactorization`, a Hensel factorization condition, not Mathlib's `HenselianRing`.
- The forward direction and the equivalence are stated only for valuation rings of real-valued absolute values, hence rank at most one; the converse implications hold for an arbitrary valuation subring V.
- In `HasUniqueAlgebraicValuationSubringExtensions`, hence in the version for all L, the converse and the equivalence, algebraic extensions are quantified over the universe of K; the forward theorem for a single L allows K and L in different universes.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/Henselian/UniqueAlgebraicExtensions.lean`: the Lean file is the source byte for byte (SHA-256 `1b80c36bda9dee2048cf565e2460b694a8fc81b5b9a1d5a00d44906ab08a369b`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
