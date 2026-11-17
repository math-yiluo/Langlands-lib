# Existence of the universal Picard-zero family over a quasi-separated base: proof

Worker 1012, 17 November 2026.

## Result

`Langlands.AbelianScheme.relativeDualSchemeExistence` has type exactly
`Langlands.AbelianScheme.RelativeDualSchemeExistenceStatement.{u}`, imported by
Lean name from `Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeExistenceStatement`.
For every scheme `S : Scheme.{u}` with `QuasiSeparatedSpace S` and every
`A : AbelianScheme S`, it proves `HasDualScheme A`: there are an actual parameter
`P : Over S` and an actual rigidified family on it that is universal for geometric
Picard-zero classes on every test scheme of the fixed universe, including nonreduced
and non-quasi-separated test schemes. Each class is classified by a unique parameter
morphism. The proof adds no hypothesis and does not restrict test schemes. The
quasi-separatedness assumption stays on the base, as in the statement.

## Implemented proof

The proof composes four published unconditional theorems.

1. **Finite-type representer.** `finiteTypeSmoothFamilyAbelianRepresentability`
   (module `FiniteTypeSmoothFamilyAbelianRepresentabilityProof`) proves
   `FiniteTypeSmoothFamilyAbelianRepresentabilityStatement.{u}`. For every abelian
   scheme over `Spec R`, with `R` of finite type over `ℤ`, it supplies an abelian
   scheme `B` and a rigidified family on `B.X`. That family is universal for
   smooth-family algebraically trivial classes on all quasi-separated tests.
2. **Extension to arbitrary quasi-separated bases.**
   `smoothFamilyAbelianRepresentabilityOfFiniteType` (module
   `SmoothFamilyAbelianRepresentabilityOfFiniteTypeProof`) proves
   `FiniteTypeSmoothFamilyAbelianRepresentabilityStatement.{u} →
   SmoothFamilyAbelianRepresentabilityStatement.{u}`. Applied to step 1 and to the
   given `S` and `A`, it yields an abelian scheme `B` over `S`, a rigidified family
   `L : RigidifiedFamily A B.X` and the proof `hL` of
   `IsUniversalSmoothFamilyOnQuasiSeparatedTests A L`.
3. **Predicate comparison.** The helper lemma
   `universalPicardZeroOnQuasiSeparatedTests_of_smoothFamily` converts `hL` into
   `IsUniversalPicardZeroOnQuasiSeparatedTests A L` for the same parameter and the
   same family. It uses the published
   `smoothFamilyPicardZeroComparison : SmoothFamilyPicardZeroComparisonStatement.{u}`
   (module `SmoothFamilyPicardZeroComparisonProof`). That theorem compares the
   Library's geometric translation-invariance predicate with the source's
   fibrewise smooth-family (algebraic-equivalence) predicate, using the actual
   rigidification and the parameter-first product convention. Its family
   conjunct turns the condition on the universal family into the Picard-zero
   condition. Its class conjunct turns an arbitrary geometric Picard-zero class
   on a quasi-separated test into a smooth-family class with the same underlying
   rigidified class. The smooth-family universal property then gives the unique
   classifying parameter morphism. Its classifying equation and its uniqueness
   predicate are unchanged by this conversion.
4. **Extension to all test schemes.** `picardZeroQuasiSeparatedExtension`
   (module `PicardZeroQuasiSeparatedExtensionProof`) upgrades universality on
   quasi-separated tests to universality on every test scheme. It glues parameter
   maps over affine open covers and uses compatible rigidification-preserving
   bundle isomorphisms, so it does more than classify geometric points. Applied
   to `B.X`, `L` and the output of step 3, it gives the universal property that
   `HasDualScheme A` requires. The theorem then returns `⟨B.X, L, _⟩`.

The parameter is the underlying `Over S` object of the abelian scheme `B`. The
statement asks only for an actual parameter scheme, so the abelian-scheme
structure of `B` is not used further.

## Provenance

This is an internal composition of published Library interfaces. The mathematical
source derivation (the construction of the dual abelian scheme as the
identity component of the relative Picard functor, its representability and the
comparison of algebraic and geometric equivalence) is documented in the paired
Markdown of the imported results. This module adds no construction or source
comparison of its own beyond the predicate transfer in step 3, which is a direct
use of the published comparison theorem.

The finite-type representer was proved by Task 3233 and published as
`lean.proof` candidate `1f268bce-9ef1-4d62-bac4-38d086a0ed3a` (first in Library
commit `f24f97443f21ff7e59b1cf3b509602157dae54c2`). The comparison theorem was
published as candidate `6b1cd5d7-8947-4935-8b6d-5d1ee83fb312` (Library commit
`0a5678a23daa0818e88076247923cd745542293f`). These identifiers only document
provenance; the Lean imports every result by its module and declaration name.

The proof uses no `sorry`, `admit` or new axiom.
