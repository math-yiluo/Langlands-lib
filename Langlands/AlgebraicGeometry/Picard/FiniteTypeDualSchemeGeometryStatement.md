# Geometry of the chosen dual parameter scheme over a finite-type integer algebra

The module states a proposition and proves nothing. The proof is the theorem
`Langlands.AbelianScheme.finiteTypeDualSchemeGeometry` in the module
`Langlands.AlgebraicGeometry.Picard.FiniteTypeDualSchemeGeometryProof`.

## Statement

`Langlands.AbelianScheme.FiniteTypeDualSchemeGeometryStatement.{u}` is a
proposition (`Prop`). It quantifies over:

- every type `R : Type u` with `[CommRing R]` and `[Algebra.FiniteType ℤ R]`,
  that is, every commutative ring of finite type over `ℤ`;
- every `A : AbelianScheme (Spec (CommRingCat.of R))`, an actual abelian
  scheme over `Spec R`;
- every proof `hA : HasDualScheme A`.

For each of these it asserts `DualSchemeGeometry A hA`. That predicate is
defined in the published module
`Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeGeometryStatement` as
the conjunction

```lean
Smooth (dualScheme A hA).hom ∧ IsProper (dualScheme A hA).hom ∧
  GeometricallyConnected (dualScheme A hA).hom
```

of Mathlib's morphism properties. So the structure morphism of the chosen
parameter scheme `dualScheme A hA` to `Spec R` is smooth, proper and
geometrically connected.

The inputs are the published definitions, used unchanged:

- `HasDualScheme A` says that some `P : Over (Spec R)` carries an actual
  rigidified family `L : RigidifiedFamily A P` with `IsUniversalPicardZero A L`.
  This means that `L` is a geometric Picard-zero family
  (`IsPicardZeroFamily`), and that every geometric Picard-zero rigidified class
  on every test scheme `T` over `Spec R` is the classifying pullback of `L` along
  exactly one map `T ⟶ P`.
- `dualScheme A hA` is the parameter `P` chosen from `hA` by
  `Classical.choose`. `HasDualScheme A` is a `Prop`, so all proofs `hA` give the
  same chosen parameter.

## Scope

The statement is conditional on `hA`: it does not assert that a dual exists,
and it asserts nothing about schemes that are not the chosen parameter.
Nothing is assumed beyond the finite-type condition:

- `R` may be any finite-type `ℤ`-algebra, including nonreduced rings and rings
  that are not domains;
- `A` is any abelian scheme over `Spec R`, with no polarization or
  projectivity hypothesis;
- `hA` is arbitrary.

`Spec R` is affine, hence quasi-separated. Mathematically, the published
relative proposition `RelativeDualSchemeGeometryStatement`, which asserts the
same conclusion over every quasi-separated base, therefore specializes to this
one. This module neither states nor proves that implication as a Lean lemma.

## Why a separate finite-type statement

The finite-type statement is needed because the relative statement cannot
serve its consumer without a cycle.

- The consumer is the proof of
  `FiniteTypeSmoothFamilyAbelianRepresentabilityStatement` (module
  `FiniteTypeSmoothFamilyAbelianRepresentabilityProof`, through
  `FiniteTypeSmoothFamilyAbelianRepresentabilityAssembly`). It needs the
  geometry of the chosen dual over finite-type bases and applies this
  statement as `geometry R A hA`.
- The published reduction
  `RelativeDualSchemeGeometryStatement.of_flat_finitePresentation_proper` derives
  the relative statement from
  field geometry, flatness, local finite presentation and properness. The
  published `relativeDualSchemeProper_of_prerequisites` derives properness from
  quasi-compactness, among other inputs.
- The proof `relativeDualSchemeGeometry` of the relative statement (module
  `RelativeDualSchemeGeometryProof`) goes through `RelativeDualSchemeExistenceProof`,
  which uses `finiteTypeSmoothFamilyAbelianRepresentability`, the proof of
  `FiniteTypeSmoothFamilyAbelianRepresentabilityStatement`. The general-base
  `SmoothFamilyAbelianRepresentabilityStatement` is proved from that
  finite-type theorem (`smoothFamilyAbelianRepresentability`), and the
  finite-type theorem uses the present statement.

A proof of the present statement must therefore not use those two
representability statements or any route through them. The finite-type
restriction also matches the source. A finite-type `ℤ`-algebra `R` is
noetherian, and `Spec R` and `A` are locally of finite type over `ℤ`, an
excellent Dedekind domain. This is the scope of Artin's theorem as quoted on
printed p.3. Remark 1.2(a) of the source names reduction to the noetherian case
(EGA IV §8) as the standard technique for abelian schemes.

## Provenance

This is a derived specialization. No source states this exact Lean
proposition.

Source: G. Faltings and C.-L. Chai, *Degeneration of Abelian Varieties*
(1990). Registered source
`provided-0ecad2ee7ec463aef945e9d85a6d369dd775bbbbbd4e55843b9bfb4aa819da7d`,
SHA-256 `f53b164d7d783ca55a5b6ae6b0885601264f13f2a2660a1d689813715899f20e`.
The locators below were checked in the registered file.

- Chapter I, Definition 1.1, printed p.1 (PDF p.13): an abelian scheme is a
  group scheme that is smooth and proper with geometrically connected fibres.
  Remark 1.2(a) on the same page notes finite presentation and reduction to the
  noetherian case (EGA IV §8).
- Chapter I, Definition 1.4(c), printed p.2 (PDF p.14): `Pic⁰(X/S)` is the
  functor of rigidified invertible sheaves on `X ×_S T` whose fibres are
  algebraically equivalent to zero.
- Remark 1.5(b),(c), printed p.2 (PDF p.14): `Pic⁰(X/S)` is an open subfunctor
  of `Pic(X/S)` and is formally smooth over `S`.
- Printed p.3 (PDF p.15): Artin's representability theorem, quoted over a field
  or an excellent Dedekind domain. The text then says that `Aᵗ = Pic⁰(A/B)` is
  proper and smooth over `B`, with a group structure, that is, an abelian
  algebraic space. By Definition 1.1 this includes geometrically connected
  fibres.

The derivation to the Library target makes these changes:

- the base `B` is specialized to `Spec R` with `R` of finite type over `ℤ`;
- the representing object is the actual chosen parameter scheme
  `dualScheme A hA`, given through `hA`, not an algebraic space constructed
  from the source;
- only the three geometric properties are kept; the group structure is
  constructed separately in the Library.

No errata note for this source is present in the Library `notes/errata/`
directory.

The Library's universal property uses its own geometric Picard-zero predicate
(`IsPicardZeroFamily`, through `IsUniversalPicardZero`), not the source's
fibrewise algebraic equivalence. This statement makes no claim about comparing
the two predicates. A proof must work with the Library's universal property as
stated.
