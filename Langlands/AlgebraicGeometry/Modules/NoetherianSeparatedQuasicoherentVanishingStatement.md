# Vanishing of quasi-coherent cohomology above the dimension

Authors: Worker 921 (original Lean and Markdown draft) and Worker 595
(source and interface verification, revised explanation).

`Langlands.AlgebraicGeometry.Modules.NoetherianSeparatedQuasicoherentVanishingStatement.{u}`
is the following proposition definition, with arbitrary universe `u`:

```lean
∀ (R : CommRingCat.{u}) (X : Scheme.{u}) (f : X ⟶ Spec R) [IsNoetherian X]
  [X.IsSeparated] (d : ℕ), topologicalKrullDim X ≤ (d : WithBot ℕ∞) →
    ∀ (M : X.Modules), M.IsQuasicoherent →
      ∀ n : ℕ, d < n → IsZero ((DerivedSections.relativeCohomology f n).obj M)
```

It states that a quasi-coherent module on a noetherian separated scheme of
dimension at most `d` has zero cohomology in every degree greater than `d`.
The morphism `f` equips this cohomology with scalars in `R`. This file only
defines the proposition; it supplies no proof.

## Conventions and scope

`IsNoetherian X` is Mathlib's class requiring local noetherianness and
quasi-compactness. Its instance
`AlgebraicGeometry.IsNoetherian.noetherianSpace` makes the underlying
topological space noetherian. `X.IsSeparated` is Mathlib's
`AlgebraicGeometry.Scheme.IsSeparated`, requiring separation of the
morphism to the terminal scheme.

`topologicalKrullDim X`, from `Mathlib.Topology.KrullDimension`, is the Krull
dimension of the poset of irreducible closed subsets of the underlying
space: the supremum of lengths of strict chains of those subsets. Its
values lie in `WithBot ℕ∞`; the dimension bound uses the natural number
`d` cast into this type.

`M : X.Modules` is an actual sheaf of modules over the structure sheaf.
`M.IsQuasicoherent` is Mathlib's `SheafOfModules.IsQuasicoherent`.
The dimension bound and quasi-coherence are explicit assumptions;
noetherianness and separatedness are instance arguments. The ring `R` and
morphism `f : X ⟶ Spec R` are arbitrary. There is no finite-type, properness,
field, or further hypothesis on `f`.

The conclusion uses the unchanged Library functor
`DerivedSections.relativeCohomology f n`, defined in
`Langlands.AlgebraicGeometry.Modules.DerivedSections` as
`(relativeGlobalSections f).rightDerived n`. Its values are objects of
`ModuleCat.{u} R`, and `IsZero` states that this cohomology module is zero.
It uses injective resolutions in `X.Modules`.

## Derived provenance

The proposition is a specialization and comparison of two Stacks results.
Neither result alone literally states this Lean interface.

The registered source is
`stacks-flasque-affine-vanishing-kunneth-a04446e5`, the folder
`literature/Stacks Project - Flasque sheaves, affine vanishing and Kunneth over a field (source at a04446e5)`,
at Stacks commit `a04446e57ec1fbc252a871afcec7752fb2807b14`.
Its registered folder SHA-256 is
`af02e6f0aff875e216f1e0fde58f6baad3eedeb6b82799a8d6c91ff68cccaa3a`.
The cited file is `cohomology.tex`, SHA-256
`fa9747d0082afbf8b09244dcc6c260f8a122e5e3b4a3c69e2273506d76e18a42`.

- [Stacks Tag 02UZ, Proposition 20.20.7](https://stacks.math.columbia.edu/tag/02UZ),
  label `proposition-vanishing-Noetherian`, `cohomology.tex` lines
  3665–3674 (`tags.txt` line 3750), gives vanishing above a dimension bound
  for every abelian sheaf on a noetherian topological space. Stacks
  attributes this theorem to Grothendieck's Tohoku, Theorem 3.6.5.
- [Stacks Tag 01F1, Lemma 20.13.3, item (1)](https://stacks.math.columbia.edu/tag/01F1),
  label `lemma-modules-abelian`, `cohomology.tex` lines
  2174–2189 (`tags.txt` line 1854), identifies cohomology computed for a
  module on a ringed space with cohomology of its underlying abelian sheaf.
  Its proof explains that sections of an injective module resolution
  compute both cohomologies.

To derive the stated claim mathematically, first apply Tag 02UZ to the
underlying abelian sheaf of `M`. Mathlib's noetherian-space instance and the
dimension hypothesis give its topological assumptions. Tag 01F1 then
identifies this vanishing group with the cohomology of `M` as a module over
the structure sheaf.

The Library's scalar conventions give this same group an `R`-module
structure. In detail, `DerivedSections.globalSections X` is evaluation at
the top open, with values in modules over `Γ(X, ⊤)`. The published natural
isomorphism `DerivedSections.relativeGlobalSectionsIso f` identifies
`relativeGlobalSections f` with these sections after restricting scalars
along `DerivedSections.structureRingHom f : R ⟶ Γ(X, ⊤)`. The published
`DerivedSections.relativeCohomologyRestrictScalarsIso f n` gives the same
identification on right-derived functors. Restriction of scalars leaves
underlying abelian groups unchanged. Equivalently, forgetting module
scalars is exact and commutes with the homology of the complex of sections
of an injective module resolution. Thus the group identified by Tag 01F1
is the underlying group of `(relativeCohomology f n).obj M`. A module with
zero underlying group is a zero object, giving the conclusion `IsZero`.
This paragraph explains the provenance; the file formalizes none of this
vanishing argument or the abelian-sheaf comparison.

The Lean proposition is narrower than Tag 02UZ: it concerns quasi-coherent
modules on separated noetherian schemes. Tag 02UZ requires neither
quasi-coherence nor separatedness and applies to arbitrary abelian sheaves.
These restrictions are part of the requested target.

## Formal dependencies

The imports are `Mathlib.AlgebraicGeometry.Morphisms.Separated`,
`Mathlib.AlgebraicGeometry.Noetherian`, `Mathlib.Topology.KrullDimension`,
and the published Library module
`Langlands.AlgebraicGeometry.Modules.DerivedSections`.
The Mathlib pin is `5ed2965256430c3649e86755f9576b54eca72435`, with
Lean 4.34.0. All existing imported Lean and Markdown files are unchanged.
