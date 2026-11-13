# Dimension of the first structure-sheaf cohomology of an abelian variety

Author: Worker 327.

`Langlands.AbelianScheme.FieldStructureSheafH1DimensionStatement.{u}` states
that an abelian variety of dimension `g` over any field has a
finite-dimensional first structure-sheaf cohomology space of dimension `g`.
This module is a proposition definition and contains no proof.

The proposition quantifies over a field `k : Type u`, an
`A : AbelianScheme (Spec (CommRingCat.of k))`, and a natural number `g`
with `A.HasRelativeDimension g`. The latter is the existing
`SmoothOfRelativeDimension g A.X.hom` predicate. The existing abelian-scheme
bundle supplies a smooth proper commutative group scheme with geometrically
connected fibres. There is no restriction on characteristic, perfectness
or algebraic closedness, and `g = 0` is allowed.

The vector space is the actual module

```text
H := (DerivedSections.relativeCohomology A.X.hom 1).obj
       (Langlands.Scheme.Modules.structureSheaf A.X.left).
```

Here `structureSheaf` is `SheafOfModules.unit`, and
`relativeCohomology` is the right-derived functor of module global sections,
with its `k`-action induced by the structure morphism. The conclusion is
`FiniteDimensional k H ∧ Module.finrank k H = g`. Explicit finiteness
prevents the zero value of `finrank` for infinite-dimensional modules from
weakening the assertion when `g = 0`.

The source is B. Edixhoven, G. van der Geer and B. Moonen, *Abelian
Varieties*, preliminary version of the first chapters, Theorem (6.18),
printed p.96 / PDF p.100. Its last equality identifies the dimension of
an abelian variety with the dimension of its first structure-sheaf
cohomology over an arbitrary field. The source's finite-dimensional
cohomology conventions and Proposition (6.15) are explained in the
imported `FieldStructureSheafH1DimensionBoundStatement.md`.
The registered source is
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.

This is precisely the cohomological dimension conclusion of (6.18),
specialized to the existing abelian-scheme bundle over a field and with
dimension specified by `HasRelativeDimension`. The source admits ordinary
Picard representability in the preceding paragraph (printed p.95 / PDF
p.99), and then combines the finite kernel of the ample Mumford classifier,
the tangent/cohomology comparison (6.6), and the upper bound (6.15).
The present proposition asserts neither Picard representability nor any
geometry of a dual scheme. It assumes no Picard family or comparison
statement. A proof must establish equality without adding such hypotheses.

The imported bound statement uses the same actual cohomology object and
requires only `finrank k H ≤ g`; the present statement adds the missing
reverse inequality. `RigidifiedPicardH1Coordinates` proves equality only
when an actual locally finite type universal rigidified Picard family is
supplied, so it does not prove this proposition unconditionally.
The degree-two exterior/coproduct comparison still additionally needs
actual cup and contraction maps, their relations and vanishing, and the
canonical pullback formulas. None of those is asserted here.
