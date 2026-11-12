# Closedness of the fibrewise ample locus on an abelian scheme

Author: Worker 833.

`Langlands.AlgebraicGeometry.Picard.AbelianFibreAmpleLocusClosedStatement.{u}`
quantifies over a locally noetherian scheme `S` in any universe `u`, an
actual Library abelian scheme `A` over `S`, and an actual specified line
bundle `L` on its total scheme. It asserts that

```lean
{s : S | ((LineBundle.pullback (A.X.hom.fiberι s)).obj L).IsAmple}
```

is a closed subset of the topological space of `S`. The fibres are the
scheme-theoretic fibres over the residue fields at all points, and
ampleness is the Library's absolute section-open predicate on each such
fibre.

There is no normality, irreducibility, affine-base, polarization,
symmetry, dual-scheme, or relative-dimension hypothesis. In particular,
the assertion concerns any specified total line bundle. It constructs
neither a bundle nor a representing object.

## Original source

G. Faltings and C.-L. Chai, *Degeneration of Abelian Varieties* (1990),
Chapter I, Remark 1.10(b), printed p.7 (PDF p.19), asserts closedness of
the ample-fibre locus for any invertible sheaf on an abelian algebraic
space over an algebraic space. The registered source is
`provided-0ecad2ee7ec463aef945e9d85a6d369dd775bbbbbd4e55843b9bfb4aa819da7d`,
content SHA-256
`f53b164d7d783ca55a5b6ae6b0885601264f13f2a2660a1d689813715899f20e`.
Worker 833 read printed pp.6–7 and inspected the image of printed p.7 in
the registered copy. No source-specific errata note was found under the
current Library's `notes/errata/`.

The Lean target retains the restriction to locally noetherian scheme
bases and actual scheme-valued abelian schemes. These are narrower than
the source's algebraic-space scope. The source also notes openness; the
present target asserts only closedness. A proof of openness by spreading
ampleness cannot by itself establish this target.

## Intended use and remaining obligation

On an integral affine base, the closure of the generic point is the
whole spectrum. Once ampleness on the canonical fraction-field pullback
has been identified with ampleness on that point's residue-field fibre,
this closedness statement therefore gives ampleness on every fibre.
The separate `ProperAffineFibrewiseAmpleStatement` then gives ampleness
of the total line bundle over a noetherian affine base.

This Lean module only defines the proposition. It does not prove
closedness or generic specialization. A proof must supply the geometric
input for closedness while preserving the separate ownership and
operator pauses of the relative dual and Picard representability tasks.
