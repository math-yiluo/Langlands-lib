# Representability of the projective frame charts of ordinary polarized moduli

`Langlands.AbelianScheme.PolarizedFiniteLevel.FrameChartRepresentabilityStatement`
is a proposition definition. It is a statement target only; this module proves
nothing.

## The statement

Let `P : Prerequisites.{0}`, let `g d n` be natural numbers with
`hd : 0 < d` and `hn : 3 ≤ n`, and let
`ρ : Fin (cubicProjectiveDimension g d + 2) → Fin (2*g) → ZMod n` be a family of
`6^g·d + 1` level coefficient tuples. (For `d > 0`,
`cubicProjectiveDimension g d + 1 = 6^g·d` is the rank of the cubic direct
image.) Then there are a level base `X : LevelBase n` and a natural
transformation
`a : uliftYoneda.{1}.obj X ⟶ moduliFunctor P g d n hd hn` such that:
- each component `a.app T` is injective; and
- for every level base `T` and datum `b : Datum P T.obj g d n`, the class
  `b.classOf` lies in the image of `a.app (op T)` exactly when the frame locus
  `b.frameLocus ρ` (internal module `FrameLocus`) is all of `T`.

So the subfunctor of classes whose torsion points `ρ` form a projective frame of
the cubic direct image everywhere is represented by `X`.

## Mathematical content and provenance

This is a derived, frame-normalized form of Mumford–Fogarty–Kirwan,
*Geometric Invariant Theory*, §7.2, registered source
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`:
- Definitions 7.5 and 7.6 (printed p.130, PDF p.143): linearly rigidified data;
- the embedding of the abelian scheme into `ℙ^m × S` determined by a linear
  rigidification and the 2g + 1 sections (printed p.131, PDF p.144);
- Proposition 7.3 and its proof (printed pp.132–134, PDF pp.145–147): the
  functor of linearly rigidified data is represented by a locally closed
  subscheme `H_{g,d,n}` of a Hilbert scheme with sections.

On the frame locus, the frame `P_{ρ_0}, …, P_{ρ_{m+1}}` determines a unique
linear rigidification sending these points to the standard projective frame.
So the frame chart is represented by the closed subscheme of `H_{g,d,n}` where
the corresponding universal sections are the standard frame points: the slice
of the free `PGL(m+1)` action on `H_{g,d,n}` determined by a projective frame.
Rigidity of the frame normalization makes `a` injective. The
level hypothesis `3 ≤ n` is the published functor's range. Charts with
degenerate `ρ` are represented by the empty level base.

This statement is the main geometric input of `LargeLevelChartCoverStatement`.
