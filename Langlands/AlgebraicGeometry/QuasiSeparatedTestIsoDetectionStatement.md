# Isomorphism detection on quasi-separated test schemes

`Langlands.AlgebraicGeometry.QuasiSeparatedTestIsoDetectionStatement.{u}`
is a proposition definition. It states a criterion for a morphism of schemes
over a base to be an isomorphism, tested only on quasi-separated test
schemes. This unit defines the proposition and supplies no proof of it.

## Exact statement

The definition is

```lean
∀ (S : Scheme.{u}) (P Q : Over S) (f : P ⟶ Q),
  (∀ (T : Over S) [QuasiSeparatedSpace T.left],
    Function.Bijective (fun (g : T ⟶ P) => g ≫ f)) →
  IsIso f
```

with `Scheme`, `Over`, `QuasiSeparatedSpace` and `IsIso` taken from Mathlib.

- `S` is an arbitrary scheme in universe `u`. `P` and `Q` are objects of
  Mathlib's category `Over S` of schemes over `S`. The morphism `f` is a
  morphism in `Over S`: a scheme morphism `f.left : P.left ⟶ Q.left`
  compatible with the structure morphisms to `S`.
- The hypothesis ranges over every `T : Over S` in the same universe whose
  underlying topological space `T.left` is quasi-separated, that is,
  satisfies Mathlib's `QuasiSeparatedSpace`: the intersection of two
  quasi-compact open subsets is quasi-compact. For each such `T`, the map
  `(T ⟶ P) → (T ⟶ Q)`, `g ↦ g ≫ f`, of morphisms over `S` must be bijective.
  Only this postcomposition map of the actual category `Over S` is used; no
  abstract replacement of the morphism sets occurs.
- The conclusion `IsIso f` is taken in `Over S`. Thus `f` has an inverse
  morphism of schemes over `S`. Since `Over.forget S` preserves and reflects
  isomorphisms, this is equivalent to `f.left` being an isomorphism of schemes.

No hypothesis is placed on `S`, `P.left`, `Q.left` or `f`. In particular
none of these schemes is assumed quasi-separated, quasi-compact, separated,
noetherian or affine, and `f` is not assumed to be of finite type or an
immersion.

The admissible tests include every `T` whose underlying scheme `T.left` is
affine, with any structure morphism to `S`, because Mathlib provides
`QuasiSeparatedSpace` for affine schemes. They also include every open
subscheme of an affine scheme, with any structure morphism to `S`, since an
open embedding into a quasi-separated space has quasi-separated source
(`Topology.IsOpenEmbedding.quasiSeparatedSpace`). A test need not be
quasi-compact. The parameter schemes `P.left` and `Q.left` themselves need not
be admissible tests.

## Derived provenance and role

This is a derived internal formalization target, not a theorem quoted from
the literature. No original source is cited for it, and the Markdown asserts no
source theorem.

If the hypothesis quantified over all objects of `Over S`, the conclusion
would follow from the Yoneda lemma by testing with `T = Q` and `T = P`.
The restriction of the tests to quasi-separated schemes is the substantive
content: it allows comparison with functors that are only defined, or only
known, on quasi-separated test schemes, without first proving the target
parameter schemes quasi-separated.

The criterion was isolated for the relative dual geometry workflow. There
the Library's chosen parameter scheme `dualScheme A hA`, used in
`Langlands.AbelianScheme.RelativeDualSchemeFlatStatement` and
`Langlands.AbelianScheme.RelativeDualSchemeFinitePresentationStatement`, has
a priori no geometric properties. Some Library universal properties, such
as `Langlands.AbelianScheme.IsUniversalSmoothFamilyOnQuasiSeparatedTests`
and `Langlands.AbelianScheme.IsUniversalPicardZeroOnQuasiSeparatedTests`,
quantify only over test schemes `T` with `QuasiSeparatedSpace T.left`, while
leaving the parameter scheme unrestricted. A morphism of parameter schemes
over `S` that induces bijections on such tests is intended to be identified
as an isomorphism over `S` by this criterion. The present statement is the
generic scheme-theoretic part of that step. It is independent of Picard functors,
line bundles, algebraic equivalence and the geometry of the parameter scheme.
It does not construct any comparison morphism, does not prove bijectivity
for any particular functor, and does not establish any property of a
representing scheme.

## Remaining proof obligations

A proof of this proposition is the separate obligation of an exact-target
proof task. It must establish a genuine inverse scheme morphism over `S`
from the stated tests. Unfolding this definition, or citing a
representability theorem, is not a proof.

One possible route, not established here, is the following. Cover
`Q.left` by affine opens and use surjectivity on these affine tests to lift
each open immersion through `f`. Pairwise overlaps are open subschemes of
affine schemes, hence admissible tests even when they are not
quasi-compact; injectivity on them makes the lifts agree, so they glue to a
morphism `g : Q.left ⟶ P.left` over `S`. Then `g ≫ f.left = 𝟙` holds on
each affine chart of `Q.left` by construction of the lifts, and
`f.left ≫ g = 𝟙` can be checked on affine opens of `P.left` using
injectivity on those affine tests. A proof may instead use an existing density or gluing
result, provided it adds no quasi-separatedness, quasi-compactness or
separatedness hypothesis on `S`, `P.left` or `Q.left`.
