# Local unit factorization for a tensor-invertible pair

`Langlands.Scheme.Modules.TensorLocalUnitFactorizationStatement X` defines
the following proposition, for every `X : AlgebraicGeometry.Scheme.{u}`:

```text
∀ (M N : X.Modules) (e : M ⊗ N ≅ 𝟙_ X.Modules) (x : X),
  ∃ (U : X.Opens) (hx : x ∈ U)
    (s : 𝟙_ U.toScheme.Modules ⟶ M.restrict U.ι)
    (t : 𝟙_ U.toScheme.Modules ⟶ N.restrict U.ι),
    IsIso (s ⊗ₘ t).
```

Its complete unapplied type is
`(X : AlgebraicGeometry.Scheme.{u}) → Prop`, with arbitrary universe `u`.
The isomorphism is quantified directly; there is no additional data structure.
The witnesses may depend on both modules, the isomorphism, and the point.

The sole import is
`Langlands.AlgebraicGeometry.Modules.TensorMonoidal`. Both tensors use its
published localized symmetric monoidal structure on actual scheme-module
sheaves. In particular, `s ⊗ₘ t` is a morphism in `U.toScheme.Modules`,
from the tensor of two copies of its unit to
`M.restrict U.ι ⊗ N.restrict U.ι`. Each of `s` and `t` has the actual
structure module of the open subscheme as source. The chosen unit is
definitionally `structureSheaf`, namely `SheafOfModules.unit` of that scheme's
`ringCatSheaf`. Restrictions are Mathlib's actual
`AlgebraicGeometry.Scheme.Modules.restrict` along the open immersion `U.ι`.
No freely chosen monoidal instance or tensor comparison is a parameter.

There are no affine, coherent, quasi-coherent, noetherian, finite-presentation,
or nonempty-scheme hypotheses. The local-ring property of the structure-sheaf
stalks is built into `Scheme` through its locally ringed space structure.
The assertion at every point is vacuous on the empty scheme.
This file defines a proposition and supplies no proof of it. In particular,
it supplies no neighborhood trivialization and asserts no individual
isomorphism property of `s` or `t`.

## Original source and internal interface

The registered source is
`stacks-local-freeness-invertibility-sections-2026-10-21`, content SHA-256
`6d1641a9deb284be889ee6e2630a2be6e57cc5985c80af2c9da7d17543ed0785`.
Its retained folder is *Stacks Project - Locally free sheaves and invertible
modules, Sections 17.14 and 17.25 (HTML snapshot 2026-10-21)*. The cited file is
`01CR.html`, with these precise locations:

- [Definition 17.25.1, tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
  defines an invertible module by tensoring with it being an equivalence.
- [Lemma 17.25.2, tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
  equates that condition with existence of a tensor inverse. Its proof locally
  writes the inverse image of one under the tensor isomorphism as a finite
  sum of pure tensors of sections, then obtains a finite free direct-summand
  presentation and finite presentation.
- [Lemma 17.25.4, tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
  proves local rank one implies invertibility on a ringed space, with the
  converse when all structure-sheaf stalks are local rings. Its converse proof
  obtains rank one on stalks and uses finite presentation to spread a stalk
  basis, invoking Lemma 17.11.7.

Both lemma proofs and the definition were read in the retained original.
No source-specific erratum file was present in the current Library or project
`notes/errata/` locations when checked on 2026-10-26.

The Lean proposition is an internal intermediate interface, specified by
Worker 124 and formalized by Worker 513. It is motivated by the finite tensor
expansion in Lemma 17.25.2 and local-ring algebra, specialized to schemes.
It is not a verbatim statement of either lemma. It selects an alternative
unit-pairing route toward the converse of Lemma 17.25.4, rather than
formalizing the source's finite-presentation and basis-spreading proof.
The stronger local-ring hypothesis needed for this interface is supplied by
schemes; Lemma 17.25.2 itself holds for arbitrary ringed spaces.

## Obligations for a later proof

A later proof must justify the following steps and comparisons; this statement
does not provide them.

1. Interpret the given isomorphism and its inverse image of one using the
   actual sheaf tensor. Obtain, near the chosen point, a finite pure-tensor
   expansion by sections. The sectionwise tensor is sheafified; a section of
   the sheaf tensor must not be identified globally with a tensor of sections.
2. Transport the finite expansion through restriction and the pairing induced
   by `e`. At the point the scalar pairings sum to one in the scheme local
   ring, so one summand has a unit germ. Justify passage from sections and the
   sum to these stalk scalars, including any tensor/stalk comparison used.
3. Shrink the neighborhood so that this scalar section is a unit. Transfer
   the chosen sections to the smaller restrictions and identify them with
   morphisms from the structure module, using the section/unit-Hom
   correspondence.
4. Construct or import the restriction/tensor comparison for the fixed tensor,
   with naturality on the section morphisms and compatibility with the unit.
   The existing `localizedTensorIso` and `localizedTensorNatIso` compare
   monoidal tensor with the explicit sheafified `tensorObj` and `tensorMap`.
   Mathlib's `restrictFunctorIsoPullback` and `restrictUnitIso` identify
   restriction with pullback and restriction of the structure module with
   the local unit. These maps alone do not establish tensor preservation.
   If the proof uses `pullbackTensorComparisonApp`, it must first obtain the
   invertibility of that fixed comparison, and check the resulting restriction
   comparison and the section-pairing equation in the required directions.
5. Under the resulting restricted isomorphism and the appropriate unit
   unitor, identify the composite of `s ⊗ₘ t` with multiplication by the unit
   scalar section. Prove that multiplication is an isomorphism, and cancel
   the comparison isomorphisms to conclude `IsIso (s ⊗ₘ t)`.

Any substantive missing comparison needs its own justified construction and
proof, rather than an extra hypothesis on the final proposition.
Generic categorical cancellation from invertibility of the tensor of two
unit-source morphisms to individual isomorphisms is a separate prerequisite.
The reverse local-rank-one implication and the parent equivalence remain
separate assembly obligations.
