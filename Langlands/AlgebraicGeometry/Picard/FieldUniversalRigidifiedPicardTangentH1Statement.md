# The actual tangent-to-H1 statement for a universal rigidified Picard parameter

Authors: Worker 139 and Worker 432. Worker 432 supplied the statement design;
Worker 139 prepared this public statement and its explanation.

`Langlands.AbelianScheme.FieldUniversalRigidifiedPicardTangentH1Statement.{u}`
is a definition returning `Prop`. It states the existence of a linear
equivalence between two specified modules. This module supplies no proof
of the proposition.

## Hypotheses

The universe `u` is arbitrary. The binders, in order, are:

- `k : Type u` with `[Field k]`, an arbitrary field;
- `A : AbelianScheme (Spec (CommRingCat.of k))`, an actual abelian scheme
  over `Spec k`;
- `P : Over (Spec (CommRingCat.of k))`, an arbitrary scheme over `Spec k`,
  whose structure morphism is `P.hom`;
- `U : RigidifiedFamily A P`, an actual relative line bundle rigidified
  along the unit section of `A`;
- `hU : RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A)
  (unitSection_comp A) U`, the full universal property of this family.

These data are followed by the hypothesis `LocallyOfFiniteType P.hom`.
The existing `AbelianScheme` structure includes a commutative group scheme
whose structure morphism is smooth and proper with geometrically connected
fibres. Its section `unitSection A` and the equation `unitSection_comp A`
are the existing declarations from `RelativePicardZero`.

`RigidifiedFamily A P` uses the published relative family on the
parameter-first fibre product `P ×_k A`, with its actual rigidification.
`IsUniversal` says that for every `Q : Over (Spec k)`, pulling back `U`
induces a bijection from morphisms `Q ⟶ P` to isomorphism classes of
rigidified relative line bundles on `Q ×_k A`. In particular it includes
nonreduced tests such as the spectrum of the dual numbers. Classification
only on geometric points would not meet this hypothesis.

There is no perfectness or algebraic closedness hypothesis on `k`, and no
additional smoothness, reducedness or group structure hypothesis on `P`.
No cohomological dimension or finite-dimensionality bound is supplied.

## The exact modules and conclusion

The local `let` bindings specify the objects; they introduce no additional
assumptions or chosen comparison maps.

First,

```text
e = RigidifiedLineBundle.trivialParameter A.X.hom (unitSection A)
      (unitSection_comp A) U hU : Over.mk (𝟙 (Spec k)) ⟶ P
```

is the published section classifying the canonically rigidified trivial
relative line bundle. Its underlying map is a section `Spec k ⟶ P.left`.
Evaluating it at the unique point of `Spec k` gives exactly
`fullPicardOriginPoint k A U hU` from `FieldPicardIdentityComponent`.
No identity-component open or group law on `P` is used.

Next, `T = Langlands.Scheme.tangentSpaceAtPoint P e` is the existing
`k`-module of global sections over `Spec k` of the internal sheaf dual
of `e* Omega_(P/k)`. More explicitly, `cotangentAtSection P e` pulls the
published relative differential sheaf of `P.hom` back along `e.left`;
`tangentAtSection P e` takes its internal Hom into the structure module;
and `tangentSpaceAtPoint P e` applies Mathlib's `moduleSpecΓFunctor`.
The scalar convention uses the canonical isomorphism between global
functions on `Spec k` and `k`. These are the actual objects from
`PointTangentSpace`, with no replacement tangent carrier.

Finally,

```text
H = (DerivedSections.relativeCohomology A.X.hom 1).obj
      (Langlands.Scheme.Modules.structureSheaf A.X.left)
```

uses `DerivedSections` in the namespace
`Langlands.AlgebraicGeometry.Modules`. The coefficient object is the
actual structure sheaf as a module over itself, from `Modules.Tensor`.
`relativeCohomology A.X.hom 1` is the first right-derived functor of
`Scheme.Modules.pushforward A.X.hom ⋙ moduleSpecΓFunctor`, on the category
of actual module sheaves on `A.X.left`. Thus `H` is structure-sheaf
cohomology as a `k`-module with the structure-map scalar action.
It is computed using Mathlib's injective resolutions, rather than being a
supplied cohomology space.

The conclusion is exactly `Nonempty (T ≃ₗ[k] H)`: there exists a
`k`-linear equivalence from this `T` to this `H`. The proposition specifies
no preferred equivalence, naturality, dimension equality, dimension bound,
or smoothness conclusion.

## Original source and derived provenance

The original is B. Edixhoven, G. van der Geer and B. Moonen,
*Abelian Varieties*, preliminary version of the first chapters, Corollary
(6.6)(i) and its explicit proof, printed pp.90–91 (PDF pp.94–95).
Registered source ID:
`edixhoven-vandergeer-moonen-abelian-varieties-draft`; SHA-256:
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Worker 139 read both full pages and inspected their rendered formulas.
No source-specific errata file was present in the checked workspace,
project or current Library `notes/errata` locations.

For a proper variety `X` over a field, the cited part of the corollary
identifies the tangent space of the Picard parameter at its identity with
`H¹(X, O_X)`. The direct explanation sets `D = Spec(k[ε]/(ε²))`.
On the common underlying topological space of `X_D` and `X`, it uses the
units sequence

```text
0 → O_X → O_(X_D)^× → O_X^× → 1,
       f ↦ 1 + εf,
```

and the resulting injection from `H¹(X, O_X)` into `Pic(X_D)`, with image
the classes restricting to the trivial bundle on `X`. The source describes
the tangent space as the kernel of restriction on Picard-valued dual-number
points and obtains a linear isomorphism from cohomology to that tangent
space. The continuation on p.91 explains surjectivity after ensuring a
rational point.

The present statement is a derived specialization to the actual abelian
scheme `A`, with its unit section already providing a rational point, and
to an arbitrary supplied rigidified universal parameter `P`. The
representable-uniqueness rationale is that all-test universality describes
the same rigidified class functor independently of the chosen universal
parameter. The existing `comparisonIso` construction compares two actual
universal rigidified parameters. To use the source's ordinary Picard
parameter one must justify the applicable comparison with this rigidified
functor and preserve the trivial class. Neither such a comparison nor
existence of a universal parameter is an extra premise or a theorem here.

A future proof must verify the source's geometric hypotheses from the
actual `AbelianScheme` input and construct the comparison between the
published sheaf-defined `T` and the dual-number tangent description. It
must also compare the source's units-sequence or Čech description with the
actual right-derived module-sheaf cohomology `H`, preserving the
`k`-linear structures. Inverting the resulting source-oriented
cohomology-to-tangent isomorphism gives the direction in the conclusion.
These comparisons are proof obligations, not existing results claimed
by this statement unit; substantial missing constructions or comparisons
require separate publication.

The later smoothness assertion in (6.6)(i) and the completeness assertion
in (6.6)(ii) are outside this statement. The module also supplies no
identity-component comparison, openness theorem, or structure-sheaf H1
dimension bound. Its imports reuse the existing definitions unchanged and
do not use the downstream Picard or dual-scheme smoothness proofs.
