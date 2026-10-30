# Finitely many rational translations preserve an ample line bundle over an algebraically closed field

`Langlands.AbelianScheme.AlgClosedFieldAmpleTranslationStabilizerFiniteStatement`
is a universe-polymorphic `Prop`-valued definition. It states the
rational-point consequence of Edixhoven, van der Geer and Moonen, *Abelian
Varieties*, Lemma (2.19), for actual line bundles on an abelian scheme over
an algebraically closed field. The module supplies no proof and adds no axiom.

## Statement

For every field `K : Type u` with `IsAlgClosed K`, every
`A : AbelianScheme (Spec (CommRingCat.of K))` and every actual line bundle
`L` on `A.X.left`,

```text
L.IsAmple →
  Finite {x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X //
    Nonempty ((LineBundle.pullback
      (GroupScheme.translation A.toGrp x).left).obj L ≅ L)}.
```

In words: if `L` is ample, then only finitely many `K`-rational points `x`
of `A` satisfy `t_x^*L ≅ L`.

The conclusion is finiteness of this subtype of rational points. It is not
finiteness of all rational points of `A`, and it does not say that any
translation morphism is finite. It uses the Mathlib class `Finite`, a
proposition; no chosen `Fintype` structure or enumeration is required. The
statement does not assert that the subtype is a subgroup, and it does not
mention a scheme-theoretic stabilizer.

## Complete checked type

The source declaration is

```lean
def AlgClosedFieldAmpleTranslationStabilizerFiniteStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (L : LineBundle A.X.left),
    L.IsAmple →
      Finite {x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X //
        Nonempty ((LineBundle.pullback
          (GroupScheme.translation A.toGrp x).left).obj L ≅ L)}
```

inside `namespace Langlands.AbelianScheme`, with
`open CategoryTheory AlgebraicGeometry` and
`open Langlands.AlgebraicGeometry.Picard`. It imports
`Langlands.AlgebraicGeometry.Picard.Ample`,
`Langlands.AlgebraicGeometry.Picard.GeometricPicardZero` and
`Mathlib.FieldTheory.IsAlgClosed.Basic`.
With `pp.fieldNotation false`, `pp.proofs true` and `pp.funBinderTypes true`,
`#print` in the approved environment reports:

```text
def Langlands.AbelianScheme.AlgClosedFieldAmpleTranslationStabilizerFiniteStatement.{u} : Prop :=
∀ (K : Type u) [inst : Field K] [IsAlgClosed K] (A : Langlands.AbelianScheme (AlgebraicGeometry.Spec ↧K))
  (L :
    Langlands.AlgebraicGeometry.Picard.LineBundle
      (CategoryTheory.Over.left
        (CategoryTheory.Grp.X (Langlands.CommGroupScheme.toGrp (Langlands.AbelianScheme.toCommGroupScheme A))))),
  Langlands.AlgebraicGeometry.Picard.LineBundle.IsAmple L →
    Finite
      { x :
        CategoryTheory.Over.mk (CategoryTheory.CategoryStruct.id (AlgebraicGeometry.Spec ↧K)) ⟶
          CategoryTheory.Grp.X (Langlands.CommGroupScheme.toGrp (Langlands.AbelianScheme.toCommGroupScheme A)) //
        Nonempty
          (CategoryTheory.Functor.obj
              (Langlands.AlgebraicGeometry.Picard.LineBundle.pullback
                (CategoryTheory.Over.Hom.left
                  (Langlands.GroupScheme.translation
                    (Langlands.CommGroupScheme.toGrp (Langlands.AbelianScheme.toCommGroupScheme A)) x)))
              L ≅
            L) }
```

and `#check` reports type `Prop`. Here `↧K` is `CommRingCat.of K`, and
`A.X` abbreviates `Grp.X (CommGroupScheme.toGrp (toCommGroupScheme A))`.

## Library objects used

The statement uses only published definitions. It adds no structure,
certificate, axiom, tensor product or chosen inverse.

- `A : AbelianScheme S` is the published bundle: a commutative group scheme
  over `S` whose structure morphism `A.X.hom` is smooth, proper and
  geometrically connected. Here `S = Spec K`.
- A section `x : Over.mk (𝟙 (Spec K)) ⟶ A.X` is a morphism over `Spec K`
  from `Spec K` to `A.X`, that is, a `K`-rational point of `A`.
- `GroupScheme.translation A.toGrp x` is
  `(Over.mkIdTerminal.from A.X ≫ x) * 𝟙 A.X`, the translation built from the
  actual group law. By the published lemma
  `Langlands.GroupScheme.points_translation`, on `T`-points it sends `y` to
  `x_T * y`. Its `.left` is the underlying morphism of schemes
  `A.X.left ⟶ A.X.left`.
- `LineBundle X` is the full subcategory of actual `X.Modules` that are
  locally isomorphic to the structure sheaf. An isomorphism of line bundles
  is an isomorphism of the underlying sheaves of modules.
- `LineBundle.pullback f` is the actual sheaf pullback
  `Scheme.Modules.pullback f` restricted to line bundles.
- `L.IsAmple` is the published ampleness predicate, described below.

The predicate inside the subtype is the same as the one quantified in the
published `Langlands.GroupScheme.IsTranslationInvariant`, but here it is
taken pointwise rather than for every `x`.

## Original source

The original is B. Edixhoven, G. van der Geer and B. Moonen, *Abelian
Varieties*, preliminary version of the first chapters, registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`,
retained as
`literature/Edixhoven, van der Geer, Moonen - Abelian Varieties (preliminary version of the first chapters).pdf`.
Printed page numbers are PDF page numbers minus four. The retained file
was hashed again for this statement and matches the registered SHA256.
The Library has no errata note for this source in `notes/errata/`. The
published Markdown of
`Langlands.AbelianScheme.AlgClosedFieldTranslationDifferenceLiftingStatement`
records that the author's PDF fetched on 2026-10-27 is byte-identical to
the registered file, and that the author's page lists no errata.

The following passages were read.

- Lemma (2.19), printed p.23 (PDF p.27): "If `L` is ample then `K(L)` is a
  finite group scheme." Here `L` is a line bundle on an abelian variety `X`
  over a field `k`.
- Definition (2.15), printed p.22 (PDF p.26): the Mumford bundle
  `Λ(L) = m^*L ⊗ p_1^*L^{-1} ⊗ p_2^*L^{-1}` on `X × X`. The text notes that
  its restriction to a horizontal fibre `X × {x}` is `t_x^*L ⊗ L^{-1}`.
- Definition (2.16), printed p.22 (PDF p.26): `K(L) ⊆ X` is the maximal
  closed subscheme such that `Λ(L)|_{X×K(L)}` is the pullback under `pr_2` of
  a line bundle on `K(L)`. It exists by Proposition (2.4), printed p.18
  (PDF p.22), which the source proves by citing Mumford's *Abelian
  Varieties*, §10.
- Lemma (2.17)(i), printed p.23 (PDF p.27): for a `k`-scheme `T` and
  `x ∈ X(T)`, the morphism `x` factors through `K(L)` if and only if
  `t_x^*L_T ⊗ L_T^{-1}` is the pullback of a line bundle on `T`. The text
  before it reads "Roughly speaking, a point belongs to `K(L)` if `L` is
  invariant under translation by this point."
- Conventions (0.4), printed p.1 (PDF p.5): a variety over `k` is a
  separated `k`-scheme of finite type that is geometrically integral, and a
  line bundle is a locally free module of rank one.
- Definitions (1.2) and (1.3), printed p.6 (PDF p.10): an abelian variety
  is a group variety that is complete.
- Definition (1.4), printed pp.6–7 (PDF pp.10–11): `t_x` is the right
  translation, `t_x(y) = m(y, x)`.
- Corollary (1.15)(ii), printed p.13 (PDF p.17): the group law of an
  abelian variety is commutative.

The provenance is derived. Lemma (2.19) is a statement about the subgroup
scheme `K(L)` over an arbitrary field. The Lean statement is its consequence
for the set of rational points over an algebraically closed field. It is
expressed directly by the condition `t_x^*L ≅ L`, so it needs neither
`K(L)` as a scheme nor the source's Proposition (2.4). The next sections
explain why the source implies it and how the conventions match.

## Why Lemma (2.19) implies this statement

Take `X = A.X.left` over `k = K` algebraically closed, and an ample line
bundle `L` on `X`.

1. **The rational points of `K(L)`.** Apply Lemma (2.17)(i) with
   `T = Spec K`. Then `X_T = X`, `L_T = L`, and `t_x` is translation by the
   rational point `x`. So `x` factors through `K(L)` if and only if
   `t_x^*L ⊗ L^{-1}` is the pullback of a line bundle on `Spec K`. Every line
   bundle on `Spec K` is trivial, and so is its pullback. Hence the
   condition is that `t_x^*L ⊗ L^{-1}` is trivial, which is equivalent to
   `t_x^*L ≅ L` (tensor both sides with `L`, or with `L^{-1}`). Since
   `K(L) → X` is a closed immersion, hence a monomorphism, composing with
   it is an injective map from the rational points of `K(L)` to those of
   `X`. Its image is exactly the subtype of the statement.
2. **Finiteness.** By Lemma (2.19), `K(L)` is finite over `K`, so
   `K(L) = Spec B` for a `K`-algebra `B` of finite dimension `d`. Its
   rational points are the `K`-algebra maps `B → K`. Distinct such maps are
   linearly independent in the `K`-dual of `B` (Dedekind's independence of
   characters), so there are at most `d` of them. This holds even when
   `K(L)` is not reduced. Hence the subtype is finite.

The source proof of Lemma (2.19) first reduces to an algebraically closed
field. The Lean statement already assumes one. Its proof also invokes
Fact (2.13), which over a perfect field makes `K(L)^0_red` an abelian
subvariety. An algebraically closed field is perfect.

The derived statement is weaker than the source lemma. It is stated only
over algebraically closed fields and it concerns rational points only. This
is the form that the ordinary lifting proof needs (see Role, below).

## Matching the conventions

**Abelian varieties.** The source abelian variety over `k` is a
geometrically integral, separated, finite-type group scheme over `k` that
is proper. The Library `AbelianScheme (Spec K)` is a commutative group
scheme whose structure morphism is smooth, proper and geometrically
connected. A source abelian variety is smooth by Proposition (1.5),
printed p.7, and commutative by Corollary (1.15)(ii). Being geometrically
integral, it is geometrically connected. Conversely, let `X` be smooth and
geometrically connected over `k`, and let `k̄` be an algebraic closure.
Then `X_k̄` is smooth over `k̄`, hence regular and in particular normal, and
it is connected and noetherian. A connected normal noetherian scheme is
integral, so `X` is geometrically integral. Proper morphisms are separated
and of finite type. So a Library abelian scheme over `Spec K` is a source
abelian variety, and conversely.

**Translations.** The source `t_x` is right translation `y ↦ m(y, x)`. The
Library translation is left translation `y ↦ x * y`. The Library group law
is commutative, so the two agree, and so do their pullbacks.

**Pullbacks and isomorphisms.** The source `t_x^*L` is the pullback of the
line bundle `L` along `t_x`. The Lean term
`(LineBundle.pullback (GroupScheme.translation A.toGrp x).left).obj L` is
the actual module pullback of `L` along the underlying scheme morphism of
the translation. `Nonempty (… ≅ L)` asks for an isomorphism of the
underlying sheaves of modules. The condition is stated without tensor
products or inverses, so no tensor-comparison premise such as
`Langlands.Scheme.Modules.pullbackTensorComparisonIsIsoStatement` is needed.

## Ampleness

EvdGM uses "ample" without its own definition; a search of Chapters I–III
of the retained PDF finds no definition. It is read as the standard notion
of EGA II, Definition 4.5.3. The registered original
`stacks-invertible-picard-ampleness-2026-10-21`, directory SHA256
`2a0bbd01484fc7cef97110a88cf4b3e472574fbbb9469d037170744a1462f835`,
retained in
`literature/Stacks Project - Invertible sheaves, Picard groups and ampleness (HTML snapshot 2026-10-21)`,
was read in `01PS.html` and `01CY.html`.
[Definition 28.27.1, tag 01PS](https://stacks.math.columbia.edu/tag/01PS),
which the page attributes to EGA II Definition 4.5.3, calls an invertible
sheaf `ℒ` ample if `X` is quasi-compact and every `x ∈ X` lies in some
affine `X_s` with `s ∈ Γ(X, ℒ^{⊗ n})` and `n ≥ 1`.

The Library predicate `L.IsAmple` is used unchanged. For `X = A.X.left` it is

```text
CompactSpace X ∧ ∀ x : X, ∃ n : ℕ, 1 ≤ n ∧ ∃ s : L.powSections n,
  x ∈ L.sectionOpen s ∧ IsAffineOpen (L.sectionOpen s).
```

Here `L.powSections n` is the set of global sections of the actual tensor
power `Langlands.Scheme.Modules.tensorPow L.obj n`. `L.sectionOpen s` is
`trivializationOpen (tensorPow L.obj n) s`, the supremum of the opens on
which the map from the structure sheaf sending `1` to `s` is an
isomorphism. The whole generation open must be affine. An affine
neighbourhood of `x` inside it does not suffice, and the statement does not
weaken this condition.

[Lemma 17.25.10, tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
shows that on `X_s` the map given by `s` is an isomorphism, so `X_s` lies
in the generation open. Conversely, at any point where `s` generates, its
image is not in `𝔪_x ℒ_x`. Hence the generation open is exactly `X_s`, and
`L.IsAmple` is the source notion with `ℒ^{⊗ n}` read as `tensorPow L.obj n`.
In Lean, the published `LineBundle.isAmple_iff_nonvanishingLocus` records
this equivalence under two hypotheses. The first,
`LineBundleResidueOpenComparison`, is available as the theorem
`Langlands.SchemeModule.lineBundleResidueOpenComparison`. The second is
local rank one of every actual tensor power `tensorPow L.obj n`, the
statement
`Langlands.AlgebraicGeometry.Picard.TensorPowLocallyFreeRankOneStatement`,
proved in the Library as `tensorPow_isLocallyFreeRankOne`. This statement
does not take either comparison as a premise; a proof that needs them can
import these published theorems.

## Proof obligations for the later exact proof

After independent acceptance and publication, a separate exact-target proof
must have this entire named proposition as its type, with no extra outer
hypotheses. A conditional finiteness assembly is not such a proof.

The source proof of Lemma (2.19) sets `Y = K(L)^0_red`, an abelian
subvariety by Fact (2.13). The restriction `L'` of `L` to `Y` is ample. By
Lemma (2.17)(iii), `Λ(L')` is trivial on `Y × Y`. Pulling it back along
`(1, -1) : Y → Y × Y` shows that `L' ⊗ (-1)^*L'` is trivial on `Y`. This
bundle is ample, because `(-1)^*L'` is ample and a tensor product of ample
bundles is ample. A proper scheme with a trivial ample bundle is finite, so
`dim Y = 0`, and `K(L)` is finite.

An alternative proof of the exact point-set statement is allowed. The
following point-level route avoids constructing `K(L)` as a scheme. Over
the algebraically closed `K`:

1. The subtype is the set of rational points of the closed set
   `{y : Λ(L)|_{X×{y}} trivial}` (source Lemma (2.3), printed p.17), since
   `Λ(L)|_{X×{y}} ≅ t_y^*L ⊗ L^{-1}`.
2. By the Theorem of the Square, the subtype is a subgroup of `X(K)`.
3. Let `Z` be that closed set with its reduced structure, and `Y` its
   identity component. Then `Y` is an abelian subvariety of `X`. Put
   `L' = L|_Y`. For every rational point `y` of `Y`,
   `Λ(L')|_{Y×{y}} ≅ t_y^*L' ⊗ L'^{-1}` is trivial, and `Λ(L')|_{{0}×Y}` is
   trivial. The See-saw Principle (2.2), printed p.17, then makes `Λ(L')`
   trivial on `Y × Y`. If `Y` has positive dimension, the source argument
   above gives a contradiction.
4. So `dim Y = 0`. The irreducible components of `Z` are the translates of
   `Y` by rational points of `Z`, and `Z` is noetherian, so it has finitely
   many of them. Hence `Z` is finite, and so is its set of rational points.

Read as a Library proof, either route leaves these obligations.

- Restriction of ampleness along a closed immersion, and ampleness of
  `(-1)^*L'`, since the inverse `-1` is an automorphism and hence a closed
  immersion. Both are instances of
  `Langlands.AlgebraicGeometry.Picard.ClosedImmersionPullbackAmpleStatement`,
  proved in the Library as `closedImmersionPullbackAmple`. Transport of
  ampleness along an isomorphism of line bundles on one scheme is
  `Langlands.AlgebraicGeometry.Picard.AmpleIsoStatement`, proved in the
  Library as `ampleIso`.
- Ampleness of tensor products of ample bundles. This is
  `Langlands.AlgebraicGeometry.Picard.AmpleTensorStatement`, proved in the
  Library as `ampleTensor`.
- Finiteness of a proper scheme with a trivial ample bundle. This is
  `Langlands.AlgebraicGeometry.Picard.ProperAmpleTrivialFiniteStatement`,
  proved in the Library as `properAmpleTrivialFinite`.
- Triviality of line bundles over a field. This is
  `Langlands.AlgebraicGeometry.Picard.FieldLineBundleTrivialityStatement`,
  proved in the Library as `fieldLineBundleTriviality`.
- The Theorem of the Square or the Cube. The published
  `Langlands.GroupScheme.FieldCubePullbackStatement` is the relevant cube
  statement. The Library has only the conditional assembly
  `Langlands.GroupScheme.fieldCubePullbackOfIsomorphism` for it, not an
  unconditional proof.
- The Mumford-bundle restriction `Λ(L)|_{X×{y}} ≅ t_y^*L ⊗ L^{-1}` for
  actual pullbacks, tensor products and chosen inverses. The pullback-tensor
  comparison it needs is proved in the Library as
  `Langlands.Scheme.Modules.pullbackTensorComparisonIsIso`.
- Either the scheme `K(L)` (Proposition (2.4), Lemma (2.17)) or the
  point-level closedness and See-saw arguments, together with the structure
  of closed subgroups of abelian varieties used in Fact (2.13).

Any genuinely missing substantial construction must be split into
definition, statement and proof units, in that order. Existing ampleness,
cube, tensor and pullback work should be reused, not duplicated. This
module discharges none of these obligations.

## Scope

The statement covers every universe `u`, every algebraically closed field
in every characteristic, and dimension zero. Mathematically, in dimension
zero `A.X.left` is isomorphic to `Spec K`, so `A` has exactly one rational
point and the conclusion holds trivially. Algebraic closedness is the only
condition on `K`. The statement adds no symmetry, projectivity, existing
dual or Picard scheme, scheme-theoretic stabilizer, isogeny, finiteness or
tensor-preservation premise.

## Role and authorship

This is a focused prerequisite of Worker 516's exact proof
`0d978728-03a8-4f05-b45c-8ec83a017647` of
`Langlands.AbelianScheme.AlgClosedFieldTranslationDifferenceLiftingStatement`.
That proof needs only finiteness of the rational points preserving an
ample bundle, which is its obligation 5. It keeps its final assembly and
will use this statement's eventual theorem by Lean name. This statement
does not prove the lifting statement, and the lifting statement is not used
to justify it.

Worker 920 implemented this pair. Worker 516 supplied the focused
specification, including the binders and the conclusion.
