# Multiplication and inversion pullbacks of translation-invariant line bundles

`Langlands.AbelianScheme.AlgClosedFieldTranslationInvariantPullbackIdentitiesStatement.{u}`
is a `Prop`-valued definition concerning actual line bundles on abelian schemes over
algebraically closed fields. It states the multiplication and inversion identities from
Edixhoven, van der Geer and Moonen, *Abelian Varieties*, Lemma (7.16), printed p.104 /
PDF p.108, in the form used in the proof of Lemma (7.19), printed p.105 / PDF p.109.
The module states a target for a later proof and adds no axiom.

## Complete checked Lean declaration

The module imports `Langlands.AlgebraicGeometry.Modules.Tensor` and
`Langlands.AlgebraicGeometry.Picard.GeometricPicardZero`. Its entire proposition is the
following declaration, in a `noncomputable section` with universe `u`:

```lean
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

def AlgClosedFieldTranslationInvariantPullbackIdentitiesStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (A : AbelianScheme (Spec (CommRingCat.of K)))
    (L : LineBundle A.X.left),
    GroupScheme.IsTranslationInvariant A.toGrp L →
      let P : Over (Spec (CommRingCat.of K)) := A.X ⨯ A.X
      let p1 : P ⟶ A.X := Limits.prod.fst
      let p2 : P ⟶ A.X := Limits.prod.snd
      let m : P ⟶ A.X := p1 * p2
      let i : A.X.left ⟶ A.X.left := ((𝟙 A.X : A.X ⟶ A.X)⁻¹).left
      Nonempty ((Scheme.Modules.pullback m.left).obj L.obj ≅
        Langlands.Scheme.Modules.tensorObj
          ((Scheme.Modules.pullback p1.left).obj L.obj)
          ((Scheme.Modules.pullback p2.left).obj L.obj)) ∧
      Nonempty (Langlands.Scheme.Modules.tensorObj L.obj
        ((Scheme.Modules.pullback i).obj L.obj) ≅
          Langlands.Scheme.Modules.structureSheaf A.X.left)

end Langlands.AbelianScheme
```

The approved Lean service checked this declaration with zero errors and warnings and
reported `statement_returns_prop: true`, with the sole universe parameter `u`. Its
checked type is

```text
Langlands.AbelianScheme.AlgClosedFieldTranslationInvariantPullbackIdentitiesStatement.{u} : Prop
```

The declaration has no outer parameters. All the field, abelian-scheme and line-bundle
binders occur inside the proposition. Its only premise about `L` is the existing
`GroupScheme.IsTranslationInvariant A.toGrp L`.

## Actual objects and maps

Write `S := Spec (CommRingCat.of K)`. The object `A.X` lies in `Over S`; its underlying
scheme is `A.X.left` and its structure morphism is `A.X.hom`. The `AbelianScheme` bundle
supplies smoothness, properness and geometric connectedness of that morphism, together
with the commutative group law.

The product `P := A.X ⨯ A.X` is taken in `Over S`, so `P.left` is the actual scheme fibre
product of `A` with itself over `S`. Both `p1 := Limits.prod.fst` and
`p2 := Limits.prod.snd` are morphisms `P ⟶ A.X`. The scoped group-object instance makes
this hom set a group. Thus `m := p1 * p2` is the morphism whose value on every test
scheme is the product of the two projected points, namely the actual addition on `A`.
The first conjunct compares the following objects of `P.left.Modules`:

- `(Scheme.Modules.pullback m.left).obj L.obj`, the sheaf `m^*L`;
- `Langlands.Scheme.Modules.tensorObj
    ((Scheme.Modules.pullback p1.left).obj L.obj)
    ((Scheme.Modules.pullback p2.left).obj L.obj)`, the sheaf `p1^*L ⊗ p2^*L`.

Similarly, `𝟙 A.X` is a member of the group `A.X ⟶ A.X`. Its group inverse is the
morphism inducing pointwise inversion. Consequently
`i := ((𝟙 A.X : A.X ⟶ A.X)⁻¹).left` is the actual inversion scheme map, and the second
conjunct compares the following objects of `A.X.left.Modules`:

- `Langlands.Scheme.Modules.tensorObj L.obj ((Scheme.Modules.pullback i).obj L.obj)`,
  the sheaf `L ⊗ i^*L`;
- `Langlands.Scheme.Modules.structureSheaf A.X.left`, the structure sheaf as a module
  over itself, defined as `SheafOfModules.unit A.X.left.ringCatSheaf`.

`Scheme.Modules.pullback` is Mathlib's pullback of actual module sheaves. The Library
`tensorObj` sheafifies the sectionwise tensor product of the underlying module
presheaves. `LineBundle X` is the full subcategory of actual `X.Modules` consisting of
locally free rank-one sheaves; its underlying sheaf is `L.obj`. Module-sheaf isomorphisms
therefore express the usual line-bundle identities. Pullback preserves local rank one,
and tensor products of line bundles have local rank one. These facts do not become
premises in this proposition.

Both conclusions use `Nonempty`: the statement asserts existence of isomorphisms and
does not choose one. No trivialization of the fibre of `L` at the identity is supplied,
so it makes no claim of a canonical isomorphism. The second conjunct expresses `i^*L`
as a tensor inverse directly, without introducing a chosen inverse line bundle.

## Source and translation of the hypotheses

The registered original is B. Edixhoven, G. van der Geer and B. Moonen, *Abelian
Varieties*, preliminary version of the first chapters, literature ID
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
The retained file is
`literature/Edixhoven, van der Geer, Moonen - Abelian Varieties (preliminary version of the first chapters).pdf`.
Printed pages are one-based PDF pages minus four. The original passages read for this
statement are printed pp.88–89, 95 and 104–105 / PDF pp.92–93, 99 and 108–109.

Lemma (7.16)(i) states the class identity
`[(f + g)^*L] = [f^*L ⊗ g^*L]` in `Pic_{Y/T}(T)` under `phi_L = 0`.
For multiplication, take `T = Spec K`, `Y = A ×_K A`, `f = p1` and `g = p2`.
Its proof identifies the discrepancy with a pullback of a line bundle from the base.
Every line bundle on `Spec K` is trivial, so this discrepancy has an actual
trivialization after a choice, giving an isomorphism of the two sheaves. Equivalently,
the exact sequence (1) of (6.2), printed p.88 / PDF p.92, identifies the kernel of
`Pic(Y) → Pic_{Y/K}(K)` with line bundles pulled back from `Spec K`, and
`Pic(Spec K) = 0`. The product `Y` has a rational identity section, as required by the
source's hypotheses. Lemma (7.16)(ii) includes `n = -1`; the resulting inverse identity
also follows by pulling back multiplication along `(id,-1)` as explained below.
Both actual identities appear in the proof of (7.19). No cohomology vanishing result
is needed for them.

Chapter VI §3, printed p.95 / PDF p.99, describes
`phi_L(x) = [t_x^*L ⊗ L^{-1}]`. The published predicate used here is exactly

```text
∀ x : Over.mk (𝟙 S) ⟶ A.X,
  Nonempty ((LineBundle.pullback (GroupScheme.translation A.toGrp x).left).obj L ≅ L).
```

For `S = Spec K`, these sections are precisely the `K`-rational points. Library
translation is `y ↦ x * y`, whereas the source writes `y ↦ y + x`; commutativity
identifies them. Mathematically, over algebraically closed `K`, this ordinary
rational-point invariance is equivalent to the source condition `phi_L = 0`.
One direction follows from the exact sequence in (6.2) and `Pic(Spec K) = 0`.
For the converse, invariance makes `phi_L` agree with zero on all `K`-points. The source
Picard scheme is separated by (6.3)(iii), printed p.89 / PDF p.93, so their equalizer is
closed. The smooth scheme `A` is reduced and of finite type over `K`; all its closed
points are `K`-rational, and they are dense. A closed subscheme containing all of them
has the full underlying space, and reducedness then forces that closed subscheme to
be all of `A`. Thus the two morphisms agree.

This is the mathematical interpretation of the source, not an asserted formal
comparison with a represented Picard functor. The declaration uses ordinary
`IsTranslationInvariant` directly and quantifies over no Picard scheme or dual.
It does not strengthen the hypothesis to translation invariance in arbitrary families.
The same interpretation and a bounded manuscript-version/errata audit are documented
in `TranslationInvariantCohomologyVanishingStatement.md`. On 2026-10-30 no source-specific
errata file was found under the checked project, Library or workspace `notes/errata`
locations; this records those local checks only.

## Obligations for a later exact proof

The proposition above is not proved in this module. A later proof must prove this
entire named proposition in every universe, with no additional outer hypotheses.
The rational-point hypothesis must be globalized; a cube identity by itself does not
supply this step.

A possible route compares `m^*L` with `p1^*L ⊗ p2^*L` as two line-bundle families over
one factor of `A ×_K A`. Over a rational parameter `x`, translation invariance and
triviality of the one-dimensional fibre of `L` give an isomorphism of these families.
Use the existing `NoetherianLineBundleSeesawStatement` for the closed locus of local
isomorphism over the parameter. Its proof is available as
`Langlands.AlgebraicGeometry.Picard.noetherianLineBundleSeesaw` in
`NoetherianLineBundleSeesawProof`; it requires properness, flatness, geometric
integrality, a noetherian parameter and the stated affine-base-change global-functions
condition. In the abelian-scheme setting, the existing
`Langlands.AbelianScheme.smoothGeometricIntegrality` and
`Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions` provide relevant
geometric inputs. A future application must instantiate the precise seesaw hypotheses
and transport the categorical product to its scheme-pullback presentation.

Every closed point of the parameter is a `K`-point, so the fibre comparisons put all
closed points in this closed locus. One must prove the closed-point detection step
for the reduced finite-type parameter and obtain local isomorphisms over all of it.
Normalize along the identity section, using a chosen field trivialization internally,
and glue compatible normalized isomorphisms. The published
`Langlands.AbelianScheme.rigidifiedClassesZariskiSeparated` in
`RigidifiedClassesZariskiSeparatedProof` is a possible gluing interface. One must still
verify the normalization, compatibility and descent comparisons and then forget the
normalization. These are proof obligations, not extra assumptions or results supplied
by this statement. Reuse the existing seesaw and equalizer interfaces rather than
creating a duplicate seesaw target.

For inversion, pull the multiplication isomorphism back along the categorical map
`j := Limits.prod.lift (𝟙 A.X) ((𝟙 A.X : A.X ⟶ A.X)⁻¹) : A.X ⟶ P`.
The group laws give `j ≫ m = 1`, the constant identity map, and the projection equations
give `j ≫ p1 = 𝟙 A.X` and `j ≫ p2 = (𝟙 A.X)⁻¹`. Tensor preservation and the actual
`Scheme.Modules.pullbackId` and `pullbackComp` comparisons then identify the right side
with `L ⊗ i^*L`. The left side is pulled back from the fibre of `L` at the identity,
a line bundle on `Spec K`, hence is trivial. Reverse this isomorphism to obtain exactly
the second conjunct. The existing `fieldLineBundleTriviality` and
`LineBundle.exists_tensorObj_iso_structureSheaf` are available for field triviality
and tensor-inverse manipulations. The unconditional Library theorem
`Langlands.Scheme.Modules.pullbackTensorComparisonIsIso` can discharge tensor
preservation internally; it is not a premise of the proposition.

The field cube target, any unpublished draft, the all-degree cohomology vanishing
statement, the parent translation-difference lifting statement, and downstream
Picard/dual existence are not proof inputs established here. The host retains its
cohomology assembly, and its separate pullback-on-cohomology work is independent of
this statement task.

## Scope and authorship

The field universe is arbitrary. The statement covers every characteristic and
includes dimension zero, the trivial line bundle and all other ordinarily
translation-invariant line bundles. There is no positivity or nontriviality premise.
No tensor-preservation, cube, seesaw, Picard-zero, rigidification, inverse choice,
compatibility, global-detection or representability premise occurs.

Worker 59 authored this pair. Workers 306 and 100 supplied the focused specification
and source/ownership context; Worker 306 also authored the source-interpretation text
in the cohomology statement consulted here. Their specification and source audit
informed the provenance and later-proof discussion. This is a focused statement
prerequisite of their cohomology proof task `a45129b4-368e-4cd9-813b-e2e884897b35`;
that target is not used to justify these identities. Existing operator pauses and
separate task ownership remain in force. Separate exact-target proof work follows
publication of this statement.
