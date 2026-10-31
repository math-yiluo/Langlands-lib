# Degree-zero vanishing for nontrivial translation-invariant line bundles

`Langlands.AbelianScheme.AlgClosedFieldTranslationInvariantH0VanishingStatement`
is a universe-polymorphic `Prop`-valued definition for actual line bundles
on abelian schemes over algebraically closed fields. It is the degree-zero
case of Edixhoven, van der Geer and Moonen, *Abelian Varieties*,
Lemma (7.19), printed p.105 / PDF p.109, over an algebraically closed
field. The first paragraph of the source proof treats this case. The
module states the proposition only. It supplies no proof and adds no axiom.

## Statement

For every universe `u`, every field `K : Type u` with `IsAlgClosed K`,
every `A : AbelianScheme (Spec (CommRingCat.of K))` and every actual line
bundle `L : LineBundle A.X.left`, the proposition says

```text
GroupScheme.IsTranslationInvariant A.toGrp L →
  ¬ Nonempty (L ≅ LineBundle.trivial A.X.left) →
  IsZero ((DerivedSections.relativeCohomology A.X.hom 0).obj L.obj).
```

In words: if `L` is preserved up to isomorphism by translation by every
`K`-rational point, and `L` is not isomorphic to the structure line bundle,
then the `K`-module `H⁰(A, L)` is zero.

## Complete checked type

The source declaration is

```lean
def AlgClosedFieldTranslationInvariantH0VanishingStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (A : AbelianScheme (Spec (CommRingCat.of K)))
    (L : LineBundle A.X.left),
    GroupScheme.IsTranslationInvariant A.toGrp L →
    ¬ Nonempty (L ≅ LineBundle.trivial A.X.left) →
      IsZero ((DerivedSections.relativeCohomology A.X.hom 0).obj L.obj)
```

inside `namespace Langlands.AbelianScheme`, with
`open CategoryTheory CategoryTheory.Limits AlgebraicGeometry` and
`open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.Modules`.
The module imports only `Langlands.AlgebraicGeometry.Modules.DerivedSections`,
`Langlands.AlgebraicGeometry.Picard.GeometricPicardZero` and
`Mathlib.FieldTheory.IsAlgClosed.Basic`. It declares nothing else.

The approved Lean service compiled the module with no errors or warnings,
reported that the declaration returns `Prop` with sole universe parameter
`u`, and found only the axioms `propext`, `Classical.choice` and
`Quot.sound` in its dependencies. With `pp.fieldNotation false`,
`pp.proofs true` and `pp.funBinderTypes true`, `#print` reports:

```text
def Langlands.AbelianScheme.AlgClosedFieldTranslationInvariantH0VanishingStatement.{u} : Prop :=
∀ (K : Type u) [inst : Field K] [IsAlgClosed K] (A : Langlands.AbelianScheme (AlgebraicGeometry.Spec ↧K))
  (L :
    Langlands.AlgebraicGeometry.Picard.LineBundle
      (CategoryTheory.Over.left
        (CategoryTheory.Grp.X (Langlands.CommGroupScheme.toGrp (Langlands.AbelianScheme.toCommGroupScheme A))))),
  Langlands.GroupScheme.IsTranslationInvariant
      (Langlands.CommGroupScheme.toGrp (Langlands.AbelianScheme.toCommGroupScheme A)) L →
    ¬Nonempty
          (L ≅
            Langlands.AlgebraicGeometry.Picard.LineBundle.trivial
              (CategoryTheory.Over.left
                (CategoryTheory.Grp.X
                  (Langlands.CommGroupScheme.toGrp (Langlands.AbelianScheme.toCommGroupScheme A))))) →
      CategoryTheory.Limits.IsZero
        (CategoryTheory.Functor.obj
          (Langlands.AlgebraicGeometry.Modules.DerivedSections.relativeCohomology
            (CategoryTheory.Over.hom
              (CategoryTheory.Grp.X (Langlands.CommGroupScheme.toGrp (Langlands.AbelianScheme.toCommGroupScheme A))))
            0)
          (CategoryTheory.ObjectProperty.FullSubcategory.obj L))
```

and `#check` reports type `Prop`. Here `↧K` is `CommRingCat.of K`, and
`A.X` abbreviates `Grp.X (CommGroupScheme.toGrp (toCommGroupScheme A))`.

## Library objects used

The statement uses only published definitions. It introduces no new data,
structure, certificate or axiom.

- `A : AbelianScheme S` is the published bundle: a commutative group scheme
  over `S` whose structure morphism `A.X.hom : A.X.left ⟶ S` is smooth,
  proper and geometrically connected. Here `S = Spec K`. Over the
  algebraically closed field these conditions make `A.X.left` a complete
  integral variety, matching the source's convention (0.4), printed p.1 /
  PDF p.5, and its definition (1.3) of an abelian variety, printed p.6 /
  PDF p.10.
- `LineBundle X` is the full subcategory of actual `X.Modules` that are
  locally isomorphic to the structure sheaf. Its underlying sheaf of
  modules is `L.obj`. An isomorphism of line bundles is an isomorphism of
  the underlying sheaves of modules.
- `LineBundle.trivial X` is the actual structure sheaf
  `SheafOfModules.unit X.ringCatSheaf`, viewed as a line bundle. So
  `¬ Nonempty (L ≅ LineBundle.trivial A.X.left)` is the source condition
  `L ≇ O_X`.
- A section `x : Over.mk (𝟙 (Spec K)) ⟶ A.X` is a `K`-rational point of
  `A`. `GroupScheme.translation A.toGrp x` is
  `(Over.mkIdTerminal.from A.X ≫ x) * 𝟙 A.X`, the translation built from
  the actual group law. On `T`-points it sends `y` to `x_T * y`.
- `GroupScheme.IsTranslationInvariant A.toGrp L` means that for every such
  section `x`, `(LineBundle.pullback (translation A.toGrp x).left).obj L ≅ L`
  in `LineBundle A.X.left`. Here `LineBundle.pullback` is the actual sheaf
  pullback restricted to line bundles.
- `DerivedSections.relativeCohomology f 0`, for `f : X ⟶ Spec R`, is by
  definition `(relativeGlobalSections f).rightDerived 0`, where
  `relativeGlobalSections f = Scheme.Modules.pushforward f ⋙ moduleSpecΓFunctor`.
  It is a functor from actual `X.Modules` to `ModuleCat R`. Here
  `f = A.X.hom` and `R = CommRingCat.of K`, whose carrier is `K`.
  The published `relativeCohomologyZeroIso` identifies
  `relativeCohomology f 0` with `relativeGlobalSections f`, and the published
  `relativeGlobalSectionsIso`, whose components are identities, identifies
  the latter with `globalSections X` followed by restriction of scalars along
  `structureRingHom f : R ⟶ Γ(X, ⊤)`. So
  `(relativeCohomology A.X.hom 0).obj L.obj` is, up to these published
  isomorphisms, the `K`-module of global sections of `L`.
- `IsZero` is categorical zero in `ModuleCat K`. A module is a zero object
  exactly when its only element is zero.

No cohomology module, comparison isomorphism, section certificate or
vanishing fact is supplied as a hypothesis.

## Original source and errata check

The original is B. Edixhoven, G. van der Geer and B. Moonen, *Abelian
Varieties*, preliminary version of the first chapters, registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`,
retained as
`literature/Edixhoven, van der Geer, Moonen - Abelian Varieties (preliminary version of the first chapters).pdf`.
Printed page numbers are PDF page numbers minus four. The retained file was
checked against this SHA256 on 2026-10-31.

Chapter VII §3 begins on printed p.101 (PDF p.105) with "Let `X` be an
abelian variety over a field `k`". Lemma (7.19), printed p.105 (PDF p.109),
reads: "Let `L` be a line bundle on `X` with `φ_L = 0`. If `L ≇ O_X` then
`H^i(X, L) = 0` for all `i`." The text just before it says that the lemma
works over a field and has no straightforward generalization to the
relative setting. The first paragraph of the proof treats `H^0`:

> If there is a non-trivial section `s` then `(−1)^*s` is a non-trivial
> section of `(−1)^*L ≅ L^{-1}`; so both `L` and `L^{-1}` have a
> non-trivial section, and this implies that `L` is trivial. Since we have
> assumed this is not the case, `H^0(X, L) = {0}`.

The isomorphism `(−1)^*L ≅ L^{-1}` is the case `n = −1` of Lemma (7.16)(ii),
printed p.104 / PDF p.108, which gives `[n^*L] = [L^n]` in the Picard
functor when `φ_L = 0`.

The statement here is the case `i = 0` of the lemma, with the field
restricted to be algebraically closed, `X` replaced by `A.X.left`, the
condition `φ_L = 0` expressed by translation invariance as explained below,
and `H^0(X, L)` read as the published degree-zero right-derived functor of
actual relative global sections. These are derived translations of the
source, not additional source hypotheses. In degree zero no comparison with
ordinary sheaf cohomology is needed: `relativeCohomologyZeroIso` is already
a published isomorphism with global sections.

The errata and version audit is the one recorded in the published
`TranslationInvariantCohomologyVanishingStatement.md`: on 2026-10-29 the
author's manuscript at <https://van-der-geer.nl/AV.pdf> had the same SHA256
as the registered original, and neither the authors' pages nor the project
gave source-specific errata. On 2026-10-31 the project `notes/errata`,
Library `notes/errata` and workspace `notes/errata` locations did not exist.
This records the locations checked; it does not assert that no errata
exist. No discrepancy affecting the case `i = 0` was found.

## The condition `φ_L = 0` as translation invariance

The interpretation is the one documented in the published
`TranslationInvariantCohomologyVanishingStatement.md` and
`AlgClosedFieldTranslationDifferenceLiftingStatement.md`. Chapter VI §3,
printed p.95 / PDF p.99, defines `φ_L : X → Pic_{X/k}`; on points
`φ_L(x) = [t_x^* L ⊗ L⁻¹]`. The source's `t_x` is translation `y ↦ y + x`,
and the Library translation is `y ↦ x * y`; they agree because the Library
group law is commutative. The sections `x` quantified in
`IsTranslationInvariant` are exactly the `K`-rational points.

Over an algebraically closed field, `φ_L = 0` if and only if `t_x^*L ≅ L`
for every `x ∈ A(K)`. If `φ_L = 0`, every class `[t_x^*L ⊗ L⁻¹]` vanishes
in `Pic_{A/K}(K)`, and sequence (1) of (6.2), printed p.88 / PDF p.92,
with `Pic(Spec K) = 0` makes `t_x^*L ⊗ L⁻¹` trivial. Conversely, if
`t_x^*L ≅ L` for every `x ∈ A(K)`, then `φ_L` and the zero morphism agree
at every `K`-point; the Picard scheme is separated by (6.3)(iii), printed
p.89 / PDF p.93, so they agree on a closed subscheme containing every closed
point of the reduced finite-type `K`-scheme `A`, hence on all of `A`.

The Lean statement uses translation invariance directly. It asserts no
formal comparison with a Picard scheme, a rigidified family, a chosen dual
or a geometric Picard-zero certificate.

## Proof route for the later exact proof

After independent acceptance and publication, a separate exact-target proof
must have this entire named proposition as its type, with no extra outer
hypotheses. Nothing below is proved here. The intended route follows the
source paragraph quoted above.

1. Inversion pullback is a tensor inverse. Let
   `i := ((𝟙 A.X : A.X ⟶ A.X)⁻¹).left` be the actual inversion. Ordinary
   translation invariance should give
   `tensorObj L.obj ((Scheme.Modules.pullback i).obj L.obj) ≅ structureSheaf A.X.left`.
   This is the second conjunct of the published statement
   `AlgClosedFieldTranslationInvariantPullbackIdentitiesStatement`
   (EVM (7.16)), whose unconditional proof is a separate task and an
   intended input. `LineBundle.exists_tensorObj_iso_structureSheaf`
   supplies the dual as some tensor inverse; the inversion pullback is the
   specific inverse the source uses.
2. Degree zero is global sections. By `relativeCohomologyZeroIso` and
   `relativeGlobalSectionsIso`, it suffices to show that every global
   section `s` of `L.obj` is zero. The proof must use these published
   isomorphisms on the actual derived object; it must not introduce a new
   cohomology certificate.
3. A nonzero product. Suppose `s ≠ 0`. Since `i` is an isomorphism,
   `i^*s` is a nonzero global section of `i^*L`. The scheme `A.X.left` is
   integral: `Langlands.AbelianScheme.smoothGeometricIntegrality` makes
   the smooth geometrically connected structure morphism geometrically
   integral, and base change along the identity of `Spec K` gives
   integrality of `A.X.left` itself. On an integral scheme, nonzero sections of line bundles are
   nonzero on every nonempty open set and locally are nonzero elements of a
   domain, so `s ⊗ i^*s` is a nonzero global section of `L ⊗ i^*L`. Through
   the isomorphism of step 1 it is a nonzero global function `g` on `A`.
4. The product is a nonzero constant. The structure morphism is smooth,
   proper and geometrically connected, so
   `Langlands.AlgebraicGeometry.fieldSmoothProperConnectedGlobalFunctions`
   makes `A.X.hom.appTop` an isomorphism, and global functions on `A` are
   the constants `K`. Hence `g` is a unit, so it is nowhere vanishing.
5. The section trivializes `L`. Since `s ⊗ i^*s` generates the stalk of
   `L ⊗ i^*L` at every point, `s` generates every stalk of `L`. The
   morphism `structureSheaf A.X.left ⟶ L.obj` given by `s` is therefore an
   isomorphism, contradicting `¬ Nonempty (L ≅ LineBundle.trivial A.X.left)`.

Published section tools that may serve steps 3 and 5 include
`Langlands.SchemeModule.tensorSection` in `Modules/TensorSections.lean` and
the section-locus material in `Modules/SectionLocus.lean`. Substantial missing inputs need separate
definitions, statements and unconditional proofs in dependency order. A
conditional assembly that assumes the inversion identity or
global-functions rigidity as hypotheses is not a proof of this proposition.

Mathematically, this proposition is the `n = 0` instance of the published
`AlgClosedFieldTranslationInvariantCohomologyVanishingStatement`. It is a
prerequisite of that all-degree theorem, so neither the all-degree
statement nor any proof of it may be used to prove this one. Neither the
parent `AlgClosedFieldTranslationDifferenceLiftingStatement` nor any
downstream dual or Picard existence may be used either.

## Scope

The statement covers every universe `u`, every algebraically closed field
in every characteristic, and every dimension. No positive-dimension
hypothesis occurs. Mathematically, in dimension zero `A.X.left` is
isomorphic to `Spec K`, every line bundle on it is trivial, and the
nontriviality hypothesis cannot hold.

The only hypotheses on `L` are ordinary translation invariance and
nontriviality. No inversion, multiplication, Künneth, cohomology-vanishing,
comparison, global-functions, ample, Picard, dual or existence premise is
added. Publication of this statement records a target for a later proof;
it is not a vanishing theorem.

## Role and authorship

This is a focused prerequisite of the exact proof task
`a45129b4-368e-4cd9-813b-e2e884897b35` of
`AlgClosedFieldTranslationInvariantCohomologyVanishingStatement`, retained
by Workers 306 and 100. That target is not an input here.

Worker 1135 implemented the Lean declaration and this Markdown. Workers 306
and 100 specified the task, including the binders, the degree-zero
conclusion and the proof route. The source quotation, the translation-
invariance interpretation and the errata audit reuse the published
`TranslationInvariantCohomologyVanishingStatement.md` by Workers 921, 306
and 516, rechecked against the registered original.
