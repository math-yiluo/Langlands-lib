# Cohomology vanishing for nontrivial translation-invariant line bundles

`Langlands.AbelianScheme.AlgClosedFieldTranslationInvariantCohomologyVanishingStatement`
is a universe-polymorphic `Prop`-valued definition for actual line bundles
on abelian schemes over algebraically closed fields. It is the
algebraically closed field form of Edixhoven, van der Geer and Moonen,
*Abelian Varieties*, Lemma (7.19), printed p.105 / PDF p.109. The module
states the proposition only. It supplies no proof and adds no axiom.

## Statement

For every universe `u`, every field `K : Type u` with `IsAlgClosed K`,
every `A : AbelianScheme (Spec (CommRingCat.of K))` and every actual line
bundle `L : LineBundle A.X.left`, the proposition says

```text
GroupScheme.IsTranslationInvariant A.toGrp L →
  ¬ Nonempty (L ≅ LineBundle.trivial A.X.left) →
  ∀ n : ℕ,
    IsZero ((DerivedSections.relativeCohomology A.X.hom n).obj L.obj).
```

In words: if `L` is preserved up to isomorphism by translation by every
`K`-rational point, and `L` is not isomorphic to the structure line bundle,
then the `K`-module `Hⁿ(A, L)` is zero for every natural number `n`,
including `n = 0`.

## Complete checked type

The source declaration is

```lean
def AlgClosedFieldTranslationInvariantCohomologyVanishingStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (A : AbelianScheme (Spec (CommRingCat.of K)))
    (L : LineBundle A.X.left),
    GroupScheme.IsTranslationInvariant A.toGrp L →
    ¬ Nonempty (L ≅ LineBundle.trivial A.X.left) →
      ∀ n : ℕ, IsZero ((DerivedSections.relativeCohomology A.X.hom n).obj L.obj)
```

inside `namespace Langlands.AbelianScheme`, with
`open CategoryTheory CategoryTheory.Limits AlgebraicGeometry` and
`open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.Modules`.
The module imports only `Langlands.AlgebraicGeometry.Modules.DerivedSections`,
`Langlands.AlgebraicGeometry.Picard.GeometricPicardZero` and
`Mathlib.FieldTheory.IsAlgClosed.Basic`. With `pp.fieldNotation false`,
`pp.proofs true` and `pp.funBinderTypes true`, `#print` in the approved
environment reports:

```text
def Langlands.AbelianScheme.AlgClosedFieldTranslationInvariantCohomologyVanishingStatement.{u} : Prop :=
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
      ∀ (n : ℕ),
        CategoryTheory.Limits.IsZero
          (CategoryTheory.Functor.obj
            (Langlands.AlgebraicGeometry.Modules.DerivedSections.relativeCohomology
              (CategoryTheory.Over.hom
                (CategoryTheory.Grp.X (Langlands.CommGroupScheme.toGrp (Langlands.AbelianScheme.toCommGroupScheme A))))
              n)
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
  algebraically closed field, smoothness and connectedness make `A.X.left`
  an integral variety, and properness makes it complete. This matches the
  source's variety convention (0.4), printed p.1 / PDF p.5, and its
  definition (1.3) of an abelian variety, printed p.6 / PDF p.10.
- `LineBundle X` is the full subcategory of actual `X.Modules` that are
  locally isomorphic to the structure sheaf. Its underlying sheaf of
  modules is `L.obj`. An isomorphism of line bundles is an isomorphism of
  the underlying sheaves of modules.
- `LineBundle.trivial X` is the actual structure sheaf
  `SheafOfModules.unit X.ringCatSheaf`, viewed as a line bundle. So
  `¬ Nonempty (L ≅ LineBundle.trivial A.X.left)` is the source condition
  `L ≇ O_X`. No isomorphism class, rigidification or chosen trivialization
  is part of the quantified data.
- A section `x : Over.mk (𝟙 (Spec K)) ⟶ A.X` is a `K`-rational point of
  `A`. `GroupScheme.translation A.toGrp x` is
  `(Over.mkIdTerminal.from A.X ≫ x) * 𝟙 A.X`, the translation built from
  the actual group law. On `T`-points it sends `y` to `x_T * y`.
- `GroupScheme.IsTranslationInvariant A.toGrp L` means that for every such
  section `x`, `(LineBundle.pullback (translation A.toGrp x).left).obj L ≅ L`
  in `LineBundle A.X.left`. Here `LineBundle.pullback` is the actual sheaf
  pullback restricted to line bundles.
- `DerivedSections.relativeCohomology f n`, for `f : X ⟶ Spec R`, is by
  definition `(relativeGlobalSections f).rightDerived n`, where
  `relativeGlobalSections f = Scheme.Modules.pushforward f ⋙ moduleSpecΓFunctor`.
  It is a functor from actual `X.Modules` to `ModuleCat R`, computed with
  injective resolutions in the abelian category `X.Modules`. Here
  `f = A.X.hom` and `R = CommRingCat.of K`, whose carrier is `K`, so
  `(relativeCohomology A.X.hom n).obj L.obj` is the actual `K`-module
  `Hⁿ(A, L)`. In degree zero the published `relativeCohomologyZeroIso`
  identifies it with the global sections of `L` as a `K`-module.
- `IsZero` is categorical zero in `ModuleCat K`. A module is a zero object
  exactly when its only element is zero.

No cohomology module, comparison isomorphism or vanishing fact is supplied
as a hypothesis.

## Original source and errata check

The original is B. Edixhoven, G. van der Geer and B. Moonen, *Abelian
Varieties*, preliminary version of the first chapters, registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`,
retained as
`literature/Edixhoven, van der Geer, Moonen - Abelian Varieties (preliminary version of the first chapters).pdf`.
Printed page numbers are PDF page numbers minus four.

Chapter VII §3 begins on printed p.101 (PDF p.105) with "Let `X` be an
abelian variety over a field `k`". Lemma (7.19), printed p.105 (PDF p.109),
reads: "Let `L` be a line bundle on `X` with `φ_L = 0`. If `L ≇ O_X` then
`H^i(X, L) = 0` for all `i`." The text just before it says that the lemma
works over a field and has no straightforward generalization to the
relative setting.

The statement here is this lemma with the field restricted to be
algebraically closed, `X` replaced by `A.X.left`, the condition `φ_L = 0`
expressed by translation invariance as explained below, and `H^i(X, L)`
read as the published right-derived functor of actual relative global
sections. The source quantifies over all `i`; the statement quantifies over
all `n : ℕ`, including degree zero. These are derived translations of the
source, not additional source hypotheses. The source cohomology is ordinary
sheaf cohomology. The Library computes right-derived functors in the
category of sheaves of `𝒪_A`-modules. These agree by the standard
comparison (Hartshorne, *Algebraic Geometry*, III.2.6), which the Library
has not formalized and this statement does not claim.

On 2026-10-29 the [author's manuscript](https://van-der-geer.nl/AV.pdf)
was fetched and had the same SHA256 as the registered original. The
[author's page](https://van-der-geer.nl/index.html) links the manuscript
without a source-specific errata link. The book section of
[Moonen's research page](https://www.math.ru.nl/~bmoonen/research.html)
posts preliminary chapters and directs book questions to van der Geer; it
gives no errata for this manuscript. No source-specific errata note was
present in the project, Library or workspace `notes/errata/` locations.
This records the locations checked; it does not assert that no errata
exist.

The published parent statement `AlgClosedFieldTranslationDifferenceLiftingStatement`
documents an apparent cross-reference slip in the proof of (7.21), printed
p.106 / PDF p.110: the finite-support argument cites (7.15), whereas its
repeated vanishing argument uses (7.19) and (7.20). This does not affect
the statement of (7.19).

## The condition `φ_L = 0` as translation invariance

This is the same interpretation as in the published
`AlgClosedFieldTranslationDifferenceLiftingStatement` Markdown. Chapter VI
§3, printed p.95 / PDF p.99, defines `φ_L : X → Pic_{X/k}`; on points it is

```text
φ_L(x) = [t_x^* L ⊗ L⁻¹].
```

The source's `t_x` is translation `y ↦ y + x`, and the Library translation
is `y ↦ x * y`. They agree because the Library group law is commutative.
The sections `x` quantified in `IsTranslationInvariant` are exactly the
`K`-rational points.

Mathematically, over an algebraically closed field, `φ_L = 0` if and only
if `t_x^*L ≅ L` for every `x ∈ A(K)`.

- If `φ_L = 0`, every class `[t_x^*L ⊗ L⁻¹]` is zero in `Pic_{A/K}(K)`.
  Sequence (1) of (6.2), printed p.88 / PDF p.92, says the kernel of
  `Pic(A) → Pic_{A/K}(K)` consists of pullbacks from `Pic(Spec K) = 0`.
  So `t_x^*L ⊗ L⁻¹` is trivial and `t_x^*L ≅ L`.
- Conversely, if `t_x^*L ≅ L` for every `x ∈ A(K)`, then `φ_L` and the
  zero morphism agree at every `K`-point. The source Picard scheme is
  separated by (6.3)(iii), printed p.89 / PDF p.93, so the locus where they
  agree is a closed subscheme of `A`. Since `A` is reduced and of finite
  type over the algebraically closed `K`, its `K`-points are its closed
  points and are dense in every closed subset. The locus contains every
  closed point, so it is all of the reduced scheme `A`, and `φ_L = 0`.

Thus over an algebraically closed field the source hypothesis `φ_L = 0` is
exactly `IsTranslationInvariant A.toGrp L`. The Lean statement uses
translation invariance directly. It asserts no formal comparison with a
Picard scheme, a rigidified family, a chosen dual or a geometric
Picard-zero certificate. `TranslationBaseChange.isTranslationInvariant_of_isGeometricallyPicardZero`
derives this hypothesis from the Library's geometric-fibre Picard-zero
condition over an algebraically closed field; it is not used here.

## Proof obligations for the later exact proof

After independent acceptance and publication, a separate exact-target proof
must have this entire named proposition as its type, with no extra outer
hypotheses. The source proof has two steps; neither is proved here.

1. Degree zero. From translation invariance derive `(-1)^*L ≅ L⁻¹`. A
   nonzero section of `L` then gives, by pullback under `-1`, a nonzero
   section of `L⁻¹`. On the proper integral variety `A` their product is a
   nonzero global function, hence a nonzero constant. So both sections are
   nowhere vanishing and `L` is trivial. Nontriviality gives
   `H⁰(A, L) = 0`.
2. Positive degree. Derive the actual isomorphism
   `m^*L ≅ p₁^*L ⊗ p₂^*L` on `A × A`. Lemma (7.16), printed p.104 /
   PDF p.108, gives the source Picard-class identities; over a field the
   passage to actual line bundles uses that line bundles on the base are
   trivial. Let `i ≥ 1` be least with `Hⁱ(A, L) ≠ 0`. The coherent Künneth
   formula gives

   ```text
   Hⁱ(A × A, m^*L) ≅ ⨁_{a+b=i} Hᵃ(A, L) ⊗_K Hᵇ(A, L).
   ```

   Terms with `a = 0` or `b = 0` vanish by step 1; every other term has
   `a < i`, so it vanishes by minimality. The map `j : A → A × A`,
   `x ↦ (x, 0)`, satisfies `m ∘ j = id`. Functorial pullback on cohomology
   makes the identity of `Hⁱ(A, L)` factor through the zero module
   `Hⁱ(A × A, m^*L)`, a contradiction.

A later exact proof must therefore implement, for the published
`relativeCohomology`, the actual inversion and multiplication comparisons,
the degree-zero argument, coherent Künneth in every required degree, and
pullback functoriality along `j` and `m` with the coefficient
identifications. The published cohomology foundation alone does not supply
these. Substantial missing inputs need separate definitions, statements and
unconditional proofs in dependency order; conditional assembly is not a
proof of this proposition. Multiplication and inversion inputs should reuse
the existing field cube and Mumford-bundle work, and Künneth and pullback
inputs should be coordinated with the existing coherent-cohomology and
base-change work. Neither the parent lifting statement nor any downstream
dual existence may be used to prove this prerequisite.

## Scope

The statement covers every universe `u`, every algebraically closed field
in every characteristic, every degree including zero, and every dimension.
No positive-dimension hypothesis occurs. Mathematically, in dimension zero
`A.X.left` is isomorphic to `Spec K`, every line bundle on it is trivial,
and the nontriviality hypothesis cannot hold.

The only hypotheses on `L` are ordinary translation invariance and
nontriviality. The target contains no tensor operation, so there is no
tensor-preservation binder. No cube, Künneth, cohomology-vanishing,
comparison, compatibility, ample, projectivity, Picard, dual or existence
premise is added. Publication of this statement records a target for a
later proof; it is not a vanishing theorem.

## Role and authorship

This is a focused prerequisite of Worker 516's exact proof
`0d978728-03a8-4f05-b45c-8ec83a017647` of the parent
`AlgClosedFieldTranslationDifferenceLiftingStatement`; it is obligation 3
in the parent Markdown. The parent is not used to justify it.

Worker 921 implemented the Lean declaration and this Markdown. Worker 306
audited the original source and errata and drafted the provenance,
interpretation and proof-obligation sections. Worker 516 supplied the
focused specification, including the binders and the conclusion.
