# Higher direct images of the Poincaré bundle when the chosen dual is smooth

Authors: Worker 3613 (shared draft) and Worker 944 (source and scope checks).

Module `Langlands.AlgebraicGeometry.Picard.AlgClosedFieldSmoothDualPoincareDirectImageStatement`,
namespace `Langlands.AbelianScheme`, with
`open CategoryTheory CategoryTheory.Limits AlgebraicGeometry`,
`open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules` and
`open Langlands.AlgebraicGeometry.Modules.DerivedSections`. The file defines one
universe-polymorphic proposition, `AlgClosedFieldSmoothDualPoincareDirectImageStatement.{u}`.
It does not prove it.

## Complete proposition

```lean
def AlgClosedFieldSmoothDualPoincareDirectImageStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (hA : HasDualScheme A) (g : ℕ),
    A.HasRelativeDimension g → SmoothOfRelativeDimension g (dualScheme A hA).hom →
      (∀ n : ℕ, n ≠ g →
        IsZero ((higherDirectImage ((baseChange (dualScheme A hA).hom).obj A).X.hom n).obj
          (poincareLineBundle A hA).obj)) ∧
      Nonempty ((higherDirectImage ((baseChange (dualScheme A hA).hom).obj A).X.hom g).obj
          (poincareLineBundle A hA).obj ≅
        (Scheme.Modules.pushforward (dualOrigin A hA).left).obj
          (structureSheaf (Spec (CommRingCat.of K))))
```

Imports: `Langlands.AlgebraicGeometry.Picard.DualScheme`,
`Langlands.AlgebraicGeometry.Modules.DerivedSections`,
`Langlands.AlgebraicGeometry.Modules.Tensor` and `Mathlib.FieldTheory.IsAlgClosed.Basic`,
the imports of the published `AlgClosedFieldPoincareDirectImageStatement`.

## Relation to the published universal statement

The proposition is the published
`Langlands.AbelianScheme.AlgClosedFieldPoincareDirectImageStatement` (module
`Langlands.AlgebraicGeometry.Picard.AlgClosedFieldPoincareDirectImageStatement`) with one
extra hypothesis, `SmoothOfRelativeDimension g (dualScheme A hA).hom`, placed after
`A.HasRelativeDimension g`. The conclusion is word for word the same. So the published
statement implies this one. Conversely, this one together with the published
`AlgClosedFieldDualSchemeRelativeDimensionStatement`, which supplies the extra hypothesis,
gives the published statement. The extra hypothesis lets a proof apply to one `A` whose dual
is known to be smooth of relative dimension `g`, without proving that every dual is.
Neither universal statement is a hypothesis or an import of this module; the only
assumptions are the displayed field, abelian-scheme, dual and relative-dimension data.

## Meaning of the binders

All names are the published Library and Mathlib ones, used unchanged. The Markdown of the
published `AlgClosedFieldPoincareDirectImageStatement` explains each of them in detail.

- `K` is an algebraically closed field in universe `u`, of any characteristic, and
  `A : AbelianScheme (Spec (CommRingCat.of K))` is an abelian variety over `K`.
- `hA : HasDualScheme A` asserts that a universal rigidified Picard-zero family exists;
  `D := dualScheme A hA` is the chosen dual, and `poincareLineBundle A hA` is the line bundle
  `P` of the chosen universal family on `A ×_K D`.
- `g : ℕ` with `A.HasRelativeDimension g`, Mathlib's `SmoothOfRelativeDimension g A.X.hom`,
  and the extra hypothesis that `D.hom : D.left ⟶ Spec K` is smooth of relative dimension `g`.
- `((baseChange D.hom).obj A).X.hom` is the projection `p : A ×_K D ⟶ D` to the dual factor,
  and `higherDirectImage p n` is the Library's `Rⁿ p_*`, Mathlib's right-derived functor of
  `Scheme.Modules.pushforward p`.
- `(dualOrigin A hA).left : Spec K ⟶ D.left` is the origin of the dual, and
  `(Scheme.Modules.pushforward (dualOrigin A hA).left).obj (structureSheaf (Spec K))` is the
  skyscraper `𝒪_D`-module at the origin with value `K`.

The conclusion: `Rⁿ p_* P` is a zero object for every `n ≠ g`, and some isomorphism of
`𝒪_D`-modules exists between `R^g p_* P` and the skyscraper sheaf at the origin. The
quantifiers include `g = 0`.

## Original source and derived formulation

B. Edixhoven, G. van der Geer and B. Moonen, *Abelian Varieties*, preliminary draft (registered
source `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`), Theorem (9.1), printed
p.126 (PDF p.130): the higher direct images of the Poincaré bundle under the second projection
vanish outside degree `g`, and in degree `g` give the skyscraper sheaf at the origin. Its
second proof, (9.6)–(9.9), uses that the dual is an abelian variety of dimension `g`, that is
Theorem (6.18) on p.96, at the local ring of the origin. These second-proof steps
are on printed pp.128–130 (PDF pp.132–134).

The statement is derived content. It is the direct-image half of Theorem (9.1) for the
Library's chosen dual, with the input from (6.18) stated as a hypothesis on the given `A`. The
correspondence with the source's objects, factor order and field is the same as for the
published `AlgClosedFieldPoincareDirectImageStatement`: the factors are ordered
`A ×_K D`, the source's `p₂` is the displayed structure morphism to `D`, and its
`i₀(k)` is the displayed origin pushforward. The source permits an arbitrary field; this
statement restricts to algebraically closed fields of every characteristic. It states only
the direct-image formula, not the source's additional global-cohomology formula. The
source's equality of sheaves is expressed as existence of an isomorphism (`Nonempty`).

No source-specific errata note was found in the pinned Library `notes/errata/`; the
project `notes/errata/` directory is absent. This records the checked locations without
asserting that no errata exist elsewhere.

## Role

Prerequisite of task `6b1ab3e8-b3b0-4567-9251-7566e7a6dba3`, the exact proof of
`Langlands.AbelianScheme.AlgClosedFieldMumfordDualEulerStatement`. There the extra
hypothesis is the relative-dimension conclusion of
`AlgClosedFieldFiniteMumfordDualGeometryStatement` for an `A` with a finite flat Mumford
map; that proposition requires its own proof. The published conditional assembly
`algClosedFieldPoincareDirectImage_of_relativeDimension` (module
`Langlands.AlgebraicGeometry.Picard.PoincareDirectImageAssembly`) shows how its proof can
reuse the published local computation.

The transitive imports contain neither `AlgClosedFieldMumfordDualEulerStatement` nor
`AlgClosedFieldAmpleMumfordEulerSquareStatement`, nor anything downstream of either.
