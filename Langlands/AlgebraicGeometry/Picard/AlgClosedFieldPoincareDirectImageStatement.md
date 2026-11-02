# Higher direct images of the Poincaré bundle over an algebraically closed field

Authors: Worker 943 and Worker 360. This pair adapts Worker 943's shared draft;
Worker 360 checked the original theorem and the Library conventions.

Module `Langlands.AlgebraicGeometry.Picard.AlgClosedFieldPoincareDirectImageStatement`,
namespace `Langlands.AbelianScheme`, with
`open CategoryTheory CategoryTheory.Limits AlgebraicGeometry`,
`open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules` and
`open Langlands.AlgebraicGeometry.Modules.DerivedSections`. The file defines one
universe-polymorphic proposition, `AlgClosedFieldPoincareDirectImageStatement.{u}`. It does
not prove it.

## Complete proposition

```lean
def AlgClosedFieldPoincareDirectImageStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (hA : HasDualScheme A) (g : ℕ),
    A.HasRelativeDimension g →
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
`Langlands.AlgebraicGeometry.Modules.Tensor` and `Mathlib.FieldTheory.IsAlgClosed.Basic`.

## Meaning of the binders

All names are the published Library and Mathlib ones, used unchanged.

- `K` is an algebraically closed field in universe `u`, and
  `A : AbelianScheme (Spec (CommRingCat.of K))` is a published abelian scheme over `Spec K`
  (smooth, proper, geometrically connected commutative group scheme), that is, an abelian
  variety over `K`.
- `hA : HasDualScheme A` is the proposition that a universal rigidified Picard-zero family
  exists. `D := dualScheme A hA` is the chosen dual, an object of `Over (Spec K)`, and
  `poincareLineBundle A hA` is the line bundle of the chosen universal family
  `poincareFamily A hA`, transported to the total space `A ×_K D` (module
  `Langlands.AlgebraicGeometry.Picard.DualScheme`). The family is rigidified along the unit
  section of `A`.
- `g : ℕ` with `A.HasRelativeDimension g`, which is Mathlib's
  `SmoothOfRelativeDimension g A.X.hom`.
- `(baseChange D.hom).obj A` is the abelian scheme `A ×_K D` over `D`; its structure morphism
  `((baseChange D.hom).obj A).X.hom` is, by the definition of `AbelianScheme.baseChange`,
  Mathlib's `pullback.snd A.X.hom D.hom : pullback A.X.hom D.hom ⟶ D.left`, the projection
  `p : A ×_K D ⟶ D` to the dual factor. `poincareLineBundle A hA` is a line bundle on its
  source `((baseChange D.hom).obj A).X.left`, and `.obj` is its underlying sheaf of modules.
- `higherDirectImage p n` is the Library's `Rⁿ p_*` on actual module sheaves, Mathlib's
  right-derived functor `(Scheme.Modules.pushforward p).rightDerived n`, computed from chosen
  injective resolutions (module `Langlands.AlgebraicGeometry.Modules.DerivedSections`).
- `dualOrigin A hA : Over.mk (𝟙 (Spec K)) ⟶ D` is the Library's origin of the dual, the
  `K`-point classifying the trivial rigidified bundle, and `(dualOrigin A hA).left` is its
  underlying morphism `Spec K ⟶ D.left`. `structureSheaf (Spec K)` is the Library's
  structure sheaf as a module over itself, and `Scheme.Modules.pushforward` is Mathlib's
  pushforward. So the sections of
  `(Scheme.Modules.pushforward (dualOrigin A hA).left).obj (structureSheaf (Spec K))` over an
  open `U ⊆ D.left` are `K` if `U` contains the origin and zero otherwise: it is the
  skyscraper `𝒪_D`-module at the origin with value `K`.

The conclusion has two parts: `Rⁿ p_* P` is a zero object of `D.left.Modules` for every
`n ≠ g`, and there exists an isomorphism of `𝒪_D`-modules between `R^g p_* P` and the
skyscraper sheaf with value `K` at the origin. The quantifiers include `g = 0`
and fields of every characteristic.

## Source and correspondence

B. Edixhoven, G. van der Geer and B. Moonen, *Abelian Varieties* (registered source
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`), Theorem (9.1),
printed p.126 (PDF p.130). This theorem computes the higher direct images of
the Poincaré bundle under the second projection: they vanish outside degree
`g`, and in degree `g` give the skyscraper sheaf `i₀(k)` at the origin.
It also computes the cohomology of the Poincaré bundle. The original theorem
on PDF p.130 was read and its displayed formulas checked visually.

Correspondence:

- The source's `X` is `A`, of dimension `g` (`A.HasRelativeDimension g`), and its `X^t` is
  the Library's chosen dual `D`. The source's `P` is the Poincaré bundle, rigidified along
  `{0} × X^t`; the Lean statement uses the Library's chosen universal rigidified family,
  which is rigidified along the unit section of `A` and classifies Picard-zero line bundles,
  so it plays the role of the source's `P`.
- The factor order is the source's: `poincareLineBundle` lives on `A ×_K D`, and `p` is the
  projection to the second factor `D`, the source's `p₂`.
- The source's `i₀(k)` is the pushforward of the structure sheaf of `Spec K` along the
  origin `(dualOrigin A hA).left`. Its stalk is `K` at the origin and zero elsewhere.
- The source works over an arbitrary field `k`; the Lean statement assumes `K`
  algebraically closed, so it is narrower in this respect. This matches the Library's
  version of the source's (7.19),
  `Langlands.AbelianScheme.AlgClosedFieldTranslationInvariantCohomologyVanishingStatement`,
  which is also stated over algebraically closed fields and is used in the source's proof
  step (9.2).
- The Lean statement contains only the direct-image half of Theorem (9.1). The cohomology
  half `Hⁿ(X × X^t, P)` is not stated.
- For `R^g p_* P` the source gives an equality of sheaves, that is, an isomorphism; the Lean
  statement asserts that some isomorphism exists.

No source-specific errata note was present in the pinned Library's
`notes/errata/` or in the project `notes/errata/` location when checked.
This records those checked locations, without asserting that no errata exist
elsewhere.

## Role

Prerequisite of task `fc8e4732-8e1b-497e-adb1-c27ee538f442` (proof of
`Langlands.AbelianScheme.AlgClosedFieldAmpleMumfordEulerSquareStatement`), through the
dual-side interface `Langlands.AbelianScheme.AlgClosedFieldMumfordDualEulerStatement`
(statement task `2590f5a1-e1c2-4ec1-ade7-377e97a3e12f`). The source uses it together with
flat base change in the proof of the Riemann-Roch theorem (9.11), printed p.132 (PDF p.136),
to compute the higher direct images of the Mumford bundle `Λ(L) = (id × φ_L)^* P` and
`χ(Λ(L)) = (-1)^g · deg(φ_L)`.

This statement imports neither consumer statement nor any proof of either
consumer. It supplies no proof of the direct-image assertion.
