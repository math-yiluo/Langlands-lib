# The chosen dual under a finite flat Mumford map over an algebraically closed field

Authors: Worker 3613 (shared draft) and Worker 944 (source and scope checks).

Module `Langlands.AlgebraicGeometry.Picard.AlgClosedFieldFiniteMumfordDualGeometryStatement`,
namespace `Langlands.AbelianScheme`, with `open CategoryTheory AlgebraicGeometry` and
`open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules`. The file defines one
universe-polymorphic proposition, `AlgClosedFieldFiniteMumfordDualGeometryStatement.{u}`. It
does not prove it.

## Complete proposition

```lean
def AlgClosedFieldFiniteMumfordDualGeometryStatement : Prop :=
  ∀ (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (square : MumfordBundlePicardZeroStatement.{u})
    (K : Type u) [Field K] [IsAlgClosed K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (hA : HasDualScheme A)
    (L : RigidifiedLineBundle (unitSection A)) (M : LineBundle A.X.left)
    (evaluation : tensorObj L.obj.carrier M.obj ≅ structureSheaf A.X.left),
    IsFinite (mumfordSchemeMap preservation square A L M evaluation hA).left →
    Flat (mumfordSchemeMap preservation square A L M evaluation hA).left →
      (∀ y y' : (dualScheme A hA).left,
        (mumfordSchemeMap preservation square A L M evaluation hA).left.finrank y =
          (mumfordSchemeMap preservation square A L M evaluation hA).left.finrank y') ∧
      ∀ g : ℕ, A.HasRelativeDimension g → SmoothOfRelativeDimension g (dualScheme A hA).hom
```

Imports: `Langlands.AlgebraicGeometry.Picard.MumfordMap`,
`Mathlib.AlgebraicGeometry.Morphisms.Finite`, `Mathlib.AlgebraicGeometry.Morphisms.FlatRank`
and `Mathlib.FieldTheory.IsAlgClosed.Basic`.

## Meaning of the binders

All names are the published Library and Mathlib ones, used unchanged.

- `preservation : pullbackTensorComparisonIsIsoStatement.{u}` says the actual
  tensor/pullback comparison is an isomorphism for every scheme morphism in universe `u`.
  `square : MumfordBundlePicardZeroStatement.{u}` says the constructed Mumford family has
  translation-invariant geometric fibres. The Library's construction of the Mumford map
  takes these as inputs; they are the same two binders as in
  `AlgClosedFieldMumfordDualEulerStatement`. Neither input proposition is proved here.
- `K` is an algebraically closed field in universe `u`, of any characteristic, and
  `A : AbelianScheme (Spec (CommRingCat.of K))` is an abelian variety over `K`.
- `hA : HasDualScheme A` asserts that a universal rigidified Picard-zero family exists;
  `D := dualScheme A hA` is the chosen dual, an object of `Over (Spec K)`, and `D.hom` is its
  structure morphism `D.left ⟶ Spec K`.
- `L : RigidifiedLineBundle (unitSection A)` is a line bundle on `A` rigidified along
  its unit section. `M : LineBundle A.X.left` is any line bundle on `A`, and
  `evaluation : tensorObj L.obj.carrier M.obj ≅ structureSheaf A.X.left` is an actual
  isomorphism exhibiting `M` as the tensor inverse of `L`. No ampleness is imposed on `L`. Write
  `f := mumfordSchemeMap preservation square A L M evaluation hA : A.X ⟶ D`, the Library's
  Mumford map, the source's `φ_L`.

The hypotheses are Mathlib's `IsFinite` and `Flat` for the underlying scheme morphism
`f.left`. The conclusion has two parts.

1. `f.left.finrank y = f.left.finrank y'` for all points `y`, `y'` of `D.left`, closed or not.
   `Scheme.Hom.finrank` is Mathlib's rank of `f_* 𝒪_A` at a point (module
   `Mathlib.AlgebraicGeometry.Morphisms.FlatRank`), the degree of `f` over that point.
2. For every `g : ℕ` with `A.HasRelativeDimension g`, which is Mathlib's
   `SmoothOfRelativeDimension g A.X.hom`, the structure morphism `D.hom` is also
   `SmoothOfRelativeDimension g`. The quantifier includes `g = 0`.

## Original source and derived formulation

B. Edixhoven, G. van der Geer and B. Moonen, *Abelian Varieties*, preliminary draft (registered
source `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`). Theorem (6.18), printed
p.96 (PDF p.100): for an abelian variety `X` over a field `k`, `Pic⁰_{X/k}` is reduced, hence
an abelian variety; for every ample `L`, `φ_L : X → Pic⁰_{X/k}` is an isogeny with kernel
`K(L)`; and `dim Pic⁰_{X/k} = dim X`. Definition (6.19) on the same page names
`X^t := Pic⁰_{X/k}` the dual.

The statement is derived content:

- The source's proof uses the ample `L` only through finiteness of `K(L)`, which gives
  `dim Pic⁰ ≥ dim X`. Here the Mumford map is assumed finite and flat instead, and no ample
  line bundle is assumed to exist.
- Part 1 is the statement that the isogeny `φ_L` has a well-defined degree: an isogeny is
  finite flat and surjective onto the connected `X^t`, so its rank is constant.
- Part 2 combines two claims of (6.18): the dual is an abelian variety, hence smooth, and
  its dimension is `dim X`.
- The source's `Pic⁰_{X/k}` is replaced by the Library's chosen parameter scheme
  `dualScheme A hA`, as in the published
  `Langlands.AbelianScheme.AlgClosedFieldDualSchemeRelativeDimensionStatement`. Part 2 is
  that published statement for one `A` that has a finite flat Mumford map.
- The source permits an arbitrary field; this statement restricts to algebraically closed
  fields of every characteristic because that is the case the consumer needs.

No projectivity, Noetherian, or additional dual-existence premise is added: the only
existence datum is the quantified `hA`. No source-specific errata note was found in the
pinned Library `notes/errata/`; the project `notes/errata/` directory is absent. This
records the checked locations without asserting that no errata exist elsewhere.

## Role

Prerequisite of task `6b1ab3e8-b3b0-4567-9251-7566e7a6dba3`, the exact proof of
`Langlands.AbelianScheme.AlgClosedFieldMumfordDualEulerStatement`. Part 1 turns the Euler
characteristic at the origin of the dual into the formula at every point `y`. Part 2 is the
hypothesis of `AlgClosedFieldSmoothDualPoincareDirectImageStatement`, which computes the
higher direct images of the Poincaré bundle.

The transitive imports contain neither `AlgClosedFieldMumfordDualEulerStatement` nor
`AlgClosedFieldAmpleMumfordEulerSquareStatement`, nor anything downstream of either.
