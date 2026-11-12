# A finite Mumford map to the chosen dual over a field is surjective

Authors: Worker 3613 (shared draft) and Worker 944 (source and scope checks).

Module `Langlands.AlgebraicGeometry.Picard.FieldFiniteMumfordMapSurjectiveStatement`,
namespace `Langlands.AbelianScheme`, with `open CategoryTheory AlgebraicGeometry` and
`open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules`. The file defines one
universe-polymorphic proposition, `FieldFiniteMumfordMapSurjectiveStatement.{u}`. It does not
prove it.

## Complete proposition

```lean
def FieldFiniteMumfordMapSurjectiveStatement : Prop :=
  ∀ (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (square : MumfordBundlePicardZeroStatement.{u})
    (K : Type u) [Field K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (hA : HasDualScheme A)
    (L : RigidifiedLineBundle (unitSection A)) (M : LineBundle A.X.left)
    (evaluation : tensorObj L.obj.carrier M.obj ≅ structureSheaf A.X.left),
    IsFinite (mumfordSchemeMap preservation square A L M evaluation hA).left →
      Function.Surjective (mumfordSchemeMap preservation square A L M evaluation hA).left
```

Imports: `Langlands.AlgebraicGeometry.Picard.MumfordMap` and
`Mathlib.AlgebraicGeometry.Morphisms.Finite`.

## Meaning of the binders

All names are the published Library and Mathlib ones, used unchanged.

- `preservation : pullbackTensorComparisonIsIsoStatement.{u}` and
  `square : MumfordBundlePicardZeroStatement.{u}` are the two published propositions that the
  Library's construction of the Mumford map takes as inputs (module
  `Langlands.AlgebraicGeometry.Picard.MumfordMap`). They are binders of the proposition, the
  same two binders as in `AlgClosedFieldMumfordDualEulerStatement`. `preservation` says the
  actual tensor/pullback comparison is an isomorphism for every scheme morphism in universe
  `u`; `square` says the constructed Mumford family has translation-invariant geometric
  fibres. The statement asserts nothing about whether either input proposition holds.
- `K` is any field in universe `u`, of any characteristic and not necessarily algebraically
  closed. `A : AbelianScheme (Spec (CommRingCat.of K))` is a published abelian scheme over
  `Spec K`, that is, an abelian variety over `K`.
- `hA : HasDualScheme A` asserts that a universal rigidified Picard-zero family exists;
  `D := dualScheme A hA` is the chosen dual, an object of `Over (Spec K)`.
- `L : RigidifiedLineBundle (unitSection A)` is a line bundle on `A` rigidified along the
  unit section, `M` is a line bundle on `A`, and `evaluation : L ⊗ M ≅ 𝒪_A` exhibits `M` as an
  inverse of `L`. No ampleness or other condition is imposed on `L`.
- `mumfordSchemeMap preservation square A L M evaluation hA : A.X ⟶ D` is the Library's
  morphism classifying the actual Mumford family `(m^*L ⊗ p₁^*M) ⊗ p₂^*M`. Over a field its
  fibre over a point `a` is the class of `t_a^*L ⊗ L⁻¹`, so it is the source's `φ_L`. Its
  `.left` is the underlying morphism of schemes `A.X.left ⟶ D.left`.

The hypothesis is Mathlib's `IsFinite` for this underlying morphism. The conclusion is
`Function.Surjective` for the map on underlying points of schemes, so every point of `D.left`,
closed or not, lies in the image.

## Original source and derived formulation

B. Edixhoven, G. van der Geer and B. Moonen, *Abelian Varieties*, preliminary draft (registered
source `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`). Proposition (7.21),
printed p.105 (PDF p.109), with Mumford's proof on printed p.106 (PDF p.110): for an abelian
variety `X` over an algebraically closed field `k`, an ample line bundle `L` and a line bundle
`M` with `φ_M = 0`, there is `x ∈ X(k)` with `M ≅ t_x^*L ⊗ L⁻¹`. Corollary (7.22) on p.106
identifies `Pic⁰_{X/k}` with the kernel of `φ`. Together they say that `φ_L : X → X^t` is
surjective on `k`-points.

The statement is derived content:

- The proof of (7.21) uses ampleness of `L` only to know that `K(L)`, the kernel of `φ_L`, is
  finite. Here finiteness of the Mumford map is assumed instead. It gives finiteness of
  `K(L)`, the fibre over the origin.
- The source works over an algebraically closed field and concludes for `k`-points. The
  statement allows any field `K` and concludes surjectivity on all scheme points. A proof
  applies the source argument after base change to an algebraic closure of the residue field
  of each point of `D`.
- The source's `X^t = Pic⁰_{X/k}` is replaced by the Library's chosen parameter scheme
  `dualScheme A hA`. It represents rigidified classes that are Picard-zero in the Library's
  sense: translation invariant on fibres over algebraically closed fields. This is the
  condition `φ_M = 0` of the source, which by (7.22) cuts out `Pic⁰`.

## Role

Prerequisite of task `6b1ab3e8-b3b0-4567-9251-7566e7a6dba3`, the exact proof of
`Langlands.AbelianScheme.AlgClosedFieldMumfordDualEulerStatement`. That target assumes only
that the Mumford map is finite and flat. The left side of its formula
`χ = (-1)^g · f.left.finrank y` does not depend on the point `y` of the dual, while the degree
`f.left.finrank y` is zero at points outside the image of `f`. Surjectivity is also used to
prove the geometry of the dual in `AlgClosedFieldFiniteMumfordDualGeometryStatement`.

The transitive imports contain neither `AlgClosedFieldMumfordDualEulerStatement` nor
`AlgClosedFieldAmpleMumfordEulerSquareStatement`, nor anything downstream of either.
