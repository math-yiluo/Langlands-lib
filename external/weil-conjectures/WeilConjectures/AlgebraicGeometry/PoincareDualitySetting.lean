/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!

# The fixed geometric setting of the Poincaré duality chapter

Poincaré duality for `ℓ`-adic cohomology is stated for a scheme `X₀` over a finite field `k₀`
which is smooth of relative dimension `d`, separated of finite type and geometrically
connected, base changed to an algebraic closure `k` of `k₀`. This file packages that
geometric datum as a single structure, so that the statements of the chapter can quantify
over it.

## Main definitions

- `AlgebraicGeometry.PoincareDualitySetting`: the geometric datum `(X₀, a_{X₀})`.
- `AlgebraicGeometry.PoincareDualitySetting.geometricFiber`: the base change
  `X = X₀ ×_{k₀} k` to the algebraic closure.
- `AlgebraicGeometry.PoincareDualitySetting.structureMorphism`: the structure morphism
  `a_X : X ⟶ Spec k`.

## Implementation notes

Properness of `X₀` is deliberately *not* part of the datum: the duality statements are
formulated with compact supports and do not use it. It is imposed explicitly, as an
`[IsProper …]` instance hypothesis, exactly where `Ra_{X!} ≅ Ra_{X*}` is needed.

The blueprint (`prose-01-10`) imposes no admissibility on `a_X`. In Lean, `Ra_{X!}` and
`Ra_X^!` are only constructed for morphisms admitting a compactification, so
`AlgebraicGeometry.HasCompactification` is carried as an instance hypothesis by the statements
that use them rather than as a field of the datum. For `a_X` this hypothesis is redundant
mathematically: `a_X` is separated of finite type over the quasi-compact quasi-separated
`Spec k`, so Nagata's theorem (`AlgebraicGeometry.NagataCompactification`, which comes with an
instance) provides a compactification once those properties of `a_X` are available as
instances.

The blueprint node `prose-01-10` fixes, besides the geometry, a *coefficient* datum
`(ℓ, E, 𝒪_E, ϖ_E, Λ)` subject to `ℓ ≠ ring characteristic of k₀`. That half of the datum is
not recorded here: the coefficient category is a type parameter of the six operations, and
the constraint `ℓ ≠ p` is a hypothesis of the duality *theorems*, none of which is stated
yet. It is to be added together with them.

Likewise the Frobenius endomorphism of the geometric fibre is not constructed here; it is the
geometric Galois Frobenius `𝟙_{X₀} × Spec σ` of
`WeilConjectures.AlgebraicGeometry.GeometricFrobenius`, where `σ` is the geometric — not the
arithmetic — Frobenius of the algebraic closure.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (k₀ : Type u) [Field k₀] [Finite k₀]

/-- Blueprint `prose-01-10`: The fixed setting.

The geometric datum of the Poincaré duality chapter over the finite field `k₀`: a scheme `X₀`
over `k₀` which is smooth of relative dimension `d`, separated of finite type and
geometrically connected. The algebraic closure `k` of `k₀`, along which `X₀` is base changed,
is an argument of `PoincareDualitySetting.geometricFiber` rather than a field of the
datum. -/
structure PoincareDualitySetting (d : ℕ) where
  /-- The model `X₀` over the finite base field `k₀`. -/
  model : Scheme.{u}
  /-- The structure morphism `a_{X₀} : X₀ ⟶ Spec k₀`. -/
  modelStructureMorphism : model ⟶ Spec (CommRingCat.of k₀)
  [isSeparated : IsSeparated modelStructureMorphism]
  [quasiCompact : QuasiCompact modelStructureMorphism]
  [smoothOfRelativeDimension : SmoothOfRelativeDimension d modelStructureMorphism]
  [geometricallyConnected : GeometricallyConnected modelStructureMorphism]

attribute [instance] PoincareDualitySetting.isSeparated PoincareDualitySetting.quasiCompact
  PoincareDualitySetting.smoothOfRelativeDimension
  PoincareDualitySetting.geometricallyConnected

namespace PoincareDualitySetting

variable {k₀} {d : ℕ} (S : PoincareDualitySetting k₀ d)

/-- Smoothness of relative dimension `d` is smoothness. Together with the `quasiCompact`
field this is what makes `X₀` of finite type over `k₀`, so finite type is not a field. -/
instance smooth : Smooth S.modelStructureMorphism :=
  SmoothOfRelativeDimension.smooth d _

variable (k : Type u) [Field k] [IsAlgClosed k] [Algebra k₀ k] [Algebra.IsAlgebraic k₀ k]

/-- The geometric fibre `X = X₀ ×_{k₀} k` of the datum `S` over an algebraic closure `k`
of `k₀`.

That `k` is an algebraic closure of `k₀`, and not just an algebraically closed extension, is the
hypothesis `[Algebra.IsAlgebraic k₀ k]`: without it the `k`-points of `X` would not be the
`𝔽̄_q`-points of `X₀`. With it `k ≅ AlgebraicClosure k₀` over `k₀` (`IsAlgClosure`), so this is
the geometric fiber `AlgebraicGeometry.Scheme.Hom.geometricFiber` of `S.modelStructureMorphism`
used by the geometric Galois Frobenius of
`WeilConjectures.AlgebraicGeometry.GeometricFrobenius`, up to the choice of the algebraic
closure. -/
noncomputable def geometricFiber : Scheme.{u} :=
  pullback S.modelStructureMorphism (Spec.map (CommRingCat.ofHom (algebraMap k₀ k)))

/-- The structure morphism `a_X : X ⟶ Spec k` of the geometric fibre. -/
noncomputable def structureMorphism : S.geometricFiber k ⟶ Spec (CommRingCat.of k) :=
  pullback.snd S.modelStructureMorphism (Spec.map (CommRingCat.ofHom (algebraMap k₀ k)))

/-- The projection `p_X : X = X₀ ×_{k₀} k ⟶ X₀` from the geometric fibre to the model. -/
noncomputable def toModel : S.geometricFiber k ⟶ S.model :=
  pullback.fst S.modelStructureMorphism (Spec.map (CommRingCat.ofHom (algebraMap k₀ k)))

omit [Finite k₀] [IsAlgClosed k] [Algebra.IsAlgebraic k₀ k] in
/-- The geometric fibre is defined by the Cartesian square

```
            p_X
  X ────────────────▶ X₀
  │                   │
 a_X               a_{X₀}
  ▼                   ▼
Spec k ───────────▶ Spec k₀
        Spec (k₀ → k)
```
-/
lemma isPullback_geometricFiber :
    IsPullback (S.toModel k) (S.structureMorphism k) S.modelStructureMorphism
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ k))) :=
  IsPullback.of_hasPullback _ _

end PoincareDualitySetting

end AlgebraicGeometry
