/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.Mathlib.Data.Set.Image
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.Outer

/-!
# Topological invariance of the small étale site

Let `f: X ⟶ Y` be a universal homeomorphism, i.e. integral, universally injective and
surjective. Then base change along `f` is an equivalence between the category of schemes
étale over `Y` and the category of schemes étale over `X`, and it matches the small étale
topologies on the two sides. This is [Stacks 04DZ].

The base change functor is `AlgebraicGeometry.Scheme.Hom.Etale`; it sends an étale
`Y`-scheme `V` to the top-left corner of the cartesian square

```
   f.Etale.obj V = V ×_Y X ──→ V
            │                  │
            ↓                  ↓
            X ────────f───────→ Y
```

so the statement is that `f.Etale: Y.Etale ⥤ X.Etale` is an equivalence of categories,
with `AlgebraicGeometry.Scheme.Hom.etaleEquivalence` the bundled form.

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.etaleEquivalence`: base change along a universal
  homeomorphism, as a bundled equivalence of categories `Y.Etale ≌ X.Etale`. This is the
  form in which the equivalence enters `CategoryTheory.Equivalence.sheafCongr`, hence the
  topos statements downstream.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.functorPushforward_mem_smallEtaleTopology_iff`: a sieve on an étale
  `Y`-scheme is a covering for the small étale topology of `Y` if and only if its base
  change along `f` is a covering for the small étale topology of `X`. Equivalently, a family
  of étale morphisms is jointly surjective if and only if its base change is.
- `AlgebraicGeometry.Scheme.Hom.isEquivalence_etale`: base change along
  a universal homeomorphism is an equivalence of the underlying categories of the small
  étale sites. See the implementation notes for the structure of the proof.
- `AlgebraicGeometry.Scheme.Hom.isDenseSubsite_etale`: the two statements above combined,
  in the form `CategoryTheory.Functor.IsDenseSubsite` consumed by
  `CategoryTheory.Equivalence.sheafCongr`.

## Implementation notes

The comparison of the topologies is proved here (filling the omission in [Stacks 03SI]): a
sieve is a covering for the small étale topology exactly when its arrows are jointly surjective
(`AlgebraicGeometry.Scheme.mem_smallEtaleTopology_iff`), and for every étale `V ⟶ Y` the
projection `V ×_Y X ⟶ V` is a base change of `f`, hence bijective on points; so ranges of
arrows correspond to ranges of their base changes under these bijections. This uses
nothing about `f.Etale` being an equivalence, nor integrality: it is stated for a morphism that
is merely universally injective and surjective.

The equivalence itself, `Hom.isEquivalence_etale`, is the mathematical content of [Stacks
04DZ]. It is proved in the files of the directory `EtaleTopologicalInvariance/`, following
the second proof of [Stacks 04DZ]:

* `FullyFaithful`: full faithfulness of base change, by descending an `X`-morphism through
  its graph, an open subscheme which corresponds to an open subscheme on the `Y`-side
  because the base change of `f` is a homeomorphism ([Stacks 04DY]).
* `Gluing`: being in the essential image is local on the source, by gluing descended
  opens along a locally directed diagram of open immersions.
* `PropertyC`: property (C) of [Stacks 04DW], reduced to the ring-theoretic statement
  `Algebra.Etale.exists_etale_algHom_comap_eq`, which is proved by trivialising the
  separable part of the residue field extension and applying the étale local structure of
  quasi-finite algebras.
* `EssSurj`: the affine case, by induction on a bound for the fibre degrees, using the
  section trick of [Stacks 04DZ] and descent along an étale cover (`Descent`) through the
  affine hull of a quasi-affine scheme (`Mathlib.RingTheory.Flat.DescentAlgebra`).
* `Outer`: reduction of the general case to the affine case with bounded fibre degrees,
  using the local structure of étale algebras.

The equivalence `Hom.isEquivalence_etale` and the dense-subsite statement
`Hom.isDenseSubsite_etale` are global instances.

## References

* [Stacks 04DZ], Étale Cohomology, Theorem 59.45.2.
* [Stacks 03SI]
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

section Bijective

variable [UniversallyInjective f] [Surjective f]

set_option backward.isDefEq.respectTransparency.types false in
/-- The image of the base change of `g : V ⟶ U` along `f` is the preimage of the image of
`g` under the projection `U ×_Y X ⟶ U`:

```
   V ×_Y X ──(f.Etale.map g).left──→ U ×_Y X
      │                                 │
      │ pullback.fst V.hom f            │ pullback.fst U.hom f
      ↓                                 ↓
      V ────────────g.left────────────→  U
```
-/
lemma range_etale_map_left {U V : Y.Etale} (g : V ⟶ U) :
    Set.range (f.Etale.map g).left = pullback.fst U.hom f ⁻¹' Set.range g.left := by
  have : UniversallyInjective (pullback.fst U.hom f) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  refine Set.range_eq_preimage_range_of_comm (pullback.fst V.hom f).surjective
    (pullback.fst U.hom f).injective (funext fun x ↦ ?_)
  change ((f.Etale.map g).left ≫ pullback.fst U.hom f) x = _
  rw [etale_map_left_comp_fst]
  rfl

/-- **Covering compatibility for universal homeomorphisms**: a sieve on an étale `Y`-scheme
`U` is a covering for the small étale topology of `Y` if and only if its base change along
`f` is a covering for the small étale topology of `X`. -/
@[stacks 04DZ]
lemma functorPushforward_mem_smallEtaleTopology_iff {U : Y.Etale} (S : Sieve U) :
    S.functorPushforward f.Etale ∈ X.smallEtaleTopology (f.Etale.obj U) ↔
      S ∈ Y.smallEtaleTopology U := by
  rw [mem_smallEtaleTopology_iff, mem_smallEtaleTopology_iff]
  constructor
  · intro h u
    obtain ⟨x, hx⟩ := (pullback.fst U.hom f).surjective u
    obtain ⟨W, k, ⟨V, g, l, hg, rfl⟩, hxk⟩ := h x
    refine ⟨V, g, hg, ?_⟩
    have hsub : Set.range (l ≫ f.Etale.map g).left ⊆ Set.range (f.Etale.map g).left := by
      change Set.range (l.left ≫ (f.Etale.map g).left) ⊆ _
      simp [Set.range_comp]
    rw [← hx]
    exact (range_etale_map_left f g).le (hsub hxk)
  · intro h x
    obtain ⟨V, g, hg, hx⟩ := h (pullback.fst U.hom f x)
    exact ⟨f.Etale.obj V, f.Etale.map g, Presieve.image_mem_functorPushforward _ _ hg,
      (range_etale_map_left f g).ge hx⟩

end Bijective

variable [IsUniversalHomeomorphism f]

/-- **Topological invariance of the small étale site**: base change along a universal
homeomorphism `f: X ⟶ Y` is an equivalence between the category of schemes étale over `Y`
and the category of schemes étale over `X`. -/
@[stacks 04DZ]
instance isEquivalence_etale : f.Etale.IsEquivalence where

/-- **Topological invariance of the small étale site**, [Stacks 04DZ]: for a universal
homeomorphism `f: X ⟶ Y`, the functor `V ↦ V ×_Y X` is an equivalence of categories
between schemes étale over `Y` and schemes étale over `X`. -/
@[stacks 04DZ]
noncomputable def etaleEquivalence : Y.Etale ≌ X.Etale :=
  f.Etale.asEquivalence

/-- Base change along a universal homeomorphism exhibits the small étale site of `Y` as a
dense subsite of the small étale site of `X`. -/
instance isDenseSubsite_etale :
    f.Etale.IsDenseSubsite Y.smallEtaleTopology X.smallEtaleTopology where
  functorPushforward_mem_iff := functorPushforward_mem_smallEtaleTopology_iff f _

end AlgebraicGeometry.Scheme.Hom
