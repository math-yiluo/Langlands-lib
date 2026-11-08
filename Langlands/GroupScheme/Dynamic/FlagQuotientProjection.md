# Flatness of a quotient map with local sections near rational points

Authors: Worker 254, Worker 266.

This module proves three results in the namespace
`Langlands.GroupScheme.Dynamic`. It imports the Library module
`Langlands.GroupScheme.QuotientCell` and the Mathlib modules
`AlgebraicGeometry.AlgClosed.Basic`, `AlgebraicGeometry.Morphisms.Flat` and
`AlgebraicGeometry.Morphisms.QuasiCompact`.

## Main result

- `flat_surjective_quasiCompact_of_localSections`: let `Ω` be an
  algebraically closed field. Let `iP : P ⟶ H` be a homomorphism of group
  schemes over `Spec Ω` whose underlying scheme map `iP.hom.hom` is a
  monomorphism, and assume that the structure morphism `P.X.hom` of `P` is
  flat, surjective and quasi-compact. Let `Q₀` be a scheme over `Spec Ω` that
  is locally of finite type and quasi-compact over `Spec Ω`, and let
  `π₀ : H.X ⟶ Q₀` be a morphism over `Spec Ω`. Assume:
  - (`hf`) for every test scheme `T` over `Spec Ω` and points
    `g, h : T ⟶ H.X`, `g ≫ π₀ = h ≫ π₀` holds if and only if `g⁻¹ * h` lies
    in the image subgroup functor `SubgroupFunctor.range iP` at `T`;
  - (`hsec`) for every `Ω`-point `p : RingPoint Ω Q₀ Ω` there are an open
    `U` of `Q₀` containing the image of `p` and a section
    `s : openOver Ω Q₀ U ⟶ H.X` of `π₀` over `U`, that is,
    `s ≫ π₀ = openOverι Ω Q₀ U`.

  Then the underlying scheme morphism `π₀.left` is flat, surjective and
  quasi-compact.

## Auxiliary results

- `of_isPullback_of_iSup_eq_top`: let `Pr` be a morphism property of schemes
  that is Zariski-local at the target, `f : X ⟶ Y` a morphism and
  `U : κ → Y.Opens` a family of opens with `⨆ U = ⊤`. If, for every `i`,
  some pullback `b : Z ⟶ U i` of `f` along `(U i).ι` satisfies `Pr`, then
  `f` satisfies `Pr`.
- `exists_ringPoint_specializes`: for a scheme `Q₀` over `Spec Ω` that is
  locally of finite type and quasi-compact over `Spec Ω`, with `Ω`
  algebraically closed, every point `y` of `Q₀` specializes to a point `c`
  in the image of some `Ω`-point `p : RingPoint Ω Q₀ Ω`.

## Proof

`of_isPullback_of_iSup_eq_top`: by
`IsZariskiLocalAtTarget.of_iSup_eq_top` it suffices that `Pr (f ∣_ U i)` for
every `i`. Both `f ∣_ U i` (`isPullback_morphismRestrict`) and `b` are
pullbacks of `f` along `(U i).ι`. Then `IsPullback.isoIsPullback_inv_snd`
writes `f ∣_ U i` as an isomorphism followed by `b`, and `Pr` respects
isomorphisms.

`exists_ringPoint_specializes`: `Q₀` is a compact space, because `Q₀.hom` is
quasi-compact and `Spec Ω` is compact. So the nonempty closed set
`closure {y}` contains a closed point `c`
(`IsClosed.exists_closed_singleton`). Mathlib's `pointOfClosedPoint Q₀.hom c`
is a morphism `Spec Ω ⟶ Q₀` that sends the closed point of `Spec Ω` to `c`.
Since its composite with `Q₀.hom` is the identity of `Spec Ω`
(`pointOfClosedPoint_comp`), it is an `Ω`-point of `Q₀`. Finally `y ⤳ c`
because `c ∈ closure {y}`.

Main result: for every point `y` of `Q₀`, `exists_ringPoint_specializes`
gives an `Ω`-point `p` through a specialization `c` of `y`. `hsec` gives an
open `U y` containing `c` with a section `s y`. Since an open set containing
`c` contains every generization of `c`, `y ∈ U y`. So the opens `U y` cover
`Q₀`. For each `y`, the Library lemma `QuotientCell.multiplication_isPullback`
applied to `iP`, `s y`, `π₀` and `hf`, sent to schemes by `Over.forget`, gives
a pullback square

```
openOver Ω Q₀ (U y) ⊗ P.X ──multiplication──▶ H.X
          │ fst                                │ π₀
          ▼                                    ▼
   openOver Ω Q₀ (U y) ──────(s y ≫ π₀)──────▶ Q₀
```

Rewriting with `s y ≫ π₀ = openOverι Ω Q₀ (U y)` turns the bottom map into
`(U y).ι`. The left map is `pullback.fst` of `P.X.hom` along the structure
morphism of `openOver Ω Q₀ (U y)` (`Over.fst_left`). It therefore inherits
every property of `P.X.hom` that is stable under base change
(`MorphismProperty.pullback_fst`). Flatness, surjectivity and
quasi-compactness are each stable under base change and Zariski-local at the
target. `of_isPullback_of_iSup_eq_top` therefore gives each of them for
`π₀.left`.

The declarations that need the instances `IsZariskiLocalAtTarget @Flat` and
`IsZariskiLocalAtTarget @QuasiCompact` use
`set_option backward.isDefEq.respectTransparency.types false`, as Mathlib's
`Morphisms/Flat.lean` does. Without it, instance synthesis does not find
these instances.

## Provenance

This is an internal lemma for the formalization of CGP Proposition C.1.6
(Conrad, Gabber and Prasad, *Pseudo-reductive groups*, 2nd ed., printed
p.586). Worker 266 requested it with this exact signature. The Library's
dynamic flag-quotient existence statement provides a quotient `Q₀` with exact
fibres and local sections near rational points. The C.1.6 argument then uses
that the quotient map `G ⟶ G/P` is flat, surjective and quasi-compact. In
classical terms, a quotient map with local sections is Zariski-locally a
product `U × P ⟶ U`, which is the route formalized here.
