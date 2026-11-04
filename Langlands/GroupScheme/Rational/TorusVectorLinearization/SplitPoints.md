# Points of a torus that splits over an extension field

Let `k ⊆ K` be fields. Let `T` be a group scheme over `k` and
`s : T_K ≅ splitTorus (Spec K) I` a splitting of its base change to `K`, with `I`
finite. Over every `K`-algebra `C`, this module describes the points of `T` itself
by families of units of `C`. The points are taken with coefficients in `C`, viewed
as a `k`-algebra through `K`. Everything is in namespace
`Langlands.GroupScheme.RelativeRoot`.

The algebra `C` carries compatible `k`- and `K`-algebra structures
(`IsScalarTower k K C`). No finiteness of `K` over `k` is assumed, matching the
published `IsTorus`, which allows an arbitrary splitting field.

## Definition

`splitPoint s τ` is the point of `T` over `C` whose unit coordinates in the
splitting `s` are `τ : I → Cˣ`. It is built in two steps.

1. The published `AutomorphicAction.torusPoint s τ` turns `τ` into a point of
   the base change `T_K` over `C`, regarded as a `K`-algebra. It takes the point of
   the split torus with unit coordinates `τ` and applies `s⁻¹`.
2. The published `Lie.affineBaseChangeEquiv k K T C` identifies points of `T_K`
   over `C` with points of `T` over `C`.

## Properties

- `splitPoint_one` and `splitPoint_mul`: `τ ↦ splitPoint s τ` is
  multiplicative and sends `1` to `1`. Both steps of the definition are group
  homomorphisms (`torusPoint_one`, `torusPoint_mul`).
- `splitPoint_surjective`: every point `t` of `T` over `C` is `splitPoint s τ`
  for some `τ`. Take the point `x` of `T_K` corresponding to `t` and let `τ` be
  the unit coordinates of `x ≫ s`. Since `s` is an isomorphism, `splitPoint s τ`
  is `t` again.
- `splitPoint_naturality`: for every `K`-algebra map `f : C →ₐ[K] D`, extending
  coefficients along `f` (as a `k`-algebra map) sends `splitPoint s τ` to
  `splitPoint s (Units.map f ∘ τ)`. This combines the published naturality of the
  base change comparison (`Lie.affineBaseChangeEquiv_naturality`) with that of
  `torusPoint` (`torusPoint_naturality`).

## Provenance

These lemmas are internal to the proof of
`TorusVectorActionLinearizationStatement`. They do not formalize a statement from
the literature. They describe the points of a torus through a splitting field,
which the formal proof uses to obtain a weight grading over `K` that is then
descended to `k`. Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, 2nd ed., argue
differently: the proofs of Proposition B.4.2 and Theorem B.4.3 (printed
pp.576–577, PDF pp.602–603) extend scalars to an algebraically or separably
closed field for some of their steps. The lemmas are assembled from the published
`torusPoint` and `affineBaseChangeEquiv`.
