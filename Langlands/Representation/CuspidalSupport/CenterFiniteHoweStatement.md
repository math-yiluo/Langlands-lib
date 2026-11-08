# Finite type, admissibility and `ℨ(G)`-finiteness: statement

Author: Worker 6. Module `Langlands.Representation.CuspidalSupport.CenterFiniteHoweStatement`, namespace `Langlands.Aubert.General.RepresentedParabolic`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VI.10.8, Theorem and proof, printed p.217 / PDF p.223. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

## The source

A smooth representation `(π, V)` of `G` is called `ℨ(G)`-finite if its annihilator in `ℨ(G)` is an ideal of finite codimension. The theorem reads: for a smooth `(π, V)`, consider the properties (1) `π` is of finite type, (2) `π` is admissible, (3) `π` is `ℨ(G)`-finite. Then any two of them imply the third, and `π` then has finite length. The proof combines Howe's theorem VI.6.3 ((1) and (2) together are equivalent to finite length), Schur's lemma, and the results of VI.10.7.

## The Lean statement

`CenterFiniteHoweStatement` is a statement unit: nothing is proved. It quantifies over:

- a nonarchimedean local field `k : Type u`;
- a connected reductive group scheme `G` over `Spec k`, with `G(F)` locally compact and nonarchimedean in the canonical topology `RationalPointFamily.pointTopology`;
- a smooth representation `π : SmoothRep.{0, u, v} ℂ (rationalPoints G)`, with no further hypothesis.

The three properties are:

1. `FiniteType`: `Module.Finite (MonoidAlgebra ℂ (rationalPoints G)) π.representation.asModule`, finite generation over the group algebra. This is the notion of the published VI.1.3 and VI.7.5 statements.
2. `π.IsAdmissible`: the published admissibility of smooth representations.
3. `CenterFinite`: the `ℂ`-span, inside the linear endomorphisms of the carrier of `π`, of the operators `(z.app π)` for `z` in Mathlib's `CatCenter (SmoothRep.{0, u, v} ℂ (rationalPoints G))` is finite-dimensional. `CatCenter C` is `End (𝟭 C)`, Renard's `ℨ(G)`.

Property 3 is Renard's `ℨ(G)`-finiteness. The map `z ↦ z.app π` from `ℨ(G)` to `End_ℂ(V)` has kernel the annihilator of `π`. Its image is therefore isomorphic to `ℨ(G)/Ann(π)`, and it is finite-dimensional exactly when the annihilator has finite codimension. Taking the span is harmless, because the image of `ℂ`-scalar natural transformations already makes the image a subspace. These identifications are not formalized.

The conclusion is: if `(FiniteType ∧ π.IsAdmissible) ∨ (FiniteType ∧ CenterFinite) ∨ (π.IsAdmissible ∧ CenterFinite)`, then `FiniteType ∧ π.IsAdmissible ∧ CenterFinite ∧ π.HasFiniteLength`. That is, any two of the properties imply the third, and then the representation has finite length. `SmoothRep.HasFiniteLength` is the published finite composition length over the group algebra.

## Remarks

- The centre is taken in the category of smooth representations with carriers in the universe `v` of `π`. Renard's `ℨ(G)` does not depend on such a choice. The comparison between universes is not formalized.
- The proof (Howe's theorem, Schur's lemma, the VI.10.7 Theorem and Proposition) is not formalized here.
