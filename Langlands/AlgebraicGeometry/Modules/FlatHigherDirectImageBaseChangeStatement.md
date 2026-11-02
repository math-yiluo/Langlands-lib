# Flat base change for higher direct images

Authors: Worker 1159 and Worker 943. The formulation was supplied by Worker 943
in the task; Worker 1159 checked the source and prepared this pair.

`Langlands.AlgebraicGeometry.Modules.FlatHigherDirectImageBaseChangeStatement.{u}`
is a proposition in an arbitrary universe `u`. It states that, for every
cartesian square of schemes

```text
X' --g'--> X
 |         |
 f'        f
 |         |
 v         v
Y' ---g--> Y,
```

if `f` is quasi-compact and separated and `g` is flat, then for every
quasi-coherent `𝒪_X`-module `M` and every `n : ℕ` there exists an isomorphism
of `𝒪_{Y'}`-modules

```text
g^* Rⁿ f_* M ≅ Rⁿ f'_* (g'^* M).
```

The schemes and arrows are universally quantified in the order
`X, Y, X', Y', f, g, f', g'`, followed by the hypotheses
`IsPullback g' f' f g`, `QuasiCompact f`, `IsSeparated f`, and `Flat g`,
then `M`, `M.IsQuasicoherent`, and `n`. Any square satisfying Mathlib's
`IsPullback` is allowed; no chosen fibre product is required.

The Lean expressions use Mathlib's actual `Scheme.Modules`,
`Scheme.Modules.pullback`, and `SheafOfModules.IsQuasicoherent`. The Library's
`DerivedSections.higherDirectImage f n` is
`(Scheme.Modules.pushforward f).rightDerived n` on all sheaves of modules.
Both sides of the asserted isomorphism therefore lie in `Y'.Modules`.
`Nonempty` asserts existence of an isomorphism and specifies no particular
base change map or naturality data.

This file defines the proposition only. It supplies no proof.

## Source and correspondence

The source is The Stacks Project Authors, *The Stacks Project*, Cohomology of
Schemes, Lemma 30.5.2, tag 02KH, “Flat base change,” part (1):
[original lemma and comments](https://stacks.math.columbia.edu/tag/02KH).
Registered literature ID:
`stacks-flat-base-change-projection-formula-2026-11-02`; retained file:
`tag-02KH-lemma-30.5.2-flat-base-change.html` in the registered publication
folder; folder SHA-256:
`80cf9b0aa84270eb3e84d8a9be983aa9e38e16813713c407f723aeb49d49c8bd`.

The source's base schemes `S` and `S'` are Lean's `Y` and `Y'`, its
coefficient sheaf `𝓕` is `M`, its
`𝓕' = (g')^*𝓕` is `(Scheme.Modules.pullback g').obj M`, and its
nonnegative degree `i` is `n : ℕ`. The source assumes `f` quasi-compact and
quasi-separated. This Lean statement assumes `f` quasi-compact and
separated, a narrower hypothesis because separated morphisms are
quasi-separated. The source identifies the canonical base change map as an
isomorphism; this proposition only asserts that the two modules are
isomorphic, a weaker conclusion. Part (2), the affine-base tensor-product
formula for cohomology, is not stated here.

Worker 1159 read the retained lemma and all eight comments. The comments
correct typos and redundant proof wording, and comments 5458 and 5676
discuss the flatness of `g'` needed to apply Cohomology, Lemma 20.17.1.
The response explains that `g'` is flat as the base change of the flat
morphism `g`; the proof now states this. None of the comments changes the
statement or requires another hypothesis.

The only imports are Mathlib's flat and separated morphism modules and the
Library's `Langlands.AlgebraicGeometry.Modules.DerivedSections`. No
abelian-scheme statement or proof is a dependency.
