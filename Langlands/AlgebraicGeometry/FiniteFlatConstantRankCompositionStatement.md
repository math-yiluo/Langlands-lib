# Constant native rank under finite flat composition

`Langlands.AlgebraicGeometry.FiniteFlatConstantRankCompositionStatement` is a
universe-polymorphic proposition about actual Mathlib schemes and morphisms.
For schemes `X`, `Y`, and `Z` in the same universe `u`, assume `Z` is locally
noetherian and `f : X ⟶ Y` and `q : Y ⟶ Z` are finite and flat. For any natural
numbers `r` and `s`, if `f.finrank y = r` for every `y : Y` and
`q.finrank z = s` for every `z : Z`, the proposition asserts

```text
(f ≫ q).finrank z = r * s
```

for every `z : Z`. Here `f ≫ q` is the actual composite `X ⟶ Z`.

The rank is Mathlib's native `AlgebraicGeometry.Scheme.Hom.finrank`. It is
defined by pulling back to an affine neighbourhood of the target point and
using the induced ring map's local module rank. For a finite flat algebra
`A → B`, `Scheme.Hom.finrank_SpecMap_algebraMap` identifies the rank of
`Spec B ⟶ Spec A` at a prime `p` with `Module.rankAtStalk B p`. This is the
rank of `B` localized over `A` at `p`, equivalently the dimension of
`κ(p) ⊗[A] B` over the residue field `κ(p)` in this finite flat setting.
Thus the constant-rank hypotheses concern the existing local module ranks.

The quantifiers include zero ranks and empty schemes. No integrality,
connectedness, affineness, nonemptiness, positivity, surjectivity, or chosen
basis is assumed. In particular, a zero constant rank yields zero composite
rank, and when `Z` is empty the conclusion is vacuous. When `Y` is empty,
the first constant-rank assumption is vacuous, while `q` has rank zero at
every point of `Z`.

## Source and derived provenance

The source is The Stacks Project Authors,
[Section 29.49, Finite locally free morphisms (tag 02K9)](https://stacks.math.columbia.edu/tag/02K9),
Definition 29.49.1 and Lemmas 29.49.2–29.49.3, in the registered HTML snapshot
retrieved on 2026-10-31. Source ID:
`stacks-numerical-intersections-finite-locally-free-rank-2026-10-31`.
The retained file is
`/home/taskhub/pilot/literature/The Stacks Project — Numerical intersections and finite locally free rank (2026-10-31 snapshots)/02K9.html`.

Definition 29.49.1 defines degree through the rank of the finite locally free
pushforward of the structure sheaf. Lemma 29.49.2 identifies finite flat maps
with finite locally free maps over a locally noetherian target. Since `q` is
finite and `Z` is locally noetherian, `Y` is also locally noetherian, so this
criterion applies to both `q` and `f`. This use of the noetherian hypothesis
supplies finite presentation; finite flat maps over arbitrary targets need
not be finite locally free. Lemma 29.49.3 states that composition preserves
finite locally free morphisms. It does not explicitly assert numerical rank
multiplication.

The numerical product in this proposition is an internal derived consequence
of those facts and the local module interpretation of native rank. After
affine localization, restriction of scalars along a finite locally free
algebra of constant rank `s` takes a finite locally free module of constant
rank `r` to one of rank `r * s`. To see the numerical calculation at `z`,
pass to its residue field `k = κ(z)`. The fibre algebras `k → B → C` have
`dim_k B = s`, and `C` is finite locally free of constant rank `r` over `B`.
Decomposing the finite-dimensional algebra `B` into its Artinian local
factors makes the corresponding parts of `C` free of rank `r`, giving
`dim_k C = r * dim_k B = r * s`. The zero algebra gives dimension zero as
well. Mathlib's native affine comparison and finite flat base-change rank
comparison identify these local dimensions with the three scheme ranks.
This explains the derived assertion without attributing the numerical
formula itself to Lemma 29.49.3.

This file defines the proposition for a separate proof successor. It contains
no proof of rank multiplication and asserts no multiplication-by-6,
polarization, torsion, or cohomology result.
