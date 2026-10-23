# Compact coefficients and compact averaged orbits

Author: Worker 246. This file defines one proposition,
`Langlands.CompactCoefficientAveragedOrbitStatement.{uG, uV}`. It proves nothing
and assumes no theorem as data. The equivalence is not proved here.

## The proposition

Let `G : Type uG` be a group with a topology. It is a topological group
(`IsTopologicalGroup`) and is Hausdorff (`T2Space`), locally compact
(`LocallyCompactSpace`) and totally disconnected (`TotallyDisconnectedSpace`).
Let `V : Type uV` be a complex vector space (`AddCommGroup`, `Module ℂ`) with
no topology. Let `ρ : Representation ℂ G V` be a representation and
`hρ : IsSmooth ρ` a proof that it is smooth. The proposition states that

```
HasCompactSmoothDualCoefficients ρ ↔
  ∀ (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (v : V),
    HasCompactSupport (fun g : G => Compact.averageMap ρ hρ K hK (ρ g v))
```

In words, the following are equivalent.

1. For every `v : V` and every `ℓ : Module.Dual ℂ V` that is a smooth vector
   of the dual representation, the coefficient `g ↦ ℓ (ρ g v)` has compact
   support.
2. For every open subgroup `K` whose underlying set is compact and every
   `v : V`, the averaged orbit `g ↦ e_K (ρ g v)` has compact support. Here
   `e_K = Compact.averageMap ρ hρ K hK`.

`G`, its instances, `V`, its instances, `ρ` and `hρ` are all quantified inside
the proposition. There are no other hypotheses.

## Terms used

All terms are published Library or Mathlib definitions; nothing is redefined.

- `IsSmooth ρ` (`Smooth/Definitions`): every vector is fixed by some open
  subgroup. This is the source's "algebraic" representation (2.1(a)), not a
  finite-dimensional one.
- `HasCompactSmoothDualCoefficients ρ` (`CompactCoefficient/Classes`): for all
  `v : V` and `ℓ : Module.Dual ℂ V` with `IsSmoothVector ρ.dual ℓ`,
  `HasCompactSupport (matrixCoefficient ρ ℓ v)`. Here
  `matrixCoefficient ρ ℓ v = fun g => ℓ (ρ g v)`, the dual is the full
  algebraic dual, and `(ρ.dual g ℓ) w = ℓ (ρ g⁻¹ w)` is Mathlib's dual action.
- `Compact.averageMap ρ hρ K hK` (`Compact/Definitions`): the linear map
  `w ↦ |K w|⁻¹ ∑_{u ∈ K w} u`, the mean of the finite `K`-orbit of `w`. It
  needs the smoothness proof `hρ` and the compactness proof `hK` to make every
  `K`-orbit finite.
- `HasCompactSupport f` (Mathlib): the closure of `{g | f g ≠ 0}` is compact.
  For the second condition `f` takes values in `V`, whose zero is used.

## Original source

I. N. Bernshtein and A. V. Zelevinskii, *Representations of the group GL(n,F)
where F is a non-Archimedean local field*, Russian Math. Surveys 31:3 (1976),
1–68, Lemma–Definition 2.40, printed and PDF page 26. Registered source
`bernstein-zelevinsky-1976-representations-gln`, SHA-256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`, file
`/home/taskhub/central-library/Bernstein-Zelevinsky--Representations of the group GL(n,F) where F is a non-archimedean local field (survey)--1976.pdf`.
Worker 246 read §§2.39–2.40 (p. 26) in this file. Worker 246 also read the
conventions used there: §1.1 (p. 6, `l`-spaces and `l`-groups), §1.7 (p. 7,
locally constant functions), §§1.13–1.14 (pp. 8–9, supports and "finite"
cross-sections), §§2.1–2.4 (p. 15, algebraic representations, `π(ε_N)`) and
§2.13 (p. 19, the contragredient).

For `(π, G, E)` in `Alg G`, 2.39 defines the matrix element
`φ_{ξ̃,ξ}(g) = ⟨ξ̃, π(g⁻¹) ξ⟩` for `ξ ∈ E` and `ξ̃` in the contragredient `Ẽ`.
2.40 says the following conditions are equivalent:

- (a) every `φ_{ξ̃,ξ}` is a finite function;
- (b) for each `ξ ∈ E` and each open compact subgroup `N ⊂ G`, the set
  `K_{ξ,N} = {g ∈ G | π(ε_N) π(g⁻¹) ξ ≠ 0}` is compact.

Representations satisfying them are called *finite*. The proposition above
states exactly this equivalence: condition 1 is (a) and condition 2 is (b).
The definition of "finite representation" and the remark on subquotients in
2.40 are not part of this proposition. Corollary 2.41 is not stated here.

## Correspondence of conventions

- **Group.** The source's `G` is an `l`-group: a topological group in which the
  open compact subgroups form a neighbourhood basis of `e`. The source notes
  that this is the same as being an `l`-space, that is, Hausdorff, locally
  compact and zero-dimensional. The Lean hypotheses are the Mathlib form of
  this: a Hausdorff, locally compact, totally disconnected topological group.
  For locally compact Hausdorff spaces total disconnectedness is equivalent to
  zero-dimensionality.
- **Representation.** "Algebraic" in the source means every stabilizer is open.
  This is `IsSmooth ρ`. Vector spaces carry no topology in the source or here.
  No finite dimension is assumed. The source's word "finite" refers to compact
  support and does not mean finite-dimensional.
- **Contragredient.** `Ẽ` is the algebraic part (smooth vectors) of the full
  dual `E*` with `(π*(g) ξ*)(ξ) = ξ*(π(g⁻¹) ξ)` (2.13). The Lean condition
  quantifies over `ℓ : Module.Dual ℂ V` with `IsSmoothVector ρ.dual ℓ`, which
  is the same set with the same action.
- **Averaging.** `π(ε_N)` is integration of `n ↦ π(n) ξ` against the normalized
  Haar measure of the compact subgroup `N` (2.3–2.4). On a smooth vector the
  stabilizer in `N` is open, hence of finite index. Haar measure gives each of
  its cosets the same mass. So `π(ε_N) ξ` is the uniform mean over the finite
  orbit `N ξ`, which is `Compact.averageMap`. This identification explains why
  the Library's Haar-free average represents the source's operator; it is not
  a Lean theorem of this file.
- **Inverse elements.** The source uses `π(g⁻¹)` in both conditions. The Lean
  statement uses `ρ g`. The source's set `K_{ξ,N}` is the image under
  `g ↦ g⁻¹` of `{g | e_N (ρ g ξ) ≠ 0}`. The source's matrix element is the
  Lean coefficient composed with `g ↦ g⁻¹`. Inversion is a homeomorphism of a
  topological group, so it preserves compactness.
- **Support.** §1.13 defines the support of a cross-section as its nonzero
  locus, which is closed, and calls a cross-section finite when its support is
  compact. The first example of §1.14 identifies the cross-sections of the
  sheaf attached to `S(X)` with the locally constant functions `C^∞(X)`. So a
  finite function is a locally constant function with compact nonzero locus,
  and (b) also asks that a nonzero locus be compact. Mathlib's
  `HasCompactSupport` asks that the closure of the nonzero locus be compact.
  Both functions are locally constant. If an open subgroup `U` fixes `v`, then
  `f (g u) = f g` for all `u ∈ U`, so `f` is constant on the open set `g U`.
  This holds for `f g = ℓ (ρ g v)` and for `f g = e_K (ρ g v)`. Hence the
  nonzero locus is open and closed, and it equals its closure. So the two
  support formulations agree.

## Scope

No admissibility, finite dimension, irreducibility, finite generation,
unimodularity, Haar measure, countability at infinity or theorem-valued input
is assumed. The source states 2.40 for every algebraic representation of an
`l`-group, without such hypotheses. Smoothness is the hypothesis `hρ`; it is
also needed to form `Compact.averageMap`. The compact open subgroups in
condition 2 are given as an `OpenSubgroup` together with a compactness proof,
the convention of `Compact.averageMap`.

## Intended proof route

This is not a proof. It records the source's argument for a later proof task.

- (2) ⇒ (1), the source's (b) ⇒ (a), via 2.14. Let `ℓ` be fixed by an open
  subgroup `U`. In an `l`-group `U` contains a compact open subgroup `K`.
  The published theorem
  `Langlands.Hecke.TestFunction.commonCompactOpenBiInvariance`, applied to an
  empty set of test functions, supplies one under the present hypotheses. Then
  `ℓ ∘ e_K = ℓ`, so `ℓ (ρ g v) = ℓ (e_K (ρ g v))`. The coefficient's support
  lies in the averaged orbit's support, which is compact.
- (1) ⇒ (2), the source's (a) ⇒ (b). Fix `v` and `K` and let `E_v` be the span
  of the averaged translates `e_K (ρ g v)`. Suppose `E_v` were
  infinite-dimensional. Choose `g_1, g_2, …` with `e_K (ρ g_i v)` linearly
  independent, and a functional on `E_v` taking the unbounded prescribed value
  `i` at `e_K (ρ g_i v)`. Extend it to `V` and compose with the averaging
  projector `e_K`. The result `ℓ` is `K`-invariant for the dual action, hence a
  smooth dual vector, and `ℓ (ρ g_i v) = i`. Its coefficient is locally
  constant with compact support, so it takes only finitely many values. This
  is a contradiction. So `E_v` is finite-dimensional. Finitely many
  functionals `ℓ_1, …, ℓ_k` on `E_v` separate its points. Extended and
  composed with `e_K` they are smooth dual vectors. The support of
  `g ↦ e_K (ρ g v)` lies in the union of the compact supports of the
  coefficients `g ↦ ℓ_j (ρ g v)`, so it is compact.

## Universes

The group universe `uG` and the carrier universe `uV` are independent universe
parameters of the definition. A development check printed the definition with
level parameters `uG, uV`. It also unfolded the proposition at universes `2` and
`5` with `Iff.rfl` against an explicit restatement in terms of
`IsCompact (closure (Function.support …))`. That check is a private draft, not
part of this unit.

## Dependencies

Project imports:

- `Langlands.Representation.CompactCoefficient.Classes` supplies
  `HasCompactSmoothDualCoefficients`. Through its imports it also supplies
  `matrixCoefficient`, `IsSmooth` and `IsSmoothVector`.
- `Langlands.Representation.Compact.Definitions` supplies
  `Compact.averageMap`.

Mathlib import: `Mathlib.Topology.Algebra.Support` for `HasCompactSupport`. No
existing published Lean/Markdown pair is modified. Lean service environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`).
