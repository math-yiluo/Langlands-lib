# The contragredient as the dual Hecke module (Renard III.1.6): statement

Module `Langlands.Representation.Hecke.ContragredientDualModuleStatement`. Namespace
`Langlands.Hecke`. Universe parameters `u` (the group) and `v` (the representation space).
The module contains one **statement**, the `Prop`-valued definition
`ContragredientHeckeDualStatement`. It proves nothing.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`. III.1.6 says that, under the III.1.4 equivalence, the
smooth contragredient corresponds to the dual module of I.4.1. The Library has both sides: the
smooth contragredient `smoothContragredient`, and the I.4.1 dual `NonUnitalModuleDual.dualObject`
([NonUnitalModuleDualFunctor](../../Algebra/NonUnitalModuleDualFunctor.md)) of the Hecke
module `heckeNondegenerateModule`. No published statement compares them. The published
`integratedAction_smoothDualPairing` ([SmoothTranspose](SmoothTranspose.md)) gives the
pairing identity only for a measure invariant under inversion, that is for unimodular `G`.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read III.1.6, printed p.61 / PDF p.67:

> Dans la section I.4.1, nous avons construit un foncteur de dualité de `M(H(G))` dans
> `M(H(G))^d`. Comme l'algèbre `H(G)` est munie de l'anti-involution `T ↦ Ť` induite par
> `g ↦ g⁻¹`, on peut identifier modules à droite et à gauche, et donc voir le foncteur de
> dualité comme un endofoncteur de `M(H(G))`. Il est clair que par l'équivalence de
> catégories du théorème III.1.4, la représentation contragrédiente `(π̃, Ṽ)` de `(π, V)`
> correspond au `H(G)`-module non dégénéré `Ṽ` défini dans la section I.4.1.
>
> Lemme. Soit `T ∈ ℰ′(G)`. Pour tout `λ ∈ Ṽ`, pour tout `v ∈ V`, on a :
> `(π̃(Ť) · λ)(v) = λ(π(T) · v)`.

## Published objects used

- `heckeNondegenerateModule μ A`: the nondegenerate `H(G)`-module of the smooth representation
  `A`, through `heckeAction` (III.1.4; [NondegenerateModuleFunctor](NondegenerateModuleFunctor.md)).
- `NonUnitalModuleDual.dualObject hA M`: the I.4.1 dual, the nondegenerate part of
  `Hom_ℂ(M, ℂ)` as a right module, with `(λ · a)(m) = λ(a · m)`; elements `φ` have underlying
  functionals `φ.val`.
- `Homomorphism.isIdempotented μ`: `H(G)` is a ring with idempotents
  ([HomomorphismLeft](HomomorphismLeft.md)).
- `haarInversion μ`: the anti-involution `T ↦ Ť` of `H(G)` on Haar densities,
  `Ť(g) = Δ(g) T(g⁻¹)` with `Δ = δ_G⁻¹` Mathlib's modular character
  ([HaarInversion](HaarInversion.md)). It is the inversion of distributions transported to
  densities.
- `SmoothDual`, `smoothContragredient`, `smoothDualPairing`, `isSmooth_smoothContragredient`.

## The statement

**`ContragredientHeckeDualStatement`.** Let `G` be a t.d. group (Hausdorff, locally compact,
nonarchimedean) with a left Haar measure `μ` and `A` a smooth complex representation. Let `D`
be the I.4.1 dual of the Hecke module of `A`. Then there is an additive equivalence
`e : Ṽ ≃ D` such that

1. `e(ℓ)(v) = ℓ(v)` for all `ℓ ∈ Ṽ` and `v ∈ V`;
2. `e(π̃(T) ℓ) = e(ℓ) · Ť` for all `T ∈ H(G)`, where `π̃(T)` is the Hecke action on the
   contragredient and `Ť = haarInversion μ T`.

## Formalization choices

- **Identifying right and left modules.** Renard turns the right module `Ṽ` into a left module
  through `T ↦ Ť`. The statement keeps the published right module and writes the
  identification as the equation `e(π̃(T) ℓ) = e(ℓ) · Ť`. This says that `e` is an isomorphism
  from the Hecke module of `π̃` to the left module obtained from `D` through `T ↦ Ť`.
- **The anti-involution on densities.** On Haar densities the inversion of distributions is
  the weighted `haarInversion`, not `f ↦ (g ↦ f(g⁻¹))`; the two agree when `G` is unimodular.
  With the weight the statement holds for every t.d. group.
- **Additive equivalence.** `e` is asserted additive. The evaluation formula 1 determines it,
  and makes it complex-linear.
- **The Lemma** for compactly supported distributions `T ∈ ℰ′(G)` is not restated: the Library
  has no action of `ℰ′(G)` on smooth representations. Its Hecke-algebra case is clause 2
  evaluated at `v`.

## Why the statement is true

For `ℓ ∈ Ṽ` the functional `v ↦ ℓ(v)` is fixed on the right by `e_K`, for a compact open `K`
fixing `ℓ`, because `ℓ(e_K · v) = ℓ(v)`. So it lies in the nondegenerate part `D`. Conversely,
if `φ · e = φ` for an idempotent `e` of `H(G)`, choose a compact open `K` with `e = e e_K`.
For `k ∈ K`, `φ(π(k) v) = φ(e e_K π(k) v) = φ(e e_K v) = φ(v)`, so `φ` is smooth. This gives
the bijection `e`. For clause 2,
`(π̃(T) ℓ)(v) = ∫ T(g) ℓ(π(g⁻¹) v) dμ(g) = ℓ(∫ T(g⁻¹) Δ(g) π(g) v dμ(g)) = ℓ(π(Ť) v)`,
by the inversion formula for a left Haar measure, `∫ F(g⁻¹) dμ(g) = ∫ F(g) Δ(g) dμ(g)`. The
right-hand side is `(e(ℓ) · Ť)(v)`.

## Remaining obligations

The proof is a separate obligation.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.Hecke.HomomorphismLeft` | `Homomorphism.isIdempotented`; through its imports `heckeNondegenerateModule`, `heckeAction`, `HeckeAlgebra`, `SmoothRep` |
| `Langlands.Representation.Hecke.HaarInversion` | `haarInversion` |
| `Langlands.Algebra.NonUnitalModuleDualFunctor` | `NonUnitalModuleDual.dualObject` |
| `Langlands.Representation.Smooth.Contragredient.LawsProof` | `isSmooth_smoothContragredient`; through its imports `SmoothDual`, `smoothContragredient`, `smoothDualPairing` |
