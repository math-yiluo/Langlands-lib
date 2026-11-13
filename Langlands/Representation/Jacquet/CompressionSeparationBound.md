# Renard VI.9.1: the bound `b ≤ c(G, K)` from separation by irreducibles

Author: Worker 167. Module `Langlands.Representation.Jacquet.CompressionSeparationBound`,
namespace `Langlands.Jacquet`.

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French edition
dated 9 July 2026, VI.9.1, last sentence of the Proposition: "la constante `b` peut être
choisie plus petite ou égale que la constante `c(G, K)` du théorème d'admissibilité
uniforme VI.2.3" (printed p.197 / PDF p.203). Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

Renard obtains the bound through the proof of the Proposition (VI.9.2–VI.9.3). The route
here is different and is ours: the bound is reduced to the vanishing on irreducible
representations of one natural endomorphism of `K`-fixed vectors, and to a separation
property of irreducible representations, proved in
`Langlands.Representation.Jacquet.FixedVectorIrreducibleSeparation`.

## Declarations

* `FixedVectorsSeparatedByIrreducibles K : Prop`, for a subgroup `K` of a topological
  group `G`. It says: for every family `T A` of linear endomorphisms of the `K`-fixed
  vectors of all smooth complex representations `A : SmoothRep.{0, uG, uV} ℂ G`, if `T` is
  natural (for every morphism `f : A ⟶ B`, `fixedVectorsMap f K ∘ T A = T B ∘
  fixedVectorsMap f K`) and `T A = 0` for every irreducible `A`, then `T A = 0` for every
  `A`. This is an internal definition, not a statement of the source.
* `pow_apply_eq_zero_of_finrank_le`: on a finite-dimensional space of dimension at most
  `c`, `t^c` kills every vector killed by some power of `t` (Mathlib's
  `Module.End.ker_pow_eq_ker_pow_finrank_of_le` and `ker_pow_le_ker_pow_finrank`).
* `fixedVectorsMap_mem_powerKernelSup`: an intertwiner maps the kernel supremum of the
  compression of `g` into the kernel supremum, by the Library naturality
  `compressedAction_pow_natural`.
* `fixedVectorsMap_projection`: when both compressions split, the projection onto the
  kernel supremum along the stable image commutes with intertwiners. Proof: decompose `v`
  as `p + (v - p)`; `f p` lies in the kernel supremum (previous lemma) and `f (v - p)` in
  the stable image (Library `fixedVectorsMap_mem_stableImage`).
* `stabilization_bound_of_separation`: for a compact open `K` and `g : G`, assume
  `FixedVectorsSeparatedByIrreducibles K`, that the compression of `g` splits for every
  smooth representation on a carrier in `Type uV`, and that `c` bounds the rank of the
  `K`-fixed vectors of every irreducible `A : SmoothRep.{0, uG, uV} ℂ G`. Then for every
  smooth `ρ` on such a carrier and every `s ≥ c`, the range of `A_g^s` is the stable image
  and its kernel the kernel supremum.

## Implemented proof of `stabilization_bound_of_separation`

Define `T A = A_g^c ∘ p_A`, where `p_A` is the projection of the `K`-fixed vectors onto the
kernel supremum along the stable image. It is natural by `compressedAction_pow_natural`
and `fixedVectorsMap_projection`. On an irreducible `A` the `K`-fixed space has dimension
at most `c`, hence `A_g^c` kills the kernel supremum (`pow_apply_eq_zero_of_finrank_le`)
and `T A = 0`. Separation gives `T = 0` on `SmoothRep.of ρ hρ`; thus `A_g^c` kills the
kernel supremum of `ρ`, and `stabilization_of_pow_kill` (module
`Langlands.Representation.Jacquet.IwahoriContractionRemarks`) concludes.

No admissibility or finiteness assumption on `ρ` is made; the splitting hypothesis is the
complementarity part of the Proposition of VI.9.1, assumed here for all representations.
