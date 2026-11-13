# Restriction of a compact induction to an open normal subgroup

Author: Worker 5104.

Supporting module for the proof of Renard VI.4.5, Corollary
(`Langlands.CuspidalSupport.rationalInertiaBlockIndecomposable`). It is built on
the published compact induction of `Langlands.Representation.Induction.OpenAdjunction`
(`compactInduced`, `CompactFunctions`, `eval`, `unitMap`, `cosetSum`,
`cosetSum_unitMap`, `cosetSum_apply`, `resIntertwining`, `compactFunctions_ext`).
From Mathlib it uses `Representation.IsIrreducible`, `Representation.asModule`,
`Representation.IntertwiningMap.equivLinearMapAsModule` and the theory of
semisimple modules (`isSemisimpleModule_of_isSemisimpleModule_submodule'`,
`IsSemisimpleModule.range`, `IsSemisimpleModule.of_injective`,
`IsSemisimpleModule.lifting_property`).

Everything is in the namespace `Langlands.Induction`. Throughout, `k` is a field,
`G` a topological group, `H` a normal subgroup of `G`, and, where stated,
`hH : IsOpen (H : Set G)`. As in the published conventions, `c-Ind_H^G σ`
(`compactInduced H σ`) consists of the functions `f : G → V` with
`f (h x) = σ h (f x)`, and `g` acts by right translation `(g f)(x) = f (x g)`.

## Provenance

These are internal lemmas with no single literature locator. The semisimplicity
of the restriction to an open normal subgroup is the standard argument: the
restriction of `c-Ind_H^G σ` to `H` is the sum of the `G/H`-conjugates of `σ`.
It is used to show that a compact induction from the norm kernel lies in the
inertia block, the first step of the proof of Renard VI.4.1 (David Renard,
*Représentations des groupes réductifs p-adiques*, printed pp.149–151 / PDF
pp.155–157), without any compactness hypothesis.

## Conjugation

- `normalConj H x : H →* H` is conjugation `h ↦ x h x⁻¹` on the normal subgroup
  `H`; `normalConj_apply_coe` records its value in `G` and
  `normalConj_surjective` shows it is surjective (with preimage `x⁻¹ h x`).
- `isIrreducible_comp_of_surjective σ f hf hσ`: if `σ` is an irreducible
  representation of `L` and `f : K →* L` is surjective, then `σ ∘ f` is
  irreducible. The subrepresentations of `σ` and of `σ ∘ f` are the same
  submodules (an order isomorphism), so the lattice of subrepresentations is
  simple for both.

## Semisimplicity

- `translatedUnitMap H hH σ hσ x`: for `x : G`, the `H`-intertwiner
  `v ↦ x⁻¹ · unit(v)` from the conjugate `σ ∘ normalConj H x` to the restriction
  `(c-Ind σ)|_H`, where `unit = unitMap H hH σ hσ` is the published unit of
  Frobenius reciprocity. Equivariance is the computation
  `unit(σ(x h x⁻¹) v) = (x h x⁻¹) · unit(v)`. `translatedUnitMap_apply` gives its
  value.
- `isSemisimpleModule_compactInduced_restrict H hH σ hσ hirr`: if `σ` is
  irreducible and smooth, then `(c-Ind_H^G σ)|_H` is a semisimple `k[H]`-module.
  The proof takes the family of submodules `p x = range (translatedUnitMap x)`,
  `x : G`. Each `p x` is semisimple, being the image of the irreducible
  representation `σ ∘ normalConj H x` (by the previous lemma). Their supremum is
  everything: by the published `cosetSum_unitMap`, every `f` equals the finite
  sum over cosets `H x` of `x⁻¹ · unit(f(x))`, and each term lies in `p x`.
  Mathlib's `isSemisimpleModule_of_isSemisimpleModule_submodule'` concludes.

## Nonzero restricted maps from subquotients

- `evalTranslate H σ τ j x`: for a representation `τ` of `G`, an
  `H`-intertwiner `j : σ → τ|_H` and `x : G`, the `H`-intertwiner
  `f ↦ τ(x⁻¹) j(f(x))` from `(c-Ind σ)|_H` to `τ|_H`. Equivariance uses the
  covariance `f(x h) = f((x h x⁻¹) x) = σ(x h x⁻¹) f(x)` and the equivariance of
  `j`. `evalTranslate_apply` gives its value.
- `exists_restricted_intertwiningMap_ne_zero_of_subquotient`: let `σ` be
  irreducible and smooth, `j : σ → τ|_H` an injective `H`-intertwiner, and let `D`
  be a subquotient of `c-Ind_H^G σ`, presented by an injective `G`-intertwiner
  `i : B → c-Ind σ` and a surjective `G`-intertwiner `q : B → D`. If `D` has a
  nonzero vector `d`, then some `H`-intertwiner `D|_H → τ|_H` is nonzero.

  Proof: `B|_H` embeds into the semisimple `(c-Ind σ)|_H` by `i`, so it is
  semisimple (`IsSemisimpleModule.of_injective`), and the surjection `q|_H` has
  an `H`-equivariant section `s` (`IsSemisimpleModule.lifting_property`). Then
  `s d ≠ 0` because `q (s d) = d`, so `i (s d)` is a nonzero function on `G`:
  it has a value `i (s d) (x) ≠ 0` at some `x`. The composite
  `evalTranslate x ∘ i ∘ s` sends `d` to `τ(x⁻¹) j(i (s d) (x))`, which is nonzero
  because `τ(x⁻¹)` is invertible and `j` is injective.

No admissibility, finiteness or compactness hypothesis is used anywhere.
