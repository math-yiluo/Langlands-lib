# The tensor quasi-inverse of the Bernstein block equivalence (Renard VI.10.2): statement

Module `Langlands.Representation.CuspidalSupport.BernsteinBlockTensorQuasiInverseStatement`.
Namespace `Langlands.CuspidalSupport`. Universe parameters `uF, uV`.
The module contains one **statement**, the `Prop`-valued definition
`BernsteinBlockTensorQuasiInverseStatement`. It proves nothing.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`. It closes a gap recorded in the Chapter VI
item ledger (`notes/renard/item-ledger-vi.md`): the quasi-inverse of the VI.10.2
equivalence was not stated.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read VI.10.2, printed p.208 / PDF p.214:

> Posons `R_Ω = End_G(Π_Ω)`. Exactement comme en VI.4.1, on introduit les foncteurs
> `F_{Π_Ω} : M(G)_Ω → M(R_Ω)_d, (π, V) ↦ Hom_G(Π_Ω, π)`,
> `G_{Π_Ω} : M(R_Ω)_d → M(G)_Ω, M ↦ M ⊗_{R_Ω} Π_Ω`.
> La démonstration du théorème VI.4.1 peut être recopiée mot pour mot et l'on obtient :
>
> **Théorème.** Les foncteurs sont quasi-inverses et réalisent une équivalence de
> catégories entre `M(G)_Ω` et `M(R_Ω)_d`.

The published `BernsteinBlockHomEquivalenceStatement` states that `F_{Π_Ω}` is an
equivalence. Its Markdown records that the identification of the quasi-inverse with
`G_{Π_Ω}` is not stated. This unit states it, in the same setting and in the same way as
the published VI.4.1 analogue `RationalSummandTensorQuasiInverseStatement`.

## The statement

The binders are copied from `BernsteinBlockHomEquivalenceStatement`: a nonarchimedean
local field `F`, a group scheme `G` with the standard-family structure
(`family : BernsteinStandardFamily i ν`), a cuspidal datum `a`, an irreducible smooth `ρ₀`
of the common norm kernel of the standard Levi of `a` with an injective map into the
restriction of `a.representation`, and `Π_Ω` the normalized induction of
`Π_D = ind_{⁰M}^{M} ρ₀` along the standard parabolic of `a`. The statement then asserts:

- `Π_Ω` lies in the published block
  `BernsteinSaturatedBlock i ν family (bernsteinInertialClass i ν family a)`; call `P` the
  block object;
- for every object `τ` of the block there is a `ℤ`-linear map
  `ev : (P ⟶ τ) ⊗[ℤ] P.obj → τ.obj` with `ev (α ⊗ₜ w) = α(w)`, which is surjective and whose
  kernel is the `ℤ`-span of the elements `(r ≫ α) ⊗ₜ w − α ⊗ₜ r(w)` for `r ∈ End P`,
  `α : P ⟶ τ` and `w ∈ Π_Ω`.

## Formalization choices

These are the choices of the published VI.4.1 analogue, whose Markdown explains them in
detail.

- **The balanced tensor.** `Hom_G(Π_Ω, τ)` is a right `R_Ω`-module by precomposition and
  `Π_Ω` a left `R_Ω`-module by evaluation. `M ⊗_{R_Ω} Π_Ω` is the quotient of
  `M ⊗_ℤ Π_Ω` by the span of the balancing differences. The statement asserts that the
  evaluation from `M ⊗_ℤ Π_Ω` is onto with exactly this kernel, that is, the induced map
  `Hom_G(Π_Ω, τ) ⊗_{R_Ω} Π_Ω → τ` is bijective.
- **What is stated of `G_{Π_Ω}`.** Bijectivity of `ev` is Renard's isomorphism
  `G_{Π_Ω} F_{Π_Ω}(τ) ≅ τ`. With the published equivalence `F_{Π_Ω}`, every unital right
  `R_Ω`-module `M` is isomorphic to some `F_{Π_Ω}(τ)`, so `G_{Π_Ω}(M) ≅ τ` lies in the
  block and `G_{Π_Ω}` is a quasi-inverse of `F_{Π_Ω}`. The functor `G_{Π_Ω}` itself is not
  constructed.
- **The block.** The block is the published one, defined with the induction-occurrence
  support relation; its comparison with Renard's Jacquet-defined `M(G)_Ω` is the separate
  comparison recorded in `BernsteinBlock.md` and `BernsteinSupportComparison.md`, as for the
  published VI.10.2 statement.
- **Carriers.** `P.obj` and `τ.obj` are the underlying smooth representations;
  `SmoothRep.hom α.hom w` is `α(w)`.

## Why the statement is true

Renard: the proof of VI.4.1 applies word for word. `G_{Π_Ω} ∘ F_{Π_Ω}` is right exact and
commutes with direct sums because `Π_Ω` is a small projective generator of the block
(published `BernsteinInducedProgeneratorStatement`, VI.10.1). `ev` is the canonical
isomorphism for `τ = Π_Ω`. Every object of the block is a cokernel of a map between direct
sums of copies of `Π_Ω` (Lemma A.VIII.2), and the five lemma concludes.

## Remaining obligations

The proof is a separate obligation. It needs the published VI.10.1 statements (task
2174cd68) and the right exactness of balanced tensor products.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.CuspidalSupport.BernsteinBlockHomEquivalenceStatement` | the binders and objects of VI.10.2: `BernsteinStandardFamily`, `BernsteinCuspidalDatum`, `BernsteinSaturatedBlock`, `bernsteinSaturatedBlockProperty`, `bernsteinInertialClass`, `normalizedInductionFunctor`, `bernsteinLiteralLeviRep`, `rationalNormKernelSummandInduction` (through its imports) |
| `Mathlib.LinearAlgebra.TensorProduct.Basic` | the integer tensor product `⊗[ℤ]` |
