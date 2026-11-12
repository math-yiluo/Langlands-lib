# Normalized induction from a cocompact closed subgroup and duality

Author: Worker 1222. Module
`Langlands.Representation.Unitary.CompactQuotientNormalizedInductionDualityStatement`,
namespace `Langlands.Renard.CompactRepresentation`. Statement
`CompactQuotientNormalizedInductionDualityStatement : Prop` (universe parameters `uG`, `v`);
nothing is proved here.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, IV.2.1, the paragraph after the Remarks, printed p.97 / PDF p.103. The registered
source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

In translation: let `H` be a closed subgroup of the t.d. group `G` and `(τ, E)` a smooth
representation of `H`. Assume `H \ G` compact, so that `Ind_H^G(τ, E) = ind_H^G(τ, E)`.
Induction does not preserve hermitian representations, because by Proposition III.2.2 (ii)
`ind_H^G(τ̃) = ind_H^G(τ ⊗ δ_{H\G})~` and `ind_H^G(τ^h) = ind_H^G(τ ⊗ δ_{H\G})^h`. To obtain
an induction that preserves hermitian representations one normalizes by `δ_{H\G}^{1/2}`,
which is unambiguous since `δ_{H\G}` takes values in `ℝ_+^×`:

`i_H^G τ = ind_H^G(τ ⊗ δ_{H\G}^{1/2})`, (IV.2.1.1)

and then

`(i_H^G τ)~ = i_H^G(τ̃)`, `(i_H^G τ)^h = i_H^G(τ^h)`. (IV.2.1.2)

The published `HermitianRepresentationStatements` (same namespace) states the IV.2.1 Remarks
and lists (IV.2.1.1)–(IV.2.1.2) as not stated there. This module states them.

## Statement

The statement quantifies over a group `G : Type uG` with `[TopologicalSpace G]`,
`[NonarchimedeanGroup G]`, `[LocallyCompactSpace G]` and `[T2Space G]`, a subgroup `H` with
`IsClosed (H : Set G)`, and instances `[LocallyCompactSpace H]` and
`[CompactSpace (Induction.LeftQuotient H)]`. `Induction.LeftQuotient H` is the quotient of `G`
by the relation whose classes are the right cosets `H g`, Renard's `H \ G`. It sets
`δ := Hecke.Homomorphism.relativeModularCharacter H.subtype continuous_subtype_val` and calls a
smooth character `χ : Induction.SmoothCharacter ℂ H` a *half modulus* when every value
`χ(h)` is a positive real number and `χ(h)² = δ(h)` for all `h`. It asserts:

1. a half modulus exists;
2. for every half modulus `χ`, with
   `i := SmoothRep.toRep ⋙ Induction.normalizedCompactInductionFunctor H χ`, a functor from
   `SmoothRep.{0, uG, v} ℂ H` to `SmoothRep.{0, uG, max uG v} ℂ G`:
   - (contragredient) there is a natural isomorphism
     `i.op ⋙ SmoothRep.contragredientFunctor ≅ SmoothRep.contragredientFunctor ⋙ i`, that is
     `(i τ)~ ≅ i(τ̃)` naturally in `τ`;
   - (hermitian contragredient) for all smooth `τ`, `σ` of `H` and every `ℂ`-antilinear
     bijection `e : σ ≃ₗ⋆[ℂ] SmoothDual τ.representation` that is `H`-equivariant for
     `smoothContragredient`, there is a `ℂ`-antilinear bijection
     `E : i σ ≃ₗ⋆[ℂ] SmoothDual (i τ).representation` that is `G`-equivariant for
     `smoothContragredient`.

## The objects

- `relativeModularCharacter H.subtype continuous_subtype_val` is the published smooth
  character `h ↦ Δ_H(h) Δ_G(h)⁻¹` (module `Langlands.Representation.Hecke.CompactInductionModels`),
  where `Δ` is Mathlib's modular character, the inverse of Renard's `δ`. It is therefore
  `δ_G / δ_H` on `H`, which is Renard's definition `δ_{H\G} = δ_G / δ_H` (II.3.9, printed p.49 /
  PDF p.55). Its values are positive reals.
- A half modulus is `δ_{H\G}^{1/2}`. The two conditions determine it: a positive real number
  has exactly one positive square root. Item 1 asserts that this square root is a smooth
  character.
- `Induction.normalizedCompactInductionFunctor H χ` is the published functor
  `A ↦ ind_H^G(A ⊗ χ)`: twist by `χ` (`h ↦ χ(h) τ(h)`), then compact induction, the functions
  `f` with `f(h g) = χ(h) τ(h) f(g)`, smooth under right translation and with compact support
  modulo `H`. With `χ = δ_{H\G}^{1/2}` this is (IV.2.1.1). `SmoothRep.toRep` forgets that the
  input is smooth. Because `H \ G` is compact, compact induction equals full smooth induction,
  as the source says; the statement uses compact induction, the `ind` of (IV.2.1.1).
- `SmoothRep.contragredientFunctor` is the published smooth contragredient `π ↦ π̃`.
- Renard's `τ^h` is the complex conjugate of `τ̃`. The Library has no conjugate-representation
  construction. As in `HermitianRepresentationStatements`, the statement describes `τ^h`
  through `ℂ`-antilinear equivariant bijections: `σ ≅ τ^h` exactly when there is an
  `H`-equivariant antilinear bijection `σ ≃ τ̃`. The hermitian clause says that whenever `σ` is
  a model of `τ^h`, `i σ` is a model of `(i τ)^h`. This is `(i_H^G τ)^h = i_H^G(τ^h)`, read
  through models. A model of `τ^h` always exists (the conjugate space of `τ̃`), so the clause
  is not vacuous.

## Faithfulness notes

- The source's equalities are read as isomorphisms. The contragredient identity is asserted
  as a natural isomorphism of functors, which is how Theorem III.2.7, its source, provides it.
  The hermitian identity is asserted for each `τ`.
- `G` is assumed nonarchimedean, locally compact and Hausdorff. For locally compact Hausdorff
  groups this is equivalent to being totally disconnected (van Dantzig), which is Renard's
  "groupe t.d.". The published `relativeModularCharacter` needs the nonarchimedean structure.
- `[LocallyCompactSpace H]` is an instance hypothesis needed by `relativeModularCharacter`. It
  holds for every closed subgroup of a locally compact group, so it adds no restriction.
- Every smooth `τ` is allowed, with no admissibility or finiteness, as in the source.
- The source does not assert that a smooth square root exists; it says the normalization "is
  defined without ambiguity". Item 1 makes this explicit, so that the quantification over half
  moduli is not vacuous.

## Remaining obligations

The proof is a separate obligation. The source's computation uses Proposition III.2.2 (ii),
or Theorem III.2.7 (`Ind_H^G(W̃) ≃ ind_H^G(W ⊗ δ_{H\G})~`), with `W = τ ⊗ δ_{H\G}^{-1/2}`,
and the identity `ind_H^G(ρ)‾ = ind_H^G(ρ̄)`, which holds for the normalized induction because
`δ_{H\G}^{1/2}` is real. A special case of the contragredient identity, for `P \ G` compact and
a continuous section of a projection `P → M`, is the proved
`Induction.exists_integralDualEquiv_of_section` (module
`Langlands.Representation.Induction.CompactQuotientSmoothDuality`). None of this is asserted
here.

## Provenance

Source assertions (IV.2.1.1)–(IV.2.1.2) of Renard 2026 IV.2.1, for an arbitrary closed
subgroup with compact quotient and every smooth representation. Formal choices: the published
relative modular character for `δ_{H\G}`, its positive square root characterized by two
conditions together with its existence, the published normalized compact induction functor,
the contragredient identity as a natural isomorphism, and the hermitian contragredient
described through antilinear equivariant bijections.
