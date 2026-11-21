# Existence of character families satisfying the cyclic block recurrence

Derived from Clozel–Rajan, *Solvable base change*, arXiv:1806.02513v1, §6, the character recurrence (6.15), `η_(α+1) ∘ σ = ω η_α` for `α` modulo `d` (PDF p. 19), and the computation after (6.5) (PDF p. 16). That computation shows that `∏_i σ^i ω(w) = ω(N_(E/F) z)` is trivial because `ω` restricts trivially to `N_(E/F)(C_E) ⊂ C_F`. Clozel–Rajan choose characters `η_α` satisfying the recurrence. This file proves that such a choice exists for every starting character `η₀`, as a family indexed by `ZMod d` with `d = [E : F]`.

## A single arithmetic automorphism

Let `E` be a number field, `σ : E ≃+* E` a ring automorphism and `ω` a Hecke character of `E` (an actual continuous character of the idele classes of `E`, not necessarily of finite order). Write `σ(y)` for `ideleClassEquiv σ y`, the actual arithmetic action on idele classes.

- `recurrenceStep σ ω χ = ω⁻¹ · HeckeCharacter.comap σ χ` is the character `y ↦ ω(y)⁻¹ χ(σ(y))`. One application of this step goes one place back along the recurrence: if `η_(α+1) = χ`, then `η_α = recurrenceStep σ ω χ`.
- `recurrenceStep_iterate_apply` evaluates the `m`-fold iterate:

  `(recurrenceStep σ ω)^[m] χ (y) = χ(σ^m(y)) · (∏_(j<m) ω(σ^j(y)))⁻¹`.

  The proof is induction on `m`, using `Function.iterate_succ_apply`, `Function.iterate_succ_apply'` and `Finset.prod_range_succ`.
- `exists_recurrence` assumes that `σ^d` acts trivially on idele classes (`hσ`) and that `∏_(j<d) ω(σ^j(y)) = 1` for every `y` (`hω`), for some `d ≠ 0`. It then gives, for every `η₀`, a family `η : ZMod d → HeckeCharacter E` with `η 0 = η₀` and

  `HeckeCharacter.comap σ (η (α + 1)) = ω * η α`  for all `α : ZMod d`,

  that is, `η_(α+1)(σ(y)) = ω(y) η_α(y)`. The family is `η α = (recurrenceStep σ ω)^[(−α).val] η₀`. Under the hypotheses, the evaluation formula shows that `η₀` is a periodic point of period `d` for the step. Since `(−α).val = ((−(α+1)).val + 1) mod d`, `Function.IsPeriodicPt.iterate_mod_apply` gives `η_α = recurrenceStep σ ω (η_(α+1))`, which is the recurrence after multiplying by `ω`.

## Galois form

Now let `E/F` be a Galois extension of number fields, in independent universes.

- `ideleClassEquiv_iterate`: the `j`-fold iterate of the arithmetic action of `σ ∈ Gal(E/F)` is the action `relativeIdeleClassAut F E (σ ^ j)` of the power `σ^j`.
- `exists_recurrence_of_isTrivialOnNorm`: assume `σ` generates the Galois group (`hgen : ∀ τ, τ ∈ Subgroup.zpowers σ`) and assume `HeckeCharacter.IsTrivialOnNorm E (ω.comp (ideleClassInclusion (K := F) (L := E)))`, i.e. the restriction of `ω` to `C_F` is trivial on the idele-class norms from `E`. Then for every `η₀` there is a family `η : ZMod (Module.finrank F E) → HeckeCharacter E` with `η 0 = η₀` and `HeckeCharacter.comap σ.toRingEquiv (η (α + 1)) = ω * η α` for all `α`.

  The order of `σ` is `[E : F]`, by `orderOf_eq_card_of_forall_mem_zpowers` and `IsGalois.card_aut_eq_finrank`. So `σ^[E:F] = 1`, which gives `hσ`. For `hω`, the powers `σ^j` with `j < [E : F]` enumerate the Galois group without repetition (`IsCyclic.image_range_orderOf` and `pow_injOn_Iio_orderOf`). The product of `ω` over the orbit is therefore `ω(∏_τ τ(y))`. By the published `ideleClassNormGaloisProduct`, `∏_τ τ(y)` is the image in `C_E` of the idele-class norm of `y`, and `ω` of that is `1` by hypothesis.

The hypothesis holds in the setting of `CyclicPrimeTwistedCuspidalObstructionStatement`, where `HeckeCharacter.HasNormKernel E (χ.comp (ideleClassInclusion …))` is assumed: `HasNormKernel.isTrivialOnNorm` gives it for `ω = χ`. It also holds for `ω = χ⁻¹`, whose values are the inverses.

## Use with the twisted endoscopic condition

For the labels `I = ZMod [E : F]` and a labelling `κ` of the Galois group with `κ σ = ofAdd 1`, the conclusion of `exists_recurrence_of_isTrivialOnNorm` is exactly the recurrence `IsBlockRecurrence` of `CyclicBlockSumTwistedEndoscopy`, the hypothesis of its twisted endoscopic condition. This file does not import that module and does not construct `κ`.

## Scope

This file proves only existence. It does not prove uniqueness up to the evident ambiguity, does not compare different choices of `η₀`, and does not prove distinctness of the values `η_α(t^p)` used for ellipticity. It contains no statement about endoscopic data, transfer or traces.
