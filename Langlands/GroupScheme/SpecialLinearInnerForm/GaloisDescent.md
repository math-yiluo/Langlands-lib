# Galois descent of algebras along a semilinear Galois action

Let `K` be a field, `L` a finite Galois extension of `K`, and `B` an
`L`-algebra (with compatible `K`-structure). A
`SemilinearGaloisAction K L B` is an action of `Gal(L/K)` on `B` by ring
endomorphisms `act σ` that is semilinear over `L`: it sends
`algebraMap L B l` to `algebraMap L B (σ l)`, `act 1` is the identity, and
`act (σ * τ) = act σ ∘ act τ`. The structure records only these
four fields; no continuity or topology is involved, since the group is
finite.

The module defines the fixed `K`-subalgebra `ρ.fixed` and proves that it
is a `K`-form of `B`:

* `descentEquiv : L ⊗[K] ρ.fixed ≃ₐ[L] B`, the `L`-algebra isomorphism
  induced by multiplication, with `descentEquiv_tmul` and
  `descentEquiv_one_tmul` giving its value on pure tensors;
* `induction_on`: every element of `B` is reached from the elements
  `algebraMap L B l * a` (with `a` fixed) by addition;
* `finiteDimensional_fixed`: if `B` is finite-dimensional over `L`, the
  fixed algebra is finite-dimensional over `K` (this needs only finiteness
  of `L/K`);
* `isCentral_fixed`: if `B` is central over `L` and nontrivial, the fixed
  algebra is central over `K`;
* `isSimpleRing_fixed`: if `B` is a simple ring, so is the fixed algebra;
* `reducedDegree_fixed`: for any `L`-algebra isomorphism of `B` with
  `Matrix (Fin m) (Fin m) L`, the canonical `reducedDegree K ρ.fixed`
  equals `m`.

The bijectivity statement `mulMap_bijective` (from which `descentEquiv`
is built) needs `[IsGalois K L]` and no hypothesis on `B` beyond the
action. Auxiliary declarations are the Galois trace `trace : B →ₗ[K]
ρ.fixed`, `b ↦ ∑ σ, act σ b`, its `ρ.fixed`-bilinearity
(`trace_fixed_mul`, `trace_mul_fixed`), the formula
`trace_algebraMap_mul` relating it to `Algebra.trace K L`, and the
`K`-linear maps `descentMap t : B → L ⊗[K] ρ.fixed` attached to
`t ∈ L ⊗[K] L`.

## Proof

This is classical Galois descent for vector spaces with a semilinear
action (Speiser's lemma), carried out here directly for algebras. The
Lean proof does not use a descent lemma from Mathlib or the Library;
instead it writes down an explicit inverse of the multiplication map.

By the Library's `GroupScheme.Descent.galoisTensorHom_surjective`
(the isomorphism `L ⊗[K] L ≅ ∏_{σ} L`, `a ⊗ b ↦ (a · σ b)_σ`), there is
`t ∈ L ⊗[K] L` whose image is the indicator of the identity
automorphism. For `t = ∑ aᵢ ⊗ bᵢ`, `descentMap t` sends `y` to
`∑ aᵢ ⊗ trace (bᵢ y)`. Two computations, each by induction on `t`, give

* `mulMap (descentMap t y) = ∑ σ, (galoisTensorHom t σ) • act σ y`,
  which is `y` for the chosen `t`;
* `descentMap t (l a) = (∑ σ, galoisTensorHom t σ * σ l) ⊗ a` for `a`
  fixed, using `trace (l a) = Tr_{L/K}(l) a` and
  `Algebra.trace = ∑ σ` for Galois extensions (Mathlib's
  `trace_eq_sum_automorphisms`); for the chosen `t` this is `l ⊗ a`.

So `descentMap t` is a two-sided inverse of `mulMap`.

Centrality: a central element `z` of the fixed algebra commutes with
every `l a`, hence (by `induction_on`) with all of `B`, so it is
`algebraMap L B l` for some `l`; invariance under the action gives
`σ l = l` for all `σ`, so `l ∈ K` by the Galois fixed-field
characterization (`IsGalois.mem_bot_iff_fixed`).

Simplicity: for a nonzero two-sided ideal `I` of the fixed algebra, the
set `J = {y ∈ B | ∀ l, trace (l y) ∈ I}` is a two-sided ideal of `B`
(closure under multiplication is checked on the generators `l a`) and
contains every nonzero `a ∈ I`, because `trace (l a) = Tr(l) a`. Since
`B` is simple, `1 ∈ J`; choosing `l` with `Tr_{L/K}(l) = 1`
(`Algebra.trace_surjective`, valid for separable extensions) gives
`1 ∈ I`.

The reduced degree statement composes `descentEquiv` with the given
matrix isomorphism and applies the Library's
`matrix_size_eq_reducedDegree`.

This module is an internal helper for the proof of
`SpecialLinearInnerFormNormOneStatement`; it adds no external-source
assertion beyond the standard facts cited above.
