# Commutative algebra for subgroups with the full Lie algebra

This file proves the commutative-algebra lemmas used in the proof of
`LieSubgroupEqualityStatement` ([SubgroupEqualityStatement](SubgroupEqualityStatement.md)).
All declarations are in the namespace `Langlands.GroupScheme.Lie.SubgroupEquality`. It
mentions no group schemes: the lemmas are about rings, ideals and algebra maps.

## Provenance

These lemmas are internal, derived prerequisites. Milne, *Algebraic Groups* (2017),
Proposition 10.15 (printed pp.190–191) proves the target statement through dimension theory
(Proposition 1.37: `dim Lie(G) ≥ dim G`, with equality exactly for smooth `G`). Mathlib at this
pin does not prove that smooth algebras are regular, so the formal proof replaces the dimension
count by an argument on coordinate algebras. Translated to that setting: `A` is the coordinate
algebra of the ambient group, `B` that of the subgroup, `φ : A → B` the surjection given by the
closed immersion, and `ε` the counit of `A`. The lemmas below are standard facts (the Krull
intersection theorem, formal smoothness, idempotents on a connected spectrum); their proofs use
Mathlib's APIs directly and are not quoted from a particular source.

## Formal smoothness

`ker_le_pow_of_formallySmooth`: let `k` be a commutative ring, `π : A →ₐ[k] B` a surjection of
`k`-algebras with `B` formally smooth over `k`, and `m` an ideal of `A`. If
`RingHom.ker π ≤ m ^ 2`, then `RingHom.ker π ≤ m ^ N` for every `N`.

Proof. Fix `N`, let `q : A → A ⧸ m ^ N` be the quotient map, `T` the image of `m` and `J` the
image of `ker π`; then `J ≤ T ^ 2`, `T ^ N = 0` and hence `J` is nilpotent. The composite
`A → (A ⧸ m ^ N) ⧸ J` vanishes on `ker π`, so it factors through `B`
(`AlgHom.liftOfSurjective`), and formal smoothness lifts this map along the nilpotent
ideal `J` to `φ : B → A ⧸ m ^ N` (`Algebra.FormallySmooth.lift`). Then `φ (π a) - q a ∈ J` for
every `a`. By induction on `i`, using `Submodule.mul_induction_on` and the identity
`φ(π(xy)) - q(xy) = (φ(π x) - q x) φ(π y) + q x (φ(π y) - q y)`, one gets
`φ (π a) - q a ∈ T ^ (i + 1)` whenever `a ∈ m ^ i`. For `a ∈ ker π ∩ m ^ i` this says
`q a ∈ T ^ (i + 1)`, so `a ∈ m ^ (i + 1)` when `i + 1 ≤ N`
(`Ideal.mem_quotient_iff_mem_sup`). Induction on `i` up to `N` gives `ker π ≤ m ^ N`.

## Krull intersection

`exists_mem_mul_eq_self_of_le_pow`: in a Noetherian commutative ring `A`, if an ideal `I` lies
in `m ^ N` for every `N`, then there is `r ∈ m` with `r * x = x` for every `x ∈ I`.

Proof. Let `P = ⨅ i, m ^ i • ⊤`. The Artin–Rees lemma, in the form of stability of the
intersection of the `m`-stable filtration with the trivial filtration of `P`
(`Ideal.Filtration.Stable.inter_right`), gives `P ≤ m • P`, as in Mathlib's proof of the Krull
intersection theorem. Since `P` is finitely generated,
`Submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul` supplies `r ∈ m` acting as the
identity on `P`, and `I ≤ P`.

## Connected spectrum

`isIdempotentElem_eq_zero_or_one`: if `PrimeSpectrum A` is preconnected, every idempotent `e` of
`A` is `0` or `1`. The basic open set of `e` is clopen (`PrimeSpectrum.isClopen_iff`), hence
empty or everything; an idempotent with empty basic open set is nilpotent and therefore zero,
applied to `e` or to `1 - e`.

`eq_bot_of_mul_eq_zero_of_one_sub_mem`: if `PrimeSpectrum A` is preconnected, `I ≠ ⊤` is an
ideal, and `t` satisfies `t * x = 0` for all `x ∈ I` and `1 - t ∈ I`, then `I = ⊥`. Indeed
`t (1 - t) = 0`, so `1 - t` is idempotent; it is not `1` because `I` is proper, so it is `0`,
`t = 1`, and `I` is killed by `1`.

## Linear forms with the Leibniz rule

`exists_leibniz_ne_zero`: let `k` be a field, `A` a commutative `k`-algebra and `ε : A →ₐ[k] k`.
If `x ∈ ker ε` but `x ∉ (ker ε) ^ 2`, there is a `k`-linear form `f : A →ₗ[k] k` with
`f x ≠ 0` and `f (a * b) = ε a * f b + ε b * f a` for all `a, b`.

Proof. `x` is not in the `k`-subspace `p = (ker ε) ^ 2 + k · 1` (apply `ε` to a decomposition),
so a linear form vanishing on `p` and not at `x` exists
(`Submodule.exists_dual_map_eq_bot_of_notMem`). The Leibniz rule follows by writing
`a b = (a - ε a)(b - ε b) + ε a · b + ε b · a - ε a ε b · 1`, whose first term lies in
`(ker ε) ^ 2`.

## The annihilating element

`exists_annihilator_of_derivations`: let `F` be a field, `A` a Noetherian commutative
`F`-algebra, `B` a formally smooth commutative `F`-algebra, `φ : A →ₐ[F] B` surjective and
`ε : A →ₐ[F] F` with `ker φ ≤ ker ε`. If every linear form `δ : A →ₗ[F] F` satisfying
`δ (a * b) = ε a * δ b + ε b * δ a` vanishes on `ker φ`, then there is `f : A` with `ε f = 1`
and `f * x = 0` for every `x ∈ ker φ`.

Proof. By `exists_leibniz_ne_zero` and the hypothesis on linear forms, `ker φ ≤ (ker ε) ^ 2`.
Then `ker_le_pow_of_formallySmooth` puts `ker φ` in every power of `ker ε`, and
`exists_mem_mul_eq_self_of_le_pow` gives `r ∈ ker ε` fixing `ker φ`; take `f = 1 - r`.

## Tensor products

`productMap_mem_map_annihilator`: let `k` be a field, `A`, `B`, `C` commutative `k`-algebras,
`I` an ideal of `A`, and `c : A ⊗[k] B` with `(x ⊗ₜ 1) * c = 0` for every `x ∈ I`. Then for
all `φ : A →ₐ[k] C` and `g : B →ₐ[k] C`, `Algebra.TensorProduct.productMap φ g c` lies in the
image under `φ` of the annihilator of `I`.

Proof. Write `c = Σ_i a_i ⊗ b_i` in a `k`-basis `b` of `B`
(`TensorProduct.equivFinsuppOfBasisRight`). Left multiplication by `x ⊗ 1` multiplies each
coefficient `a_i` by `x`, so `(x ⊗ 1) c = 0` forces `x a_i = 0`: every `a_i` annihilates `I`.
Then `productMap φ g c = Σ_i φ (a_i) g (b_i)` lies in the ideal generated by `φ` of the
annihilator.
