# Rigidity of quotients by approximate generators

This module is the algebraic heart of the reduction. It is derived from the proof
of Stacks Project Lemma 98.12.7 (Tag 07XH, `artin.pdf` printed pp. 20–21). That
proof constructs maps `R → A/m_A^n` by versality and shows they are isomorphisms
using Lemma 98.10.1(6), equality of associated graded rings, and length counts.
Here the isomorphism property is proved for every lift of the given
identification modulo squares. The tools are the Artin–Rees comparison and the
near-identity comparison of the two previous modules. Lengths are not used.

## Setting

Let `S = MvPolynomial ι R` over a commutative ring `R`, with an ideal `𝔪 : Ideal S`.
Let `Q` be a commutative ring (the completion in the application) with ideal `𝔫`,
and let `σ : S →+* Q`. The hypotheses on `σ` are:

- `hσ1`: every `x : Q` is congruent modulo every `𝔫 ^ n` to some `σ s`;
- `hσ2`: `σ s ∈ 𝔫 ^ n` implies `s ∈ 𝔪 ^ n`;
- `hσ3`: `𝔫 = 𝔪.map σ`.

`exists_mem_pow_sub_mem` derives the following: every element of `𝔫 ^ k` is
congruent modulo any `𝔫 ^ n` to `σ s` for some `s ∈ 𝔪 ^ k`.

A model is an `R`-algebra `T₀` with `σT : S →ₐ[R] T₀` and `ι₀ : T₀ →+* Q`,
satisfying `hισ : ι₀ (σT s) = σ s`. Let `u₀ 𝔫 ι₀ = 𝔫.comap ι₀`. The unramifiedness
hypothesis `hT` states that every `t` is congruent to some `σT s` modulo
`u₀ ^ 2`. From these:

- `σT_mem_pow`: `σT` maps `𝔪 ^ n` into `u₀ ^ n`;
- `mem_u₀_pow_of_mem`: `ι₀ t ∈ 𝔫 ^ k` implies `t ∈ u₀ ^ k`. Write `t ≡ σT s` modulo
  `u₀ ^ k`. Then `σ s ∈ 𝔫 ^ k`, so `s ∈ 𝔪 ^ k`.

For `b' : Fin r → T₀`, set `T = T₀ / (b')`, let `mT 𝔫 ι₀ b'` be the image of `u₀` in
`T`, and let `q 𝔫 σT ι₀ b' n : S →ₐ[R] T / mT ^ n` be the canonical map.

- `mk_mem_mT_pow_iff`: the image of `t` lies in `mT ^ n` if and only if
  `t ∈ u₀ ^ n ⊔ (b')`.
- `q_surjective`: each `q n` is surjective, by `hT` and the previous module.
- `q_eq_zero_iff`: `q n s = 0` if and only if
  `σ s ∈ Ideal.span (range (ι₀ ∘ b')) ⊔ 𝔫 ^ n`. For the reverse implication,
  write `σ s = ∑ p j * ι₀ (b' j) + e` and approximate each `p j` by `σ (sp j)`.
  Then `ι₀ (σT s - ∑ σT (sp j) * b' j) ∈ 𝔫 ^ n`, so this element lies in
  `u₀ ^ n` by `mem_u₀_pow_of_mem`.

## Rigidity

Let `A` be an `R`-algebra with `σA : S →ₐ[R] A`, let `π : Q →+* A` and let `mA` be an
ideal of `A`. Assume:

- `hπσ`: `π (σ s) = σA s`;
- `hπ`: `(mA ^ n).comap π = ker π ⊔ 𝔫 ^ n` for every `n`;
- `hπs`: `π` is surjective;
- `hAR`: for every `d`, every `z` in `Ideal.span (range (ι₀ ∘ b'))` with
  `z ∈ 𝔫 ^ d` lies in `ker π ⊔ 𝔫 ^ (d + 1)`. This is the conclusion of the
  Artin–Rees comparison.

Then `σA_mem_pow_iff` gives `σA s ∈ mA ^ n ↔ σ s ∈ ker π ⊔ 𝔫 ^ n`, and
`exists_sub_σA_mem_pow` shows that `S → A / mA ^ n` is surjective.

`rigidity` assumes `2 ≤ n` and an `R`-algebra map `φ : A →ₐ[R] T / mT ^ n` such that:

- `hloc`: `φ` maps `mA` into the image of `mT`;
- `hred`: for every `s`, the reduction of `φ (σA s)` modulo `mT ^ 2` equals
  `q 2 s`.

It concludes that `φ` is surjective with kernel `mA ^ n`.

First, `hloc` shows that `φ` kills `mA ^ n`. Each `φ (σA (X i)) - q n (X i)` maps to
zero modulo `mT ^ 2`, so `q_eq_zero_iff` and `exists_mem_pow_sub_mem` write it as
`q n (d i)` with `d i ∈ 𝔪 ^ 2`. The `R`-algebra endomorphism
`Φ = aeval (X i + d i)` of `S` satisfies `(q n).comp Φ = φ.comp σA` and is congruent
to the identity modulo `𝔪 ^ 2`. Hence it is near-identity.

The near-identity comparison applies with `I = σA⁻¹(mA ^ n)` and `I' = ker (q n)`.
Its hypothesis on `I` holds because `φ` kills `mA ^ n`. Its Artin–Rees hypothesis
`I' ⊓ 𝔪 ^ d ≤ I ⊔ 𝔪 ^ (d + 1)` for `d < n` follows from `hAR`. If `σ s = j′ + e`
with `j′` in the span of `ι₀ ∘ b'` and `e ∈ 𝔫 ^ n`, then `j′ = j + f` with
`j ∈ ker π` and `f ∈ 𝔫 ^ (d + 1)`. Approximating `f + e` by `σ sf` with
`sf ∈ 𝔪 ^ (d + 1)` gives `s - sf ∈ I`. The comparison makes `φ.comp σA` surjective
with kernel `I ⊔ 𝔪 ^ n = I`. Hence `φ` is surjective. If `φ a = 0`, then writing
`a ≡ σA s` modulo `mA ^ n` gives `s ∈ I`, so `a ∈ mA ^ n`.
