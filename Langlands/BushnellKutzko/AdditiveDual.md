# The additive character `ψ_A`, the dual `S^*` and the functions `ψ_b` (Bushnell–Kutzko 1993, §1.1)

Source: C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open
subgroups*, Annals of Math. Studies 129 (1993), `bushnell-kutzko-1993-admissible-dual-gln`,
§1.1: the notation list on printed pp. 19–20 (PDF pp. 31–32) and (1.1.4)–(1.1.6) on printed
p. 22 (PDF p. 34). PDF page = printed page + 12.

The module imports only Mathlib. `K` is a field, `V` a `K`-vector space and
`A = End_K(V) = Module.End K V`. In BK93, `K = F` is a nonarchimedean local field and `V` is
finite-dimensional. None of the three definitions needs these hypotheses, so they are not
assumed. Characters take values in `ℂ` (Mathlib's `AddChar`).

## `traceCharacter ψF` (`ψ_A`, BK93 pp. 19–20)

BK93 fixes "some fixed continuous character `ψ_F` of the additive group of `F`, with conductor
`𝔭_F`" (p. 19) and sets `ψ_A = ψ_F ∘ tr_{A/F}`, where tr is the trace (p. 20).

`traceCharacter (ψF : AddChar K ℂ) : AddChar (Module.End K V) ℂ` is the composite of `ψF` with
the trace `LinearMap.trace K V`, viewed as an additive monoid homomorphism
(`AddChar.compAddMonoidHom`). `traceCharacter_apply` gives `ψ_A(x) = ψF(tr x)` by `rfl`.

The conductor condition on `ψ_F` is not part of the definition. Statements that need it assume
it as a hypothesis: `AdditiveDualityStatement` assumes `ψF` trivial on `𝔭_F` and nontrivial on
`𝔬_F`. Continuity is not assumed anywhere. A character trivial on the open subgroup `𝔭_F` is
locally constant, hence continuous.

## `additiveDual ψ S` (`S^*`, BK93 (1.1.4), p. 22)

BK93 (1.1.4): for a subset `S` of `A`, `S^* = {x ∈ A : ψ_A(xs) = 1 for all s ∈ S}`.

`additiveDual (ψ : AddChar (Module.End K V) ℂ) (S : Set (Module.End K V)) : Set (Module.End K V)`
is `{x | ∀ s ∈ S, ψ (x * s) = 1}`. The character is a parameter. BK93's dual is the case
`ψ = traceCharacter ψF`. `mem_additiveDual` is the membership lemma (`Iff.rfl`).

## `elementCharacter ψ b` (`ψ_b`, BK93 (1.1.6), p. 22)

BK93 (1.1.6) attaches to `b ∈ 𝔓^{-n}` the character `ψ_b` of `U^{r+1}(𝔄)` given by
`ψ_b(1 + x) = ψ_A(bx)` for `x ∈ 𝔓^{r+1}`.

`elementCharacter (ψ : AddChar (Module.End K V) ℂ) (b : Module.End K V) : (Module.End K V)ˣ → ℂ`
is the function `g ↦ ψ(b(g - 1))` on all of `G = Aut_K(V)`. Writing `g = 1 + x`, this is
BK93's formula. It is only a function, not a homomorphism. BK93 uses it on `U^{r+1}(𝔄)` for
`n > r ≥ ⌊n/2⌋`, where it is a character trivial on `U^{n+1}(𝔄)`. That claim, and the
isomorphism (1.1.5) it induces, are part of `AdditiveDualityStatement`.
`elementCharacter_apply` is the defining equation (`rfl`).
