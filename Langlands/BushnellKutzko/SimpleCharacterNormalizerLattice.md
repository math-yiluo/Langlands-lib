# Multiplying `ℌ` and `𝔍^t` by adjoint preimages

This module proves two lattice inclusions for a stratum `[𝔄,n,r₀,β]` over a
nonarchimedean local field `F`, with a defining sequence `β = b₀, b₁, …, b_s` (a
`DefiningSequenceChoice`). They are used for BK93 (3.5.10) in the module
`SimpleCharacterNormalizerRestriction`. Here `r = finiteCriticalDepth L n β`, which is
`−k₀(β,𝔄)` when `β` is not scalar and the level `n` when `β` is scalar, the lattices `ℌ(β,𝔄)` and `𝔍(β,𝔄)`
are `simpleHLattice` and `simpleJLattice`, and
`𝔑_{−k}(β,𝔄) = {x ∈ 𝔄 : βx − xβ ∈ 𝔓^{−k}}` is `adjointLattice`.

Source: Bushnell and Kutzko, *The admissible dual of GL(N) via compact open
subgroups* (1993), literature ID `bushnell-kutzko-1993-admissible-dual-gln`,
SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`:
pure strata (1.5.5), printed p. 43 (PDF p. 55); defining sequences (2.4.2), printed
pp. 65–66 (PDF pp. 77–78); the lattices (3.1.7)–(3.1.8), printed pp. 89–90 (PDF
pp. 101–102); and the proof of
(3.5.9), printed pp. 121–122 (PDF pp. 133–134). That proof states, without details,
that every element of the outer factor `1 + 𝔔^{r−m}𝔑(β) + 𝔍^{⌊(r+1)/2⌋}(β)` normalizes
`H^m(β,𝔄)`. The two results below supply the lattice facts behind this statement.
They are derived here and are not stated as such in the source.

## The results

`mul_mem_simpleHLattice_of_mem_adjointLattice`: let `k` be a natural number with
`k < r`, let `y ∈ 𝔑_{−k}(β,𝔄)` and let `h ∈ ℌ(β,𝔄) ∩ 𝔓^{⌊k/2⌋+1}`. Then `yh` and `hy`
lie in `ℌ(β,𝔄)`.

`mul_mem_simpleJLayer_of_mem_adjointLattice`: let `r ≥ 0` and `t = ⌊(r+1)/2⌋`. For
`w ∈ 𝔍^t(β,𝔄) = 𝔍(β,𝔄) ∩ 𝔓^t` and `c ∈ 𝔑_{−r}(β,𝔄)`, the product `wc` lies in
`𝔍^t(β,𝔄)`.

## The proofs

Both proofs are inductions along the defining sequence. Let `−d₀, …, −d_{s−1}` be
the critical exponents of `b₀, …, b_{s−1}`, so that `b_{i+1} − b_i ∈ 𝔓^{−d_i}`. Here
`d_i` is the index of the next term (BK93 (2.4.2)(iii)–(iv)), so
`r ≤ d₀ < d₁ < … < n` and the signed exponents decrease strictly,
`−d₀ > −d₁ > … > −d_{s−1}`. The last term has critical exponent `−n` or is scalar. By
definition

`ℌ(b₀) = 𝔅_{b₀} + ℌ(b₁) ∩ 𝔓^{⌊d₀/2⌋+1}`, `𝔍(b₀) = 𝔅_{b₀} + 𝔍(b₁) ∩ 𝔓^{⌊(d₀+1)/2⌋}`,

with `ℌ(b_s) = 𝔅_{b_s} + 𝔓^{⌊n/2⌋+1}` and `𝔍(b_s) = 𝔅_{b_s} + 𝔓^{⌊(n+1)/2⌋}` for the
last term. Three facts are used.

1. *Adjoint preimages.* If `x ∈ 𝔄` with `[b₀,x] ∈ 𝔓^{−k}`, then `x ∈ ℌ(b₀)` when `2k`
   is less than all `d_i` and `n`, and `x ∈ 𝔍(b₀)` when `2k` is at most all `d_i` and
   `n`. The proof splits `x = y + z` with `y ∈ 𝔅_{b₀}` and `z ∈ 𝔓^{d₀−k}`, using the
   exactness statement `exists_commute_sub_mem`. Then `[b₁,z] ∈ 𝔓^{−k}` and induction
   applies to `z`. This is the argument of `adjointLattice_le_simpleJLattice` in
   `SimpleCharacterLoweringLattice`, here also for `ℌ`.
2. *Commutation with the centralizer.* If `c` commutes with `b₀`, then
   `[b₀,yc] = [b₀,y]c` and `[b₀,cy] = c[b₀,y]`.
3. *Passing to the next term.* If `x ∈ 𝔓^e` and `[b₀,x] ∈ 𝔓^{k'}` with `k' ≤ e − d₀`,
   then `[b₁,x] ∈ 𝔓^{k'}`, because `b₁ − b₀ ∈ 𝔓^{−d₀}`.

For `ℌ`, write `h = c + w` with `c ∈ 𝔅_{b₀}` and `w ∈ ℌ(b₁) ∩ 𝔓^{⌊d₀/2⌋+1}`. Since
`⌊d₀/2⌋ ≥ ⌊k/2⌋`, also `c ∈ 𝔓^{⌊k/2⌋+1}`. By fact 2,
`[b₀,yc] ∈ 𝔓^{−k+⌊k/2⌋+1} ⊆ 𝔓^{−⌊k/2⌋}`, and fact 1 with `2⌊k/2⌋ ≤ k < d_i` gives
`yc ∈ ℌ(b₀)`. The same holds for `cy`. By fact 3, `y ∈ 𝔑_{−d₀}(b₁)`. Induction with
`d₀` in place of `k` gives `yw, wy ∈ ℌ(b₁)`. These products lie in
`𝔓^{⌊d₀/2⌋+1}` because `y ∈ 𝔄`. For the last term, a summand in
`𝔓^{⌊n/2⌋+1}` stays there.

For `𝔍` the module proves a more general statement. Right multiplication by `c ∈ 𝔄`
with `[b₀,c] ∈ 𝔓^{−ℓ}` maps `𝔍(b₀) ∩ 𝔓^u` into `𝔍(b₀)` when `ℓ ≤ d_i` for all `i`,
`u` is at most every cutoff `⌊(d_i+1)/2⌋` and `⌊(n+1)/2⌋`, and `2(ℓ−u)` is at most
every `d_i` and `n`. Write `w = y + z` with `y ∈ 𝔅_{b₀} ∩ 𝔓^u` and
`z ∈ 𝔍(b₁) ∩ 𝔓^{⌊(d₀+1)/2⌋}`. Then `[b₀,yc] = y[b₀,c] ∈ 𝔓^{u−ℓ}`, and fact 1 gives
`yc ∈ 𝔍(b₀)`. By fact 3, `[b₁,c] ∈ 𝔓^{−d₀}`. Induction with `ℓ = d₀` and
`u = ⌊(d₀+1)/2⌋` gives `zc ∈ 𝔍(b₁)`, and `zc ∈ 𝔓^{⌊(d₀+1)/2⌋}`. The stated result is
the case `ℓ = r`, `u = t`, where `2(r − t) = 2⌊r/2⌋ ≤ r`. The factor `wc` stays in
`𝔓^t` because `c ∈ 𝔄`.

`definingSequence_recursionData` collects the facts about a defining sequence used
by the recursions: the units of each field `F[b_i]` lie in the stabilizer of the chain,
that is, they normalize `𝔄` (the purity condition (1.5.5)(ii) for the simple terms of
(2.4.2)(i)); and the depths `d_i` increase strictly, are at least `r` and are less than
`n`.
