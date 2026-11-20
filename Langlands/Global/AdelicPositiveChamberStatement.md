# The positive chamber of a parabolic is nonempty

Module `Langlands.Global.AdelicPositiveChamberStatement` states one
proposition, `Langlands.Global.PositiveChamberNonemptyStatement`, and proves
nothing.

## Statement

The data are those of the parabolic in
`Langlands.Global.EisensteinAbsoluteConvergenceStatement`, without the
unipotent radical, the compact subgroup and the automorphic form. They are a
number field `F`, a group scheme `G` over `F` (affine), a parabolic
`p : P → G` (closed immersion, `P` affine) with rational Levi `l : M → P`, a
split component `a : A → M` and a presentation
`r : ParabolicRootPresentation p l a`, with the injectivity and finiteness
instances needed for the Weyl-induced form, and `hA`, `hT` saying that `A` and
the presentation's maximal split torus `T` are split.

If `G` is connected reductive (`IsConnectedReductive G`), the statement says
that some `λ ∈ X^*(P) ⊗ ℂ` (`ComplexCharacterParameter F P`) satisfies
`r.IsRegularParameter hA hT 0 λ`. Unfolded, this is

`0 < B((Re λ)|_A, α)` for every `α ∈ r.unipotentRoots`.

Here `B` is the Weyl-induced positive definite form
`Langlands.Plancherel.weylInducedCharacterForm hA hT r.data.f r.data.i` on
`X^*(A) ⊗ ℝ`, `Re λ` is `parameterRealPart` and `(·)|_A` is
`realParameterRestriction (a ≫ l)`. The set `r.unipotentRoots` consists of the
nonzero restrictions to `A` of the positive relative roots of the
presentation, that is, the roots of `A` in the unipotent radical of `P`
(definitions in `Langlands.Global.AdelicEisensteinConvergenceStatement`). In
words: `Re λ` can be chosen in the open positive Weyl chamber of `𝔞_P^*`.

## Source

J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein
series*, J. Amer. Math. Soc. 37 (2024), registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`, §2.2, journal
p.191 (PDF page 5): "The series converges absolutely and locally uniformly in
`g` and `λ` for `Re(λ)` sufficiently regular in the positive Weyl chamber of
`𝔞_P^*` (MW II.1.5)". BL's Theorem 2.3 continues `E(φ, λ)` and `M(w, λ)` from
this region. That only makes sense because the region is not empty: the open
positive chamber of `𝔞_P^*` is a nonempty open cone, so it contains points
with every `⟨Re λ, α^∨⟩` as large as wanted. This module states that fact in
the form the Library's regularity predicate uses.

## Why it holds (explanatory, not proved here)

The restricted simple roots `Δ_P` of `A` are linearly independent in
`X^*(A) ⊗ ℝ`, and every root of `A` in the unipotent radical is a nonzero
combination of them with nonnegative integer coefficients. Since `B` is
positive definite, there is `x ∈ X^*(A) ⊗ ℝ` with `B(x, α) = 1` for every
`α ∈ Δ_P`, hence `B(x, α) > 0` for every root `α` in the unipotent radical.
Restriction `X^*(P) ⊗ ℝ → X^*(A) ⊗ ℝ` is onto, because the characters of `M`
restricted to its split component span `X^*(A) ⊗ ℚ` (BL §2.1, MW I.1.4). So
some `y ∈ X^*(P) ⊗ ℝ` has `y|_A = x`, and `λ = y ⊗ 1` works. When `P = G`
there are no roots and every `λ` qualifies.

## Role

The statements `IntertwiningRootHyperplaneStatement` and
`EisensteinRootHyperplaneStatement` (module
`Langlands.Global.AdelicRootHyperplaneStatement`) quantify continuation data
that agree with `M(w, λ)φ`, resp. `E(φ, λ)`, only for `R`-regular `λ`. If no
`λ` were regular, any meromorphic data would satisfy that hypothesis, and the
conclusion would fail for data with a pole off the root hyperplanes. The
reduction in `Langlands.Global.AdelicRootHyperplaneReduction` uses this
statement to obtain, in every linear coordinate system and for every `R`, a
nonempty open set of `R`-regular parameters. It scales `λ` by a large real
number and uses that there are finitely many roots.

The bound `0` is the weakest choice, since every `R`-regular parameter with
`R ≥ 0` is `0`-regular. Only the number field case is stated.
