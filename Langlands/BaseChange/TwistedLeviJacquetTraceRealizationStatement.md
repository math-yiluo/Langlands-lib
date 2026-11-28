# Lifting twisted traces from relative Jacquet modules of Levi products

The module `Langlands.BaseChange.TwistedLeviJacquetTraceRealizationStatement`
states Rogawski's Proposition 7.1 for the standard parabolic subgroups of the
Levi products `M_B = ∏ᵢ GL_{Bᵢ}(E)` of `GL_n(E)`, in the unnormalized Jacquet
convention. It does not prove it. All declarations are in the namespace
`Langlands.BaseChange.TwistedLeviPaleyWiener`. The relative Jacquet module
`relJacquet` and its intertwiner `relJacquetSigmaIntertwiner` are defined in
`Langlands.BaseChange.TwistedLeviJacquet`.

## Statement

`TwistedLeviJacquetTraceRealizationStatement.{u', v', z'} : Prop` has the
field and topology preamble of `TwistedLeviJacquetDescentStatement` in
`Langlands.BaseChange.TwistedLeviPaleyWienerStatements`. Here `F : Type u'` is
a nonarchimedean local field of characteristic zero. `E : Type v'` is a field
with an `F`-algebra structure and the module topology. `σ : E ≃ₐ[F] E` and
`l n : ℕ` satisfy `IsCyclicAlgebra σ l`: `E/F` is cyclic of degree `l` with
generator `σ`. This includes the trivial extension (`l = 1`) and rank zero
(`n = 0`). Every Levi product `C.Levi E` carries its Borel σ-algebra and the
instances `levi_t2Space_of_finite`, `levi_locallyCompactSpace_of_finite` and
`levi_totallyDisconnectedSpace_of_finite`.

For block shapes `B C : BlockShape n` with
`hCB : C.parabolic E ≤ B.parabolic E` (so `C` refines `B`, possibly `C = B`),
arbitrary Haar measures `μ` on `M_B` and `ν` on `M_C`, and any
`f : SchwartzBruhat (M_C)`, the statement asserts that some
`φ : SchwartzBruhat (M_B)` satisfies `RealizesLeviJacquetTrace σ hCB μ ν f φ`.

`RealizesLeviJacquetTrace σ hCB μ ν f φ` holds when the following is true for
every complex vector space `W : Type z'`, every admissible representation `ρ`
of `M_B` on `W` of finite length (`(SmoothRep.of ρ hρ.1).HasFiniteLength`) and
every `A : ρ.Equiv (ρ.comp (leviAut σ B).toMonoidHom)`:

- the unnormalized relative Jacquet module `ρ_N = relJacquet hCB ρ` is
  admissible (witness `hJ`) and of finite length;
- with `A_N = relJacquetSigmaIntertwiner σ hCB A`,

```
twistedDistribution μ ρ   hρ A.toLinearMap   φ =
twistedDistribution ν ρ_N hJ A_N.toLinearMap f.
```

The representation `ρ_N` is the action of `M_C` through the block diagonal
section `relLeviSection hCB` on the coinvariants of the restriction of `ρ` to
`relParabolic E B C` by the kernel of `relProjection E B C`. The operator
`A_N` sends `[x]` to `[A x]`. Admissibility and finite length of `ρ_N` are
conclusions, not hypotheses. `twistedDistribution` is the trace of the
integrated action composed with the twisting operator, as in Rogawski §5. One
`φ` works simultaneously for all these pairs, and it may depend on `μ` and
`ν`.

`IsLeviJacquetTransfer σ hCB μ ν L` says that a linear map
`L : SchwartzBruhat (M_C) →ₗ[ℂ] SchwartzBruhat (M_B)` satisfies
`RealizesLeviJacquetTrace σ hCB μ ν f (L f)` for every `f`. The statement
asserts only the existence of `φ` for each `f`. Both sides of the trace
identity are linear in the test functions, and the admissibility and finite
length conclusions do not involve them. So choosing `φ` on a basis of
`SchwartzBruhat (M_C)` and extending linearly gives such an `L`. This module
does not prove that.

## Comparison with the sources

**Group and automorphism.** Rogawski (1988), introduction (printed p. 215),
fixes a connected reductive group over a `p`-adic field of characteristic `0`,
an outer automorphism `ε` of finite order `r` fixing a minimal parabolic, and
the semidirect products `M* = M ⋊ ⟨ε⟩` (§1, printed p. 216). For `n > 0` and
`l > 1` take the restriction of scalars from `E` to `F` of `∏ᵢ GL_{Bᵢ}`, whose
group of `F`-points is `M_B`, with `ε` the entrywise action of `σ`, of order
`l`. It fixes the minimal parabolic of upper triangular matrices in each
block. It is not inner, since it moves block scalar matrices in the center.
Its `ε`-stable standard Levi subgroups include the block diagonal subgroups of
the refinements `C`: the standard parabolic is `relParabolic E B C`, its
unipotent radical is the kernel of `relProjection E B C`, and `relLeviSection`
identifies `M_C` with the Levi factor.

**Proposition 7.1.** Rogawski, Proposition 7.1 (printed p. 219; proof on
pp. 219–221), says `r*_{GM}(F_tr(M)) ⊂ F_tr(G)` for `M ∈ L(G)^ε`. Here
`F_tr(M)` consists of the trace functions `π ↦ tr(π(f) π(ε))` on finite-length
`M*`-modules (§5, printed pp. 218–219), and `r*_{GM}` composes with the Jacquet
functor `r_{MG}` of §3 (printed p. 218). The descended operator on `V_N` is
`[v] ↦ [π(ε) v]` (§3). So for each `f` there is `φ` with
`tr(π(φ) π(ε)) = tr(r_{MG}(π)(f) r_{MG}(π)(ε))` for every finite-length
`G*`-module `π`, where `π(ε)^r = 1`. That §3 defines `r_{LM}` on the
Grothendieck groups of finite-length modules reflects the standard fact that
Jacquet modules of admissible finite-length representations are admissible of
finite length. This gives the first two conclusions.

**Arbitrary intertwiners and finite length.** The statement allows any
invertible intertwiner `A`, not only one with `A^l = 1`. For irreducible `ρ`,
`A^l` commutes with `ρ`, so by Schur's lemma it is a nonzero scalar. Rescaling
`A` by an `l`th root of its inverse gives a `G*`-module. Rescaling `A` rescales
`A_N` by the same factor, and both twisted traces are linear in the operator
(`twistedDistribution_smul`). For a finite-length `ρ`, `A` permutes the
subrepresentations, so a maximal chain of `A`-stable subrepresentations has
subquotients without proper nonzero `A`-stable subrepresentations. As in
Rogawski, Lemma 2.1 and Corollary 2.3 (printed p. 217), such a subquotient is
either irreducible or a direct sum of `t > 1` isotypic components permuted
cyclically by `A`. In the second case both twisted traces vanish. The relative
Jacquet functor is exact and additive, so it maps the chain to an
`A_N`-stable chain whose pieces are the Jacquet modules of the pieces, and both
twisted traces are additive along these chains. Hence the identity for
irreducible pairs gives it for all finite-length pairs with the same `φ`.

**Normalization and measures.** Rogawski's Jacquet functor is normalized: on
`V_N`, `m` acts by `δ_N(m)^{-1/2} π(m)`, with `δ_N` the modulus character of
`M` on `N`. The modulus is invariant under `ε`, so the same descended
operator intertwines both actions (see the Markdown of
`Langlands.BaseChange.TwistedLeviJacquet`). Apply the normalized statement to
the test function `δ_N^{1/2} f`. The factor `δ_N^{1/2}` cancels `δ_N^{-1/2}`
in the integrated action, so the normalized trace at `δ_N^{1/2} f` is the
unnormalized trace at `f`. Multiplication by `δ_N^{1/2}` preserves local
constancy and compact support. Rogawski fixes one Haar measure on each group
(§5). Scaling `μ` by `a > 0` and `ν` by `b > 0` multiplies the required `φ` by
`b/a`, so the two measures may be chosen independently.

**Trivial extension.** For `σ = 1` the automorphism is inner and Rogawski does
not apply. Bernstein–Deligne–Kazhdan, Proposition 3.2(ii) (printed p. 184;
proof in §5.3, printed pp. 188–189), gives `r*(F_tr(M)) ⊂ F_tr(G)` for
ordinary traces. Here `A` commutes with `ρ`. On an irreducible `ρ` it is a
scalar, and the dévissage above reduces finite-length pairs to irreducible
ones.

**Rank zero.** For `n = 0` both Levi products are trivial groups and the
kernel of the projection is trivial. Admissible representations are finite
dimensional, and the identity becomes
`φ(1) μ({1}) tr A = f(1) ν({1}) tr A`. It holds for
`φ = (ν({1}) / μ({1})) f`.

**Universes.** The carrier universe `z'` is independent of the universes `u'`
of `F` and `v'` of `E`. The relative Jacquet module of a carrier in `Type z'`
is a quotient of it, so it stays in `Type z'`.

These comparisons explain the formulation; they are not Lean results here. The
statement for `GL_n(E)` and its standard block parabolics is
`Langlands.BaseChange.TwistedJacquetTraceRealizationStatement`, which tests
only irreducible pairs and takes the admissibility of the Jacquet module as a
hypothesis.

## Sources

- J. D. Rogawski, *Trace Paley–Wiener theorem in the twisted case*, Trans.
  Amer. Math. Soc. 309 (1988), 215–229. Literature ID
  `rogawski-1988-twisted-trace-paley-wiener`, SHA-256
  `86fbe930fc1db80a3a0f279db5d83af85b7e37dc7e041d813ebc9f5fdcb7c274`.
  Introduction (p. 215); §§1–5 (pp. 216–219), with Lemma 2.1 and Corollary 2.3
  (p. 217); Proposition 7.1 (p. 219) and its proof (pp. 219–221). PDF page
  = printed page − 214.
- J. Bernstein, P. Deligne and D. Kazhdan, *Trace Paley–Wiener theorem for
  reductive p-adic groups*, J. Analyse Math. 47 (1986), 180–192. Literature ID
  `bernstein-deligne-kazhdan-1986-trace-paley-wiener`, SHA-256
  `2f422d01982c19c65541cb15297694b573ec517220fe7ecd3c0ec180c8c1e472`.
  Proposition 3.2(ii) (printed p. 184, PDF p. 5) and §5.3 (printed
  pp. 188–189, PDF pp. 9–10).
