# Cocenters of split-torus centralizers in simply connected groups are induced

Authors: Worker 1532 and Worker 1390.

`Langlands.GroupScheme.SplitTorusCentralizerCocenterInducedStatement.{u}`
is a proposition definition, not a theorem. It states that for the
centralizer `M = Z_G(A)` of a split subtorus `A` of a simply connected
group `G` over a field `k`, the cocenter `M / M_der` is an induced torus.
The module proves nothing. In particular, the argument recorded below is
provenance for the statement, not a proved result.

## The proposition

For every field `k : Type u`, quantify over every

- `G : GroupScheme (Spec (CommRingCat.of k))` with `IsSimplyConnected G`;
- `A : CommGroupScheme (Spec (CommRingCat.of k))` and `a : A.toGrp ⟶ G`
  with `IsSplitSubtorus a`;
- `M : GroupScheme (Spec (CommRingCat.of k))` and `j : M ⟶ G` with
  `(torusCentralizer a).IsRepresentedBy j`;
- `D : GroupScheme (Spec (CommRingCat.of k))` and `d : D ⟶ M` with
  `IsDerivedSubgroup d`;
- `D' : CommGroupScheme (Spec (CommRingCat.of k))` and
  `q : M ⟶ D'.toGrp` with
  `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q`.

The conclusion is `IsInducedTorus D'`.

These five hypotheses are the only ones. The universe `u` is arbitrary.
The field `k` has no perfectness, separability or characteristic
hypothesis. `G` is not assumed quasi-split. No root datum, parabolic
subgroup, maximal torus or description of the character lattice of `D'`
is supplied.

The imports are the five modules named by the task, together with
`Langlands.GroupScheme.Torus.Induced`. That module publishes
`IsInducedTorus` (task `81a25228-bad4-49ef-a956-811fbd795327`).

## Exact objects

- `IsSimplyConnected G` (module `Langlands.GroupScheme.SimplyConnected.Basic`)
  is a structure with two fields. The first, `IsSemisimple G`, says that `G`
  is connected reductive with finite scheme-theoretic centre. The second
  says that every central isogeny `H ⟶ G` from a semisimple group `H` is an
  isomorphism.
- `IsSplitSubtorus a` (module `Langlands.GroupScheme.Rational.SplitTorus`)
  is `IsSplitTorus A.toGrp ∧ IsClosedSubgroup a`. So `A` is isomorphic, as
  a group scheme over `k`, to `𝔾_m^I` for some finite type `I`, and the
  underlying morphism of `a` is a closed immersion. The trivial torus
  (`I` empty) is allowed. In that case `M = G`, and `D'` is the cocenter of
  the semisimple group `G`.
- `torusCentralizer a` (module `Langlands.GroupScheme.Rational.TorusCentralizer`)
  is the centralizer subgroup functor of `a`. Over a test scheme `U`, a
  point `g` of `G` belongs to it when, for every `V ⟶ U` and every
  `V`-point `t` of `A`, the restriction of `g` to `V` commutes with `a(t)`.
  `IsRepresentedBy j` (module `Langlands.GroupScheme.SubgroupFunctor`) is
  `Mono j.hom.hom ∧ SubgroupFunctor.range j = torusCentralizer a`. So `j` is
  a monomorphism whose points are exactly the centralizer points, and `M`
  is `Z_G(A)`. Closedness of `j` is not required.
- `IsDerivedSubgroup d` (module `Langlands.GroupScheme.Derived.Basic`) is
  `IsClosedSubgroup d ∧ SubgroupFunctor.range d = derivedSubgroup M`. Here
  `derivedSubgroup M` is the pointwise intersection of the ranges of all
  closed subgroups of `M` whose range contains every commutator on every
  test scheme. So `d` is a closed immersion onto the scheme-theoretic
  derived subgroup `M_der`.
- `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q` (module
  `Langlands.GroupScheme.Rational.RootSubgroupStructureStatement`) says that
  the underlying morphism of `q` is flat, surjective and locally of finite
  presentation, and that the range of the scheme kernel `kernelι q` is
  `SubgroupFunctor.range d`. So `q` is an fppf quotient map with kernel
  `M_der`, and `D'` plays the role of `M / M_der`. Every commutative group
  scheme `D'` with such a map is covered.
- `IsInducedTorus D'` (module `Langlands.GroupScheme.Torus.Induced`,
  KP Definition 2.5.1) says the following. There are a finite Galois
  extension `E/k` with `E : Type u` such that the base change `D'_E` is a
  split torus, and a `ℤ`-basis `b` of the character lattice `X^*(D'_E)`.
  Every `σ ∈ Gal(E/k)` sends each `b i` to some `b j` under the Galois
  action `characterLattice.galoisRepresentation`.

## Source

Tasho Kaletha and Gopal Prasad, *Bruhat–Tits Theory: A New Approach*,
Cambridge University Press, 2023, registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`. Printed page = PDF page − 31.
The authors' 2024 corrections (`kaletha-prasad-2024-corrections`) do not
change Definition 2.5.1 or Lemma 2.6.27.

- **Definition 2.5.1 and the example after it**, printed p. 86 / PDF p. 117.
  The definition reads: "An `F`-torus `T` is called induced if the lattice
  `X^*(T)`, equivalently `X_*(T)`, has a `ℤ`-basis that is invariant under
  the Galois group of the splitting extension of `T`." The example after it
  reads: "If `G` is a quasi-split connected reductive `F`-group and `T` is
  a maximal `F`-torus contained in a Borel `F`-subgroup, and if in addition
  `G` is either simply connected or adjoint, then `T` is induced, since the
  fundamental weights or the simple roots, respectively, form a
  `Θ`-invariant basis of `X^*(T)`." Here `Θ = Gal(F^s/F)`.
- **Lemma 2.6.27 and its proof**, printed p. 105 / PDF p. 136. There `k`
  is a discretely valued Henselian field with perfect residue field, and
  `K` is its maximal unramified extension (KP §2.5(c), printed p. 88, and
  §2.6, printed p. 102). The
  lemma takes `G` simply connected and `M_0 ⊂ G` a minimal Levi subgroup,
  that is, `M_0 = Z_G(S)` for a maximal `k`-split torus `S` (proof of
  Fact 2.6.22 in §2.6(e), printed p. 104). The proof takes a maximally split maximal
  `K`-torus `T ⊂ M_0`. It notes that `T` is also maximally split in the
  quasi-split simply connected group `G_K`, so `T` is induced by the
  example above. With `T_sc = T ∩ M_0,der` it says: "The latter is simply
  connected, so `T_sc` is also an induced torus, as is the quotient
  `D = T/T_sc`." It then applies Lemma 2.5.18 to `D`.

## Derived formulation

The proposition is a derived strengthening of one step of the proof of
Lemma 2.6.27, namely the assertion that `D = T / T_sc` is induced. It is
not a numbered result of KP. It differs from KP's step in three ways.

- **The cocenter instead of `T / T_sc`.** `M_0` is connected reductive and
  `M_0 = Z(M_0)^0 · M_0,der` with `Z(M_0)^0 ⊂ T`. So `T → M_0 / M_0,der`
  is surjective with kernel `T ∩ M_0,der = T_sc`, and
  `T / T_sc = M_0 / M_0,der`. The proposition is about `M / M_der`
  directly and does not mention a maximal torus.
- **Centralizers of split subtori over any field instead of the minimal
  Levi subgroup over `K`.** In KP's situation `(M_0)_K = Z_{G_K}(S_K)`,
  where `S_K` is `K`-split but in general not maximal `K`-split. So KP's
  `D` is the case `k = K`, `G = G_K`, `A = S_K`. To apply the proposition
  there, a user must supply the simple connectivity of `G_K` (for example
  from the Library statement `IsSimplyConnectedFieldExtensionStatement`)
  and identify the base changes of the centralizer and of its cocenter.
  Neither is part of this statement.
- **No quasi-splitness.** KP's argument uses that `G_K` is quasi-split and
  that `T` lies in a Borel `K`-subgroup. The proposition assumes neither.
  The reason it should still hold is the following argument.

### Why it should hold without quasi-splitness (provenance only)

This argument is standard reductive-group theory over `k^sep`. It is not
proved in this module or anywhere in the Library.

Because `A` is `k`-split, choose a cocharacter `λ` of `A` that pairs
nontrivially with every root of `A` in `G`. Then `M = Z_G(A) = Z_G(λ)` is
the Levi factor of the `k`-parabolic subgroup `P = P_G(λ)`. Choose a
maximal `k`-torus `T ⊂ M` and, over `k^sep`, a Borel subgroup
`T ⊂ B ⊂ P`. Let `Δ` be the simple roots of `(G, T)` for `B`, and let
`Δ_M ⊂ Δ` be the simple roots of `M` for `B ∩ M`.

Since `G` is simply connected, the simple coroots form a basis of
`X_*(T)`, and the fundamental weights `ω_α` form the dual basis of
`X^*(T)`. A character of `M / M_der` is a character of `T` that is trivial
on `T ∩ M_der`. That torus is generated by the coroots `α^∨`,
`α ∈ Δ_M`. Hence

`X^*(M / M_der) = ℤ{ω_α : α ∈ Δ ∖ Δ_M}`.

Let `σ` be a Galois element. Since `P` and `T` are defined over `k`,
`σ(B)` is a Borel subgroup of `P` containing `T`. The Borel subgroups of
`P` containing `T` are conjugate under `W_M = N_M(T)/T`. So the Weyl
element `w_σ` with `w_σ σ(B) w_σ⁻¹ = B` lies in `W_M`. The twisted action
`σ_* = w_σ ∘ σ` preserves `B` and `M`, so it permutes `Δ ∖ Δ_M` and sends
`ω_α` to `ω_{σ_* α}`. `W_M` acts trivially on `X^*(M)`, because characters
of `M` are invariant under conjugation by `N_M(T)`. So on
`X^*(M / M_der)` the Galois action is `σ_*`, which permutes the basis
`{ω_α : α ∉ Δ_M}`.

### What a proof along this route must establish

For the actual groups of the statement, without further premises, a proof
along this route has to establish the following.

- `M` is connected reductive, and `D'` is a torus that splits over some
  finite Galois extension `E/k`. Moreover the fppf quotient `q`
  identifies `X^*(D'_E)` with the characters of `T_E` trivial on
  `T_E ∩ M_der`.
- The Library notion `IsSimplyConnected G` implies that the simple coroots
  of `G_E` form a basis of `X_*(T_E)`. The Library states this necessity
  direction for an actual split maximal torus with a supplied finite reduced
  root datum: `SplitSimplyConnectedCorootSpanStatement`
  (`Langlands/GroupScheme/SimplyConnected/SplitNecessityStatement.lean`)
  concludes that the integral coroots span the whole cocharacter lattice.
  The theorem `splitSimplyConnectedCorootSpan_of_inputs`
  (`Langlands/GroupScheme/SimplyConnected/SplitNecessityAssembly.lean`)
  derives it from the three structural inputs bundled in
  `SplitSimplyConnectedCorootSpanInputsStatement`. That is a conditional
  reduction, not an unconditional proof. A proof along this route must also
  supply whatever of those inputs is still unproved, the simple
  connectivity of `G_E` (`IsSimplyConnectedFieldExtensionStatement`), a
  finite reduced root datum of the actual torus `T_E ⟶ G_E`, and the
  passage from "the coroots span `X_*(T_E)`" to "the simple coroots for `B`
  form a basis". The converse criterion is
  `SplitCorootSpanSimplyConnectedStatement`
  (`Langlands/GroupScheme/SimplyConnected/SplitCriterionStatement.lean`),
  which this route does not need.
- The parabolic `P` defined by `A` is defined over `k`, that is,
  Galois-stable, and has Levi factor `M`.
- The Weyl elements restoring `B` lie in `W_M`.
- The characters of the actual `D'_E` whose pullbacks along
  `T_E → M_E → D'_E` are the fundamental weights `ω_α`, `α ∉ Δ_M`, form a
  basis of `X^*(D'_E)` that `Gal(E/k)` permutes.

### Why the split hypothesis is needed

The hypothesis that `A` is split cannot be dropped. Let `ℓ/k` be a
separable quadratic extension, for example `ℂ/ℝ`. Let `T ⊂ SL_2` be the
anisotropic maximal torus of norm-one elements of `ℓ`, acting on `ℓ ≅ k²`
by multiplication. Its centralizer in `SL_2` is `T` itself. `T` is
commutative, so its derived subgroup is trivial and its cocenter is `T`.
Over `ℓ`, `X^*(T) = ℤ`, and the nontrivial element of `Gal(ℓ/k)` acts by
`-1`. The only `ℤ`-bases of `ℤ` are `{1}` and `{-1}`, and `-1` maps each
to the other. So `T` is not induced. In the formal statement this case is
excluded because `IsSplitSubtorus` fails for `T`.

## Uses

The proof task `8e4f0468-a0e2-46ee-9608-49cde642ba9d` (KP Lemma 2.6.27
and Corollary 2.6.28) is meant to apply this proposition over `K` to
`Z_K = Z_{G_K}(S_K)`. The cocenter there comes from the cocenter-existence
statement of task `11882097-d293-4f3d-b80d-c3c09ea66017`, and KP
Lemma 2.5.18 is then applied to `D'`. A proof of the proposition is a
separate `lean.proof@1` obligation.
