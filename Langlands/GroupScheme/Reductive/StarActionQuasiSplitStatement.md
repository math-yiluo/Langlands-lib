# The star action of a quasi-split group is the natural action: statement

Author: Worker 15, for the algebraic and reductive group-scheme program
`2b5e4a00-9d44-49a4-9c89-979fb5b6233e` (Task 3483). The module contains one
`Prop`-valued definition and no proof.

## The statement

`Langlands.GroupScheme.StarActionQuasiSplitStatement` says the following. Let `k` be a
field in universe `u` and `G` a group scheme over `Spec k` whose structure morphism is
affine and locally of finite type. Suppose `G` is quasi-split (`IsQuasiSplit G`). That
means `G` is connected reductive and has a homomorphism `i : B ⟶ G` over `k` that is a
Borel subgroup and remains one over `AlgebraicClosure k`
(`IsGeometricBorelSubgroup`). Then there are Galois pinning data
`d : GaloisPinningData k k_s G`, with `k_s = SeparableClosure k`, such that

`(d.starAction σ).val = d.galoisAction σ` for every `σ : k_s ≃ₐ[k] k_s`.

Here `d.galoisAction` is the ordinary Galois action on the root datum of `(G_{k_s}, T_{k_s})`
for the torus `T` of `d`, which is defined over `k`. `d.starAction` is the star action of
`Reductive/StarAction`. By `GaloisPinningData.starAction_eq_galoisAction`, the conclusion
is equivalent to `d.galoisAction σ` preserving the chosen base for every `σ`.

## Source and provenance

Milne, *Algebraic Groups* (2022 corrected reprint), source `milne-2022-algebraic-groups`,
SHA-256 `f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`, §25.c,
printed p.555 (PDF p.566):

- Proposition 25.28(a): "The group `G` is quasi-split if and only if `Δ₀ = ∅`, in which
  case the `*`-action is the natural action of `Γ` on `Δ` as a subset of `X`."
- Its proof: "If `G` is quasi-split, we choose `B` to be defined over `k`, and then it is
  obvious that `Δ` is stable under `Γ`."

The statement is derived from these. It formalizes the forward direction: a quasi-split
group admits data for which the star action is the natural action. Milne's proof picks
the Borel subgroup over `k`. The existential over `d` expresses that choice: the torus of
`d` is a maximal torus contained in a Borel subgroup over `k`, and the base is the one
that Borel defines over `k_s`. The converse and the description through `Δ₀` need the
Tits index, which this statement does not involve.
