# Reduction of root reducedness to the case of proportional roots

This module is a derived, conditional assembly step toward the published
`RootReducednessStatement`
(`Langlands.GroupScheme.Reductive.RootReducednessStatement`). Its main theorem,
`rootReducedness_of_rankOne`, proves

```
RankOneRootReducednessStatement.{u} → DynamicCentralizerReductiveStatement.{u} →
  RootReducednessStatement.{u}
```

It does **not** prove either premise. Both are published Library statements whose
proofs are separate obligations:

* `RankOneRootReducednessStatement`
  (`Langlands.GroupScheme.Reductive.RankOneRootReducednessStatement`): for a connected
  reductive group with a split maximal torus in which any two roots are linearly
  dependent over `ℤ`, any two roots are equal or opposite;
* `DynamicCentralizerReductiveStatement`
  (`Langlands.GroupScheme.Dynamic.CentralizerReductiveStatement`): every closed
  group-scheme representative of the dynamic centralizer of a cocharacter of a connected
  reductive group over a field is connected reductive.

The target statement and every file it imports are unchanged.

## Mathematical model

Milne, *Algebraic Groups* (2017), Section 21.c and Theorem 21.11 (printed
pp. 428–429, PDF pp. 444–445). For a root `α` of a split reductive group `(G, T)`,
Milne sets `T_α = Ker(α)_t`, the subtorus of `T` of codimension one, and
`G_α = C_G(T_α)`. In the proof of part (a), `G_α` is reductive as the centralizer of a
torus (17.59), `T` is a split maximal torus of it, and `Lie(G_α) = 𝔤^{T_α}` (10.34). So
the roots of `(G_α, T)` are the roots of `G` vanishing on `T_α`, that is, the roots that
are rational multiples of `α`. Part (b) is then proved inside `G_α`. This module carries out the
same passage from `G` to a smaller reductive group, with one change. It takes the
centralizer of one cocharacter `ζ` of `T` instead of the centralizer of the subtorus
`T_α`. The cocharacter is chosen inside `Ker(α)` and generic there. Then the roots of
`C_G(ζ)` are exactly the roots of `G` vanishing on `ζ`, and these are the roots
proportional to `α`. Milne's reductivity of `C_G(T_α)` (via 17.59) is replaced by the
premise `DynamicCentralizerReductiveStatement`. Milne's argument in rank one
(Proposition 20.32, Theorem 20.22) is replaced by the premise
`RankOneRootReducednessStatement`.

## Setting

The universe is an arbitrary `u`. The setting is a field `k : Type u`, a commutative
group scheme `T` over `Spec k`, and, in the centralizer section, group schemes `G` and
`L` over `Spec k` with `[IsAffineHom G.X.hom]`, `[IsAffineHom L.X.hom]` and
`[LocallyOfFiniteType G.X.hom]`, a homomorphism `i : T.toGrp ⟶ G`, a cocharacter
`ζ : cocharacterLattice T`, and a homomorphism `j : L ⟶ G` with
`hj : (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy j`.
`latticePairing T` is the published integral pairing of characters and cocharacters,
and `roots i` is the published set of roots (nonzero characters with nonzero weight
space on the actual Lie algebra).

## Lattice lemmas (namespace `RootReducedness`)

* `zsmul_ne_zero`: for split `T`, a nonzero integer multiple of a nonzero character is
  nonzero. It reduces to the published `IsSplitTorus.nsmul_ne_zero` through the natural
  absolute value.
* `not_linearIndependent_of_not_linearIndependent`: for split `T` and characters
  `a, b, c` with `a ≠ 0` and `c ≠ 0`, if `![a, b]` and `![a, c]` are both linearly
  dependent over `ℤ`, then so is `![b, c]`. From `s₁ a + t₁ b = 0` and
  `s₂ a + t₂ c = 0` the proof gets `t₁ ≠ 0` and `s₂ ≠ 0` from `zsmul_ne_zero`. It then
  checks `(s₂ t₁) b - (s₁ t₂) c = 0` with the nonzero coefficient `s₂ t₁`.
* `exists_cocharacter_pairing_eq_zero`: for split `T`, a nonzero character `α` and a
  finite set `s` of characters, there is a cocharacter `ζ` with `⟨α, ζ⟩ = 0` such that
  every `γ ∈ s` with `⟨γ, ζ⟩ = 0` is linearly dependent with `α` over `ℤ`.
  Proof: the published `IsSplitTorus.exists_pairing_eq_pos` gives `ν` with
  `⟨α, ν⟩ = D > 0`. Let `f γ = D • γ - ⟨γ, ν⟩ • α`. The published
  `IsSplitTorus.exists_pairings_ne_zero` gives `ξ` that pairs nonzero with every nonzero
  element of the finite set `f '' s`. Put `ζ = D • ξ - ⟨α, ξ⟩ • ν`. Then
  `⟨α, ζ⟩ = 0`, and `⟨γ, ζ⟩ = ⟨f γ, ξ⟩` by direct computation. So `⟨γ, ζ⟩ = 0`
  forces `f γ = 0`, which is the dependence relation `-⟨γ, ν⟩ • α + D • γ = 0` with
  `D ≠ 0`.
* `kernelCocharacter hT hα hs : cocharacterLattice T` (definition): for split `T`
  (`hT`), a nonzero character `α` (`hα : α ≠ 0`) and a finite set `s` (`hs : s.Finite`),
  the cocharacter chosen by `Classical.choose` from
  `exists_cocharacter_pairing_eq_zero hT hα hs`. It is one choice of a generic
  cocharacter in the kernel of `α`; it plays the role of Milne's subtorus `T_α` (see
  *Mathematical model*). The choice is not canonical, and only the two properties
  below are used.
* `latticePairing_kernelCocharacter`: `⟨α, kernelCocharacter hT hα hs⟩ = 0`.
* `not_linearIndependent_of_latticePairing_kernelCocharacter`: every `γ ∈ s` with
  `⟨γ, kernelCocharacter hT hα hs⟩ = 0` satisfies `¬ LinearIndependent ℤ ![α, γ]`.

Both properties are the two parts of `Classical.choose_spec` for the existence lemma.

## Centralizer lemmas (namespace `RootReducedness`)

* `comp_eq_powerHom`: `ζ ≫ γ = Gm.powerHom _ ⟨γ, ζ⟩` for a character `γ`. This is the
  published `eq_gmEndEquiv_zsmul` read through `latticePairing_apply`.
* `weightSpace_le_range_centralizer`: if `⟨α, ζ⟩ = 0`, then `weightSpace i α` lies in
  the range of the differential `Lie.targetMapLinear j _`. A weight vector of `α` is a
  weight vector of `ζ ≫ α = Gm.powerHom _ 0` for the `𝔾_m`-action through
  `groupHom ζ ≫ i` (published `weightSpace_le_comp`). By the published `dynamicLie`
  (Conrad–Gabber–Prasad, Proposition 2.1.8(1)), it is then a dual-number point of the
  dynamic centralizer. By
  `SubgroupFunctor.IsRepresentedBy.mem_range_lieKernelHomLinear`, it is then in the
  range of the differential of `j`.
* `mem_roots_torusFactor`: a root `α` of `i` with `⟨α, ζ⟩ = 0` is a root of
  `Dynamic.torusFactor i (groupHom ζ) hj : T.toGrp ⟶ L`, the factorization of `i`
  through `j`. A nonzero weight vector of `α` in the Lie algebra of `G` comes from a
  tangent vector of `L`. By the published `lieKernelHomLinear_mem_weightSpace_iff` and
  `Dynamic.torusFactor_comp`, that tangent vector lies in the `α`-weight space for `L`.
* `mem_roots_of_mem_roots_torusFactor`: every root `γ` of the torus factor is a root of
  `i` with `⟨γ, ζ⟩ = 0`. Being a root of `i` is the published `roots_subset_comp`, since
  `j` is a monomorphism. For the pairing, suppose `⟨γ, ζ⟩ ≠ 0` and take a
  `γ`-weight vector `Y` of `L`. Its image `X` in the Lie algebra of `G` is a weight
  vector of `i` for `γ`. So `X` lies in the weight space of
  `Gm.powerHom _ ⟨γ, ζ⟩` for `groupHom ζ ≫ i`. Since `X` is a tangent vector of the
  centralizer, `dynamicLie` also puts it in the weight space of `Gm.powerHom _ 0`.
  Reading both memberships through the published `DynamicLie.weightCoeffs_apply_of_mem`
  at the coefficient of `t ↦ t⁰` gives `X = 0`. Injectivity of the differential
  (`Lie.targetMapLinear_injective`) gives `Y = 0`. So the `γ`-weight space of `L` is
  zero, and `γ` is not a root.

## Main theorem

`rootReducedness_of_rankOne (hrank : RankOneRootReducednessStatement.{u})
(hcent : DynamicCentralizerReductiveStatement.{u}) : RootReducednessStatement.{u}`.

Let `G` be connected reductive with split maximal torus `i : T.toGrp ⟶ G`, and let
`α, β` be roots of `i` that are linearly dependent over `ℤ`.

1. Take `ζ = kernelCocharacter hT hα.1 hs` for `α` and the finite set `roots i`
   (finiteness `hs` is the published `IsSplitTorus.finite_relativeRoots`). By its two
   properties, `⟨α, ζ⟩ = 0` and every root vanishing on `ζ` is ℤ-dependent with `α`.
   The proof then generalizes `ζ` to a variable.
2. Let `j` be the published affine centralizer representative
   `Dynamic.Affine.centralizerHom (groupHom ζ ≫ i)`. It represents the dynamic
   centralizer (`isRepresentedBy_centralizerHom`) and is a closed subgroup
   (`isClosedSubgroup_centralizerHom`). Its source `L` is connected reductive by
   `hcent`.
3. The torus factor `iL : T.toGrp ⟶ L` is a maximal torus by the published
   `IsMaximalTorus.of_comp`, because `iL ≫ j = i`.
4. `⟨β, ζ⟩ = 0`: from a relation `s α + t β = 0` with `t ≠ 0`, pairing with `ζ` gives
   `t ⟨β, ζ⟩ = 0`.
5. By `mem_roots_torusFactor`, `α` and `β` are roots of `iL`. Any two roots `γ, δ` of
   `iL` are roots of `i` vanishing on `ζ` (`mem_roots_of_mem_roots_torusFactor`), so
   both are ℤ-dependent with `α`. By `not_linearIndependent_of_not_linearIndependent`
   (with `α ≠ 0`, `δ ≠ 0`), they are ℤ-dependent with each other.
6. `hrank` applied to `L`, `T`, `iL` gives `α = β ∨ α = -β`.

## Scope

The module is conditional on the two published statements above. Once both are
proved in the Library, `rootReducedness_of_rankOne` applied to the two proofs is an
unconditional proof of `RootReducednessStatement`. That final proof is a separate
`lean.proof` candidate.
