# Reduction of Vogan's theorem for large Langlands quotients of `GL_n(ℝ)`

Lean module: `Langlands.Representation.Archimedean.RealLargeLanglandsQuotientReduction`.

This module splits `Langlands.Archimedean.RealLargeLanglandsQuotientInjectiveStatement`
(statement 3 of `RealGenericLargeReduction.md`, called S_V below) into two statements about
real standard modules. It proves the implication `realLargeLanglandsQuotientReduction`
(the two statements imply S_V) and the lemmas that proof uses. No hypothesis is added to
S_V. The two statements are only stated here and still need proofs.

Notation: `𝔤 = ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)` and `U(𝔤)` as in `RealGenericLargeReduction.md`. For a list `ds`
of real blocks, `I(ds)` is the `(𝔤𝔩_n(ℝ), O(n))`-module
`(realStandardRep n ds, realStandardLie n ds)` from `RealStandardModuleGKModule`. It acts on
the `O(n)`-finite functions `kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)`
of the Library's standard module, by right translation and right derivatives.

## Definitions

Both definitions work for any group `K`, any complex Lie algebra `L` and any complex vector
space `V` with `ρ : Representation ℂ K V` and a Lie algebra map `π : L → End(V)`.

* `IsGKSubmodule ρ π W`: the subspace `W` is stable under every `ρ(k)` and every `π(X)`.
  These are exactly the subspaces that `IsIrreducibleGKModule` quantifies over.
* `IsMaximallyFaithfulModulo π R`: every `u ∈ U(L)` with `u · v ∈ R` for all `v ∈ V` lies in
  `Ideal.span {z ∈ Z(L) | z · v ∈ R for all v ∈ V}`. Here `u · v` is
  `envelopingAction π u v`. When `R` is `π`-stable, the elements `u` with `u · V ⊆ R` form
  the annihilator of the quotient module `V / R`. So the condition is Kostant's maximal
  faithfulness (`IsMaximallyFaithful`, Kostant 1978, §3.9, p. 142) for `V / R`, stated
  without forming the quotient. The definition makes sense for any subspace `R`, but this
  module only applies it to `(𝔤, K)`-submodules.
  `isMaximallyFaithfulModulo_bot_iff` proves that the condition for `R = ⊥` is
  `IsMaximallyFaithful π`.

## Lemmas proved here

* `envelopingAction_intertwine`: if a linear map `B : X → V` satisfies
  `B(σ(Y) f) = π(Y) B(f)` for all `Y ∈ L`, then `B(u · f) = u · B(f)` for every `u ∈ U(L)`.
  The proof writes `u` as the image of a tensor and inducts on the tensor algebra (scalars,
  generators, products, sums).
* `isMaximallyFaithfulModulo_ker_iff`: if such a `B` is also onto, then
  `IsMaximallyFaithfulModulo σ (ker B) ↔ IsMaximallyFaithful π`. Indeed, `u · X ⊆ ker B`
  holds iff `u · B(X) = 0` holds, by the previous lemma, and `B(X) = V`. So the two conditions
  are about the same elements `u` and the same central elements `z`.
* For `B` with `IsRealStandardIntertwiner n ρ π ds B`:
  * `map_realStandardRep`: `B(realStandardRep n ds k f) = ρ(k) B(f)` for `k ∈ O(n)`;
  * `map_realStandardLie`: `B(realStandardLie n ds Y f) = π(Y) B(f)` for every
    `Y ∈ ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)`. This follows from the real directions `1 ⊗ X` by `ℂ`-linearity,
    using `c ⊗ X = c · (1 ⊗ X)`;
  * `isGKSubmodule_ker`: `ker B` is a `(𝔤, K)`-submodule of `I(ds)`;
  * `isGKSubmodule_map`: `B` maps `(𝔤, K)`-submodules of `I(ds)` to `(𝔤, K)`-submodules of
    `(ρ, π)`;
  * `surjective`: if `(ρ, π)` is irreducible and `B ≠ 0`, then `B` is onto, since its image
    is a nonzero `(𝔤, K)`-submodule.

## The two statements

1. `RealStandardLanglandsQuotientStatement` (L). Let `ds` be a list of real blocks with
   `realRank ds = n` and `IsRealLanglandsOrdered ds`. Then `I(ds)` has a largest proper
   `(𝔤, K)`-submodule. That is, there is a `(𝔤, K)`-submodule `R ≠ ⊤` that contains every
   `(𝔤, K)`-submodule `W ≠ ⊤`. The quotient `I(ds) / R` is the Langlands quotient.

   Sources:
   * Badulescu–Renard 2010, Theorem 3.3(i) (printed pp. 1124–1125), for Harish-Chandra
     modules of `GL_n(ℝ)` (their §2 conventions). If `d = (d_1, …, d_l)` are essentially
     square-integrable representations written in standard order, `e(d_1) ≥ … ≥ e(d_l)`,
     then `λ(d) = d_1 × … × d_l` "has a unique irreducible quotient `Lg(d)`, appearing with
     multiplicity one in a Jordan–Hölder sequence of `λ(d)`".
   * Knapp 1994, Theorem 1(a) (p. 400): under (2.5), `I(σ_1, …, σ_r)` has a unique
     irreducible quotient `J(σ_1, …, σ_r)`.

   From the source to statement L: `λ(d)` has finite length (it has a Jordan–Hölder
   sequence). So every proper submodule lies in a maximal proper submodule `M`. Then `λ(d)/M`
   is an irreducible quotient, so `λ(d)/M ≅ Lg(d)`. Suppose there were two different maximal
   submodules `M_1` and `M_2`. Then `M_1 + M_2 = λ(d)`, so
   `λ(d)/(M_1 ∩ M_2) ≅ λ(d)/M_1 × λ(d)/M_2 ≅ Lg(d) × Lg(d)`. This would make `Lg(d)` occur
   twice in a Jordan–Hölder sequence, which contradicts multiplicity one. So there is exactly
   one maximal proper submodule `R`, and it contains every proper submodule. `R ≠ ⊤` because
   `λ(d) ≠ 0`.

   As with S_V itself, a proof of L must also identify the Library's
   `realStandardModule n ds`, its `O(n)`-finite part and the order `IsRealLanglandsOrdered`
   with the classical standard module, its Harish-Chandra module and the standard order. The
   Library's blocks are `RealBlock.character` (a character of `GL_1(ℝ)`) and
   `RealBlock.induced` (a block of `GL_2(ℝ)` cut out of a principal series by a Fourier
   condition).

2. `RealLargeStandardIrreducibleStatement` (V). Let `ds` be a list of real blocks with
   `realRank ds = n` and `IsRealLanglandsOrdered ds`. Let `R` be a largest proper
   `(𝔤, K)`-submodule of `I(ds)`, with exactly the three properties produced by L. If
   `IsMaximallyFaithfulModulo (realStandardLie n ds) R`, that is, if the Langlands quotient
   `I(ds) / R` is maximally faithful, then `R = ⊥`. In other words, `I(ds)` is irreducible.

   Source: Vogan 1978, Theorem 6.2 (p. 89), proof of (a) ⇒ (f) (p. 93). The theorem covers
   quasisplit linear reductive groups with abelian Cartan subgroups, not necessarily
   connected, so it includes `GL_n(ℝ)` with `K = O(n)`. In the proof, `X` is an irreducible
   large `(𝔤, K)`-module. Translation (Zuckerman periodicity and the Borho–Jantzen
   translation principle) reduces to nonsingular infinitesimal character. By the Langlands
   classification, `X` is the Langlands quotient of a standard module `Ind(δ ⊗ ν ⊗ 1)`. If that
   standard module were reducible, then by Speh–Vogan ([11] in Vogan's paper,
   "Reducibility of generalized principal series representations"), Theorems 6.15 and 6.16,
   the τ-invariant of `X` would be nonempty. This contradicts largeness. So the standard
   module is irreducible.

   From the source to statement V: the irreducible quotient `I(ds) / R` is admissible, so it
   has an infinitesimal character `ξ`. Its maximal faithfulness then says that its
   annihilator is `U(𝔤) · ker ξ`, the minimal primitive ideal. That is Vogan's "large"
   (Definition 6.1, p. 89; see `RealGenericLargeReduction.md` for the comparison of
   definitions). Vogan's conclusion is that the standard module is irreducible. Since
   `R ≠ ⊤` and `R` is a `(𝔤, K)`-submodule, this gives `R = ⊥`. Langlands data are unique
   up to permutation of blocks with equal real exponents (Knapp 1994, Theorem 1(c)). Standard
   modules for such reorderings have the same composition factors (Badulescu–Renard 2010,
   Remark 2.3 and Proposition 2.4: `π_1 × π_2 = π_2 × π_1` in the Grothendieck group). So
   irreducibility of one standard module of `X` implies irreducibility of every standard
   module of `X`, including `I(ds)`. A proof of V needs the same identification of the
   Library's standard modules as L.

## The reduction

`RealLargeLanglandsQuotientReductionStatement` is the implication L → V → S_V, and the
theorem `realLargeLanglandsQuotientReduction` proves it. The proof assumes the hypotheses of
S_V: `B ≠ 0` with `IsRealStandardIntertwiner n ρ π ds B`, an irreducible maximally faithful
`(ρ, π)`, `realRank ds = n` and `IsRealLanglandsOrdered ds`. The admissibility and
`IsRealGKModule` hypotheses of S_V are not used. The steps are:

1. `B` is onto (`IsRealStandardIntertwiner.surjective`).
2. L gives the largest proper `(𝔤, K)`-submodule `R`.
3. `ker B` is a `(𝔤, K)`-submodule, and it is proper because `B ≠ 0`. So `ker B ≤ R`.
4. The image `B(R)` is a `(𝔤, K)`-submodule of the irreducible `(ρ, π)`, so it is `⊥` or
   `⊤`. If `B(R) = ⊤`, then for every `f` there is `r ∈ R` with `B(f) = B(r)`. Then
   `f - r ∈ ker B ≤ R`, so `f ∈ R`. That would give `R = ⊤`, which is false. So `B(R) = ⊥`,
   that is, `R ≤ ker B`. Hence `R = ker B`.
5. `isMaximallyFaithfulModulo_ker_iff` (`B` is onto and intertwines `realStandardLie` with
   `π`) turns `IsMaximallyFaithful π` into `IsMaximallyFaithfulModulo (realStandardLie n ds) R`.
6. V gives `R = ⊥`. So `ker B = ⊥`, and `B` is injective.

In step 4 the identification `ker B = R` is the abstract counterpart of "`(ρ, π)` is the
Langlands quotient of `I(ds)`". The proof gets it from the maximality in L and needs no
uniqueness of Langlands data.

## Provenance

Derived. `IsGKSubmodule` is the stability condition inside the Library's
`IsIrreducibleGKModule`. `IsMaximallyFaithfulModulo` is Kostant's maximal faithfulness
(1978, §3.9, p. 142; (3.1.1)) applied to the quotient `V / R`. L is the Langlands quotient
theorem (Badulescu–Renard 2010, Theorem 3.3(i); Knapp 1994, Theorem 1(a)) in
largest-proper-submodule form, by the finite-length argument above. V is Vogan 1978,
Theorem 6.2, proof of (a) ⇒ (f), in submodule form. The split into L and V and all the
lemmas are internal to this module.

Sources:

* A. I. Badulescu and D. Renard, Unitary dual of GL(n) at archimedean places and global
  Jacquet–Langlands correspondence, Compositio Math. 146 (2010), 1115–1164
  (`badulescu-renard-2010-unitary-dual`). §2 conventions, Remark 2.3 (printed p. 1123),
  Proposition 2.4 (p. 1124), Theorem 3.3(i) (pp. 1124–1125). PDF page = printed page − 1113.
* A. W. Knapp, Local Langlands correspondence: the archimedean case, Proc. Sympos. Pure
  Math. 55, Part 2 (1994), 393–410 (`knapp-1994-archimedean-llc`). Theorem 1(a) and (c)
  with (2.5), p. 400 (PDF page 410 of the proceedings volume).
* D. A. Vogan, Gelfand–Kirillov dimension for Harish-Chandra modules, Invent. Math. 48
  (1978), 75–98. Definition 6.1 and Theorem 6.2 (p. 89), proof of (a) ⇒ (f) (p. 93),
  reference [11] (Speh–Vogan) on p. 98.
* B. Kostant, On Whittaker vectors and representation theory, Invent. Math. 48 (1978),
  101–184. §3.1, (3.1.1) (p. 130) and §3.9 (p. 142).

  Vogan and Kostant are in the registered folder
  `provided-7fc98c3cf1cf4a28ee355a474ea2850645ab4bb5a37e25028414c938744c0cdf`. Vogan PDF
  page = printed page − 74; Kostant PDF page = printed page − 100.
