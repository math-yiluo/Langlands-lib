# The nonmultipliable relative roots and a base for them

This module is combinatorial input for the generated-subgroup argument of the proof of
Borel–Tits 1965, Théorème 7.2, in `MaximalSplitSubgroupProof`.

A root `a` of a root system is *nonmultipliable* when `2a` is not a root. Borel–Tits use that
the nonmultipliable roots `Φ'` form a reduced root system, and Théorème 7.2 starts from the
simple roots of `Φ'`. This module builds that system for the relative roots of a maximal split
torus, chooses its simple roots, and proves the properties of the simple roots that this
argument uses.

The module has two parts.

## Part A: root pairings over `ℚ` (namespace `Langlands.LinearAlgebra`)

Let `P : RootPairing ι ℚ M N`.

- `nonmultipliableIndices P` is the set of indices `j` with `P.root l ≠ 2 • P.root j` for every
  `l` (`mem_nonmultipliableIndices_iff`). Reflections permute it
  (`reflectionPerm_mem_nonmultipliableIndices_iff`).
- `nonmultipliableRootPairing P` (the entry definition) is the root pairing indexed by
  `nonmultipliableIndices P`. It has the same perfect pairing, the restricted roots and
  coroots, and the restricted reflection permutations. The `simp` lemmas
  `nonmultipliableRootPairing_root`, `_coroot`, `_pairing`, `_reflection`,
  `_reflectionPerm` and `_toLinearMap` unfold it.
- Instances: it is finite when `ι` is, and crystallographic when `P` is. When `ι` is finite and
  `P` is crystallographic it is reduced. If moreover `P` is a root system, so is it.
- `two_smul_mem_nonmultipliableIndices`: if `P` is crystallographic and
  `P.root l = 2 • P.root j`, then `l` is nonmultipliable. The proof uses Mathlib's
  `RootPairing.eq_one_or_two_of_root_eq_nsmul`, which excludes `4 • P.root j` being a root.
- `exists_nonmultipliable_smul`: for finite crystallographic `P`, every root is `t • P.root l`
  for a nonmultipliable `l` and some `t ≠ 0`, with coroot `t⁻¹ • P.coroot l`. This gives the
  spanning conditions of the root system instance.
- `isReduced_of_no_double`: a finite crystallographic root pairing over `ℚ` in which no root is
  twice another is reduced. The proof is a case analysis on the integer pairings of two
  linearly dependent roots. Their product is `4` (Mathlib's
  `coxeterWeightIn_eq_four_iff_not_linearIndependent`), and the cases `(1, 4)`, `(-1, -4)`,
  `(4, 1)` and `(-4, -1)` would make one root `±2` times the other.
- `nonmultipliableBase P f hf`: for a finite crystallographic root system `P` and an additive
  map `f : M →+ ℚ` that vanishes on no root, the base of `nonmultipliableRootPairing P` built by
  Mathlib's `RootPairing.Base.mk'` from `IsAddIndecomposable.baseOf`. Its simple roots are the
  `f`-positive nonmultipliable roots that are not sums of two `f`-positive nonmultipliable
  roots (`mem_nonmultipliableBase_support_iff`). They are `f`-positive
  (`pos_of_mem_nonmultipliableBase_support`).
- (A1) `base_nsmul_sub_nsmul`: for a base `b` of a root pairing `Q` over `ℚ`, two different
  simple roots `d ≠ e`, and natural numbers `n, m > 0`, the vector `n • d - m • e` is nonzero
  and is not a root. It is nonzero because two different simple roots are linearly
  independent. It is not a root because the coefficients of a root in the simple roots all have
  the same sign (`Base.pos_or_neg_of_sum_smul_root_mem`).
- (A2) `root_ne_two_smul_of_mem_span_int`: if `Q` is finite, crystallographic and reduced and
  has a base, then no root equals `2 • x` with `x` in the `ℤ`-span of the roots. The proof is
  Mathlib's `Base.induction_reflect`. The property is stable under negation. For a simple root
  it holds because the simple roots form a `ℤ`-basis of the root lattice
  (`Base.toWeightBasisInt`), and `1 = 2z` has no integer solution. Reflections preserve the
  `ℤ`-span of the roots.

## Part B: the relative roots (namespace `Langlands.GroupScheme.MaximalSplitSubgroup`)

Throughout, `k : Type u` is a field, `S` a commutative group scheme over `Spec k`, `G` a group
scheme over `Spec k`, and `i : S.toGrp ⟶ G`. The section `Pairing` assumes `G` affine
(`[IsAffineHom G.X.hom]`) and `S` split (`hT : IsSplitTorus S.toGrp`). It takes a root pairing
`P : RootPairing J ℚ V (Module.Dual ℚ V)` on `V = relativeRootSpan i` whose roots are the
rational images of the relative roots (`hroots`). This is the form produced by the published
`relativeRootSystem`.

- `rootChar P hT hroots r` is the relative root whose rational image is `P.root r`. It is
  defined via the published `RelativeRootCoxeter.rootIndexEquiv`. API: `rootChar_mem`,
  `toRat_rootChar`, `exists_rootChar_eq` (every relative root is a `rootChar`), and
  `rootChar_eq_iff`.
- `mem_nonmultipliableIndices_iff_rootChar`: `r` is a nonmultipliable index exactly when
  `(2 : ℤ) • rootChar r` is not a relative root.
- `rootChar_reflectionPerm_self`: `rootChar (s_r r) = -rootChar r`.
- `two_smul_two_smul_notMem` (crystallographic `P`): if `c` and `2c` are relative roots, then
  `2(2c)` is not one.
- `eq_or_eq_neg_of_nonmultipliable` (finite crystallographic `P`): two nonmultipliable relative
  roots `α, β` with `m • β = n • α` for integers `m ≠ 0` and `n` satisfy `β = α ∨ β = -α`. This
  follows from the reducedness of `nonmultipliableRootPairing P`.

From here on `i` is also assumed monic (`[Mono i.hom.hom.left]`).

- `corootFunctional_root`: the published functional
  `corootFunctional i ν` takes the value `⟨rootChar r, ν⟩` at `P.root r`.
- `rootChar_reflectionPerm` (finite root system `P`): let `ν` be any cocharacter with
  `⟨rootChar j, ν⟩ = 2` such that `c ↦ c - ⟨c, ν⟩ • rootChar j` maps relative roots to
  relative roots. Then `rootChar (s_j l) = rootChar l - ⟨rootChar l, ν⟩ • rootChar j`. Here
  `ν` need not be the coroot of `P`. The proof shows `corootFunctional i ν = P.coroot' j` with
  Mathlib's `Module.Dual.eq_of_preReflection_mapsTo`: a reflection that preserves a finite
  spanning set is determined by its root.

The section `Base` assumes `P` finite, crystallographic and a root system, and takes a generic
cocharacter `lam` (`hlam : IsGenericCocharacter i lam`, so `lam` pairs nontrivially with every
relative root).

- `simpleBase` is `nonmultipliableBase P f` for `f = corootFunctional i lam`. The hypothesis
  that `f` vanishes on no root is `corootFunctional_root_ne_zero`.
- `simpleChars` is the finite set of the characters `rootChar j` of its simple roots
  (`mem_simpleChars`, `rootChar_mem_simpleChars`). Each one is a nonmultipliable relative root
  (`simpleChars_mem`) and pairs positively with `lam` (`simpleChars_pos`).
- `nsmul_sub_nsmul_simpleChars`: for `d ≠ e` in `simpleChars` and `n, m > 0`, the character
  `n • d - m • e` is nonzero, and if it is a relative root then so is its double. If it were a
  nonmultipliable relative root it would be a root of `nonmultipliableRootPairing P`,
  contradicting (A1).
- `exists_mem_span_of_mem_closure` and `two_smul_notMem_of_mem_closure`: a relative root `c`
  in the additive subsemigroup generated by `simpleChars` is nonmultipliable. If `2c` were a
  relative root, it would be nonmultipliable by `two_smul_two_smul_notMem`. It would then be
  twice an element of the `ℤ`-span of the roots of `nonmultipliableRootPairing P`, contradicting
  (A2).
- `mem_closure_or_neg_mem_closure`: every nonmultipliable relative root or its negative lies
  in the additive submonoid generated by `simpleChars`. This is Mathlib's
  `Base.root_mem_or_neg_mem` transported to characters.
- `exists_separating_cocharacter`: for each `d₀ ∈ simpleChars` there is a cocharacter `mu` with
  `⟨d₀, mu⟩ = 0` and `⟨e, mu⟩ > 0` for the other `e ∈ simpleChars`. The rational images of the
  simple characters are linearly independent. The published
  `IsSplitTorus.exists_scaled_pairings` then gives a cocharacter whose pairings are a positive
  integer times the prescribed values `0` at `d₀` and `1` elsewhere.
- `forall_nonmultipliable_of_reflect` (Weyl closure): for each `d ∈ simpleChars` let `ν d` be a
  cocharacter with `⟨d, ν d⟩ = 2` such that `c ↦ c - ⟨c, ν d⟩ • d` maps relative roots to
  relative roots. Let `Q` be a property of characters that holds on `simpleChars`. Assume that
  for every `d ∈ simpleChars` and every nonmultipliable relative root `c`, `Q c` implies
  `Q (c - ⟨c, ν d⟩ • d)`. Then `Q` holds on every nonmultipliable relative root. The proof is
  `Base.induction_reflect` for `simpleBase`, applied to the property "`Q` holds at `rootChar t`
  and at `-rootChar t`". The reflection step uses `rootChar_reflectionPerm`, so the `ν d`
  can be any cocharacters with these two properties, for example those of the rank-one
  relations of `MaximalSplitRankOneRelation`. For a simple `d`, `Q (-d)` follows from `Q d`
  by the hypothesis at `c = d`, since `d - 2 • d = -d`.

## Main theorems

Both theorems assume `hG : IsConnectedReductive G`, `i : S.toGrp ⟶ G` and
`hi : IsMaximalSplitTorus i`. Their statements open with `haveI := hG.isAffineHom`, which
`roots i` needs. They take the root pairing from the published `relativeRootSystem` and use
`relativeRoots_eq_roots`. The cocharacter `lam` comes from the published
`IsSplitTorus.exists_genericCocharacter`.

`exists_nonmultipliableBase hG i hi`: there are `D : Finset (characterLattice S)` and
`lam : cocharacterLattice S` such that

1. every `d ∈ D` is a root with `(2 : ℤ) • d ∉ roots i`;
2. `0 < ⟨d, lam⟩` for every `d ∈ D`;
3. `⟨c, lam⟩ ≠ 0` for every `c ∈ roots i`;
4. for `d ≠ e` in `D` and natural numbers `n, m > 0`, `n • d - m • e` is nonzero and not in
   `roots i`;
5. every `c ∈ roots i` in `AddSubsemigroup.closure D` satisfies `(2 : ℤ) • c ∉ roots i`;
6. for every `d₀ ∈ D` there is a cocharacter `mu` with `⟨d₀, mu⟩ = 0` and `0 < ⟨e, mu⟩` for
   every `e ∈ D` with `e ≠ d₀`;
7. every `c ∈ roots i` with `(2 : ℤ) • c ∉ roots i` lies in `AddSubmonoid.closure D`, or its
   negative does;
8. Weyl closure: for every `ν : ∀ d ∈ D, cocharacterLattice S` with `⟨d, ν d⟩ = 2` and
   `c - ⟨c, ν d⟩ • d ∈ roots i` for all `c ∈ roots i`, and every property `Q` of characters
   that holds on `D` and satisfies `Q c → Q (c - ⟨c, ν d⟩ • d)` for every `d ∈ D` and every
   `c ∈ roots i` with `(2 : ℤ) • c ∉ roots i`, `Q c` holds for every `c ∈ roots i` with
   `(2 : ℤ) • c ∉ roots i`.

Here `D = simpleChars` and `lam` is the generic cocharacter. Clause 3 is the genericity of
`lam`; clauses 1, 2 and 5–8 are the lemmas of the section `Base`. Clause 4 combines `nsmul_sub_nsmul_simpleChars` (applied to `n, m` and to
`2n, 2m`) with `two_smul_two_smul_notMem`. If `x = n • d - m • e` were a root, then `2x` and
`2(2x) = 2n • d - 2m • e` would both be roots, which is impossible.

`nonmultipliable_eq_or_eq_neg hG i hi`: for `α, β ∈ roots i` with `(2 : ℤ) • α ∉ roots i` and
`(2 : ℤ) • β ∉ roots i`, if `m • β = n • α` for integers `m ≠ 0` and `n`, then `β = α` or
`β = -α`. This is `eq_or_eq_neg_of_nonmultipliable`.

Clause 8 has a weak hypothesis: the stability of `Q` is only assumed at nonmultipliable
relative roots `c`, not at every character.

## Scope and sources

The field is arbitrary. Nothing here uses Borel–Tits 3.22.

- Borel–Tits, *Groupes réductifs*, Publ. Math. IHÉS 27 (1965), §7, printed p.117 (PDF p.64):
  in a root system the positive integer multiples of a root `d` that are roots are `{d}` or
  `{d, 2d}`, and the set `Φ'` of nonmultipliable roots is a reduced root system. Théorème 7.2,
  on the same page, takes `Δ` to be the simple roots of `Φ'` for an order on `X*(S)`. Here `D`
  is that `Δ`, for the order defined by `lam`.
- The properties of bases used in Part A are Mathlib's (`RootPairing.Base`,
  `IsAddIndecomposable.baseOf`, `Base.induction_reflect`, `Base.toWeightBasisInt`).

Clauses 4–8 and the separating cocharacter of clause 6 are elementary consequences of these
facts, formulated for the proof of Théorème 7.2 in `MaximalSplitSubgroupProof`. Clause 4 is the hypothesis of
the published `Geometry.Building.commute_of_no_strict_root_combinations` for the roots `d` and
`-e`.
