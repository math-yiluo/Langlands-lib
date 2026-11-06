# Maximality of dynamic parabolics of regular cocharacters (conditional on structure inputs)

Module `Langlands.GroupScheme.Absolute.RegularCocharacterMaximal`. It is derived
infrastructure for the maximality part of clause 1 of
`Langlands.GroupScheme.RegularCocharacterBorelStatement` (task
`618cd683-cfcd-43a3-b4bf-6c8abd208b1f`).

Let `G` be a smooth affine group over a field `k`, `j : T ⟶ G` a homomorphism from a split
torus whose roots are stable under negation, and `ν` a cocharacter of `T`. Let `i : B ⟶ G`
represent the dynamic parabolic `P(ν ≫ j)`. The main theorem says: if `B` maps by `f` into
a smooth connected closed subgroup `B'` of `G` compatibly with the inclusions, and the image
of `Lie(B')` never meets both `𝔤_α` and `𝔤_{-α}` nontrivially, then `f` is an isomorphism.
The hypotheses on `B'` do not include solvability. Solvability enters only through the
rank-one obstruction, which this module takes as the hypothesis `hobs` and does not prove.

## Structural inputs

The main theorem takes the following published statements as explicit hypotheses and does not
prove them:

- `hLie : DynamicLieStatement` (Conrad–Gabber–Prasad, *Pseudo-reductive groups*, 2nd ed.
  (2015), Proposition 2.1.8(1), printed p.53).
- `hSm : DynamicSmoothStatement` (CGP 2.1.8(3)).
- `hEq : LieSubgroupEqualityStatement` (Milne, *Algebraic Groups* (2017), Proposition 10.15,
  printed p.190).

The root-symmetry theorem takes `RelativeRootNegationStatement` as its hypothesis `hNeg`. The
rank-one obstruction for `B'` is the explicit hypothesis `hobs` of the main theorem; it has
the form of the conclusion of the statement in task `a638de3b-f51a-4539-b985-72fc0acb694c`
(`RankOneSolvableObstructionStatement`) applied to `B'`. None of these hypotheses is a premise
of any target statement. A final proof of the target supplies them from Library proofs once
those are published.

## Contents

Notation: for `i : H ⟶ G`, `Lie.targetMapLinear i k : Lie(H) → Lie(G)` is the induced linear
map on Lie kernels, and "the image of `Lie(H)`" means the set of `X` in `Lie(G)` with
`Y.val ≫ i.hom.hom = X.toMul.val` for some `Y : lieKernel H k`. Write `⟨α, ν⟩` for
`latticePairing T α ν`.

### Weight vectors along homomorphisms

These hold over any base ring `R`, for affine `H` and `G`.

- `lieKernelMapLinear_targetMapLinear`: for `h : H ⟶ G` and an `R`-algebra map `φ : A → B`,
  pushing a Lie-kernel element along `h` commutes with change of test algebra along `φ`.
- `adjoint_comp_targetMapLinear`: `Ad(h ∘ g)(dh X) = dh(Ad(g) X)` for every `A`-point `g` of
  `H` and `X` in the Lie kernel of `H` over `A`.
- `targetMapLinear_mem_weightSpace`: for `f : T ⟶ H` and `h : H ⟶ G`, the map
  `Lie.targetMapLinear h R` sends `weightSpace f χ` into `weightSpace (f ≫ h) χ`. The proof
  applies `dh` to the defining identity of a weight vector over every test algebra and uses
  the two lemmas above.

### Root symmetry from relative-root negation

- `neg_mem_roots_of_relativeRootNegation`: assume `hNeg : RelativeRootNegationStatement`. For a
  connected reductive `G` over a field and a maximal torus `j : T ⟶ G` with `T` split,
  `α ∈ roots j` implies `-α ∈ roots j`. The proof notes that `j` is a maximal split torus
  (`IsMaximalTorus.isMaximalSplitTorus`) and that `relativeRoots j = roots j`
  (`relativeRoots_eq_roots`, true by definition), and applies `hNeg`.

### Lie algebras of subgroups containing `P(ν)`

- `targetMapLinear_mem_nonnegativeWeightSpan`. Take `T` split, `H` affine and locally of
  finite type, `i : H ⟶ G`, `f : T ⟶ H` and a cocharacter `ν`. Assume three things:
  1. the roots of `f ≫ i` are stable under negation;
  2. every weight space `weightSpace (f ≫ i) α` with `⟨α, ν⟩ > 0` lies in the image of
     `Lie(H)`;
  3. for no root `α` do both `weightSpace (f ≫ i) α` and `weightSpace (f ≫ i) (-α)`
     contain a nonzero element of the image of `Lie(H)`.

  Then every `Y` in `Lie(H)` maps into `nonnegativeWeightSpan (f ≫ i) ν`. Proof: by
  `isInternal_weightSpace_of_isSplitTorus`, `Lie(H)` is the sum of the weight spaces
  `weightSpace f χ`, so it suffices to treat `Y ∈ weightSpace f χ`. Its image lies in
  `weightSpace (f ≫ i) χ`. If `⟨χ, ν⟩ ≥ 0`, this space is part of the nonnegative span. If
  `⟨χ, ν⟩ < 0` and the image of `Y` is nonzero, then `χ ≠ 0` and `χ` is a root, so `-χ` is a
  root. Then `weightSpace (f ≫ i) (-χ)` contains a nonzero vector, and that vector lies in the
  image of `Lie(H)` by assumption 2, since `⟨-χ, ν⟩ > 0`. This contradicts assumption 3.
- `exists_lieKernel_of_mem_nonnegativeWeightSpan`: assume `hLie`. Let `G` be affine and
  locally of finite type, `T` split, `j : T ⟶ G`, `ν` a cocharacter of `T`, and `i : B ⟶ G` a
  homomorphism representing `Dynamic.parabolic (groupHom ν ≫ j)`. Then every element of
  `nonnegativeWeightSpan j ν` lies in the image of `Lie(B)`. Proof: by `hLie`, an element `X`
  of `Lie(G)` is a `k[ε]`-point of `P(ν ≫ j)` exactly when it lies in the sum over `n : ℕ`
  of the weight spaces of `t ↦ tⁿ` for `ν ≫ j`. By
  `iSup_nat_weightSpace_cocharacter_eq_nonnegativeWeightSpan` this sum is
  `nonnegativeWeightSpan j ν`. So `X` is a `k[ε]`-point of `B`. That point reduces to the
  identity, because its image in `G` does and `i` is a monomorphism (`mem_lieKernel_of_comp`).
- `isIso_of_comp_eq_of_isRepresentedBy_parabolic`. Hypotheses:
  - `hLie`, `hSm`, `hEq`;
  - `G` smooth and affine, `T` split, `j : T ⟶ G`, a cocharacter `ν`, and roots of `j` stable
    under negation (`hneg`);
  - a closed subgroup `i : B ⟶ G` representing `Dynamic.parabolic (groupHom ν ≫ j)`;
  - a smooth closed subgroup `i' : B' ⟶ G` with `B'.X.left` connected, and `f : B ⟶ B'`
    with `f ≫ i' = i`;
  - the rank-one obstruction `hobs` for the image of `Lie(B')` and the roots of `j`.

  Conclusion: `IsIso f`. Proof:
  1. `B` is smooth by `hSm`, and `f` is a closed immersion because `f ≫ i'` is one.
  2. `T` factors through `B`, by `range_le_centralizer_groupHom_comp` and
     `Dynamic.centralizer_le_parabolic`.
  3. By `exists_lieKernel_of_mem_nonnegativeWeightSpan`, every element of
     `nonnegativeWeightSpan j ν` lies in the image of `Lie(B)`. Hence the image of
     `Lie(B')` contains every `𝔤_α` with `⟨α, ν⟩ > 0`.
  4. The previous theorem, applied to `H = B'`, places the image of `Lie(B')` inside
     `nonnegativeWeightSpan j ν`, hence inside the image of `Lie(B)`. Because `i'` is a
     monomorphism, `Lie(B) → Lie(B')` is therefore surjective.
  5. `hEq` gives `SubgroupFunctor.range f = ⊤`.
  6. Then `range i' ≤ range i`, so `i'` factors through `i`
     (`SubgroupFunctor.IsRepresentedBy.liftOfLE`). The factorization is inverse to `f`
     because `i` and `i'` are monomorphisms.

## Provenance

The main theorem is the maximality step in the proof of Milne, *Algebraic Groups* (2017),
Proposition 21.29 (statement printed p.433, PDF p.449; proof printed p.434, PDF p.450). Milne
argues: `P(ν)` lies in a Borel subgroup `B`; `Lie(B)` contains `Lie P(ν) = 𝔱 ⊕ ⨁_{⟨α,ν⟩>0} 𝔤_α`;
by Lemma 21.28 (printed p.433), `Lie(B)` contains exactly one of `𝔤_α`, `𝔤_{-α}` for each
root `α`, so `Lie(B) = Lie P(ν)`, and `B = P(ν)` by 10.15.

The Lean proof follows this route with these changes:

- `B'` is any smooth connected closed subgroup containing `P(ν)` that satisfies the rank-one
  obstruction, not only a Borel subgroup. The obstruction is a hypothesis in nonzero-vector
  form: it forbids `Lie(B')` from meeting both `𝔤_α` and `𝔤_{-α}` nontrivially, and does not
  say that `Lie(B')` contains a whole root space.
- `Lie P(ν)` is described by CGP 2.1.8(1) (`hLie`) as the nonnegative weight span. Its
  zero-weight part is `weightSpace j 0`, not `Lie T`, so the proof needs no centralizer
  computation `Z(ν) = T`.
- The weight decomposition of `Lie(B')` for the split torus replaces Milne's direct-sum
  description of `Lie(B)`.
- Root symmetry, part of Milne's root datum, is a hypothesis (`hneg`) of the main theorem;
  `neg_mem_roots_of_relativeRootNegation` derives it from `RelativeRootNegationStatement`.
- Milne 10.15 enters as `hEq`, applied to the closed immersion `f`.
