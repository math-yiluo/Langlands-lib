# Statement: the rational structure of `GL_n`

Author: Worker 1220.

This module states, as one `Prop`-valued definition, the rational structure
of the general linear group `GL_n` over a field with its diagonal torus: the
diagonal torus is a maximal split torus, its relative roots are the
characters `eᵢ - eⱼ` with `i ≠ j`, it has a relative root system with its
Weyl group, and generic cocharacters have the torus centralizer as dynamic
Levi subgroup. Nothing is proved here. The declaration
`GeneralLinearRationalStatement` is in the namespace `Langlands.GroupScheme`.

## Sources

- Milne, *Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`,
  SHA-256 `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
  Printed page = PDF page − 16.
  - Example 21.6 (printed p.426, PDF p.442): for `G = GL_n` and the diagonal
    torus `T = D_n`, `X(T) = ⊕ᵢ ℤχᵢ` with `χᵢ : diag(t₁, …, tₙ) ↦ tᵢ`, and `T`
    acts on `gl_n = M_n(k)` by conjugation.
  - Example 21.36 (printed p.435, PDF p.451): "The roots of (G, T) are the
    characters χᵢ − χⱼ, i ≠ j (see 21.6)."
  - Example 21.40 (printed p.436, PDF p.452): "The centralizer of T in G is
    T", the permutation matrices normalize `T`, and `W(G, T) ≃ Sₙ`.
  - 25.13 (printed p.548, PDF p.564): the relative roots of `(G, S)` for a
    maximal split torus `S` are the characters `α ≠ 0` of `S` with
    `g_α ≠ 0` for the adjoint action of `S` on `g`.
  - 25.16–25.17 (printed p.549, PDF p.565): `(ₖV, ₖΦ)` is a root system,
    possibly nonreduced, and `N_G(S)/C_G(S)` is canonically isomorphic to its
    Weyl group.
  - 25.6 (printed pp.545–546, PDF pp.561–562): the proof chooses a cocharacter
    `λ` of `S` with `C_G(S) = C_G(λ(𝔾ₘ))`.
- Borel and Tits, *Groupes réductifs* (1965), source ID
  `borel-tits-1965-groupes-reductifs`, SHA-256
  `ec6674ba292deaadd77a449f4bad3750db79c0b87b117a892ef6b09bb16357ad`.
  Printed page = PDF page + 53.
  - 5.1 (printed p.95, PDF p.42) and 5.8 (printed p.98, PDF p.45): the
    `k`-roots and the relative root system.
  - 4.15 a) (printed pp.90–91, PDF pp.37–38): `Z(S)` is a Levi subgroup of
    `G_{Φ⁺}`.

## The objects used

Throughout, `k : Type u` is a field and `S = Spec (CommRingCat.of k)`.

- `GeneralLinear.diagonalTorus n (CommRingCat.of k)` (module
  `Langlands.GroupScheme.Reductive.RootDatum`) is the diagonal torus
  `D_n ⟶ GL_n`, a homomorphism from the split torus
  `splitTorus.commGroupScheme S (ULift.{u} n)` to the published
  `GeneralLinear.groupScheme n (CommRingCat.of k)`. On points it sends a family
  `(tᵢ)` of units to `diag(tᵢ)`. The same module supplies the instances
  `Mono (diagonalTorus n R).hom.hom.left` and
  `IsAffineHom (groupScheme n (CommRingCat.of k)).X.hom` needed by the
  definitions below.
- `IsMaximalSplitTorus` is from `Langlands.GroupScheme.Rational.SplitTorus`.
- `relativeRoots`, `IsGenericCocharacter` and `torusCentralizer` are from
  `Langlands.GroupScheme.Rational.RelativeRoots` and
  `Langlands.GroupScheme.Rational.TorusCentralizer`.
- `HasRelativeRootSystem` is the predicate of
  `Langlands.GroupScheme.Rational.Statement`: on
  `V = relativeRootSpan i` there are a finite index type and a crystallographic
  Mathlib root system with the evaluation pairing, whose roots are the images
  `1 ⊗ α` of the relative roots, and whose Weyl group has image in `GL(V)`
  equal to the range of the injective `relativeWeylAction i`.
- `splitTorus.characterLatticeEquiv k I` (module
  `Langlands.GroupScheme.Torus.Lattice`) is the isomorphism
  `X*(𝔾ₘ^I) ≃ ℤ^I` sending a character to its exponent vector.
- `Dynamic.centralizer` (module `Langlands.GroupScheme.Dynamic.Basic`) is the
  published dynamic Levi subgroup functor of a cocharacter of `G`.

## The statement

`GeneralLinearRationalStatement : Prop` says: for every field `k : Type u`
and every `n : Type` with `Fintype n` and `DecidableEq n`, writing
`i = GeneralLinear.diagonalTorus n (CommRingCat.of k)`,

1. `IsMaximalSplitTorus i`;
2. `relativeRoots i` is the set of characters `χ` for which there are
   `a b : n` with `a ≠ b` and
   `splitTorus.characterLatticeEquiv k (ULift.{u} n) χ =
   Pi.single (ULift.up a) 1 - Pi.single (ULift.up b) 1`, that is,
   `χ = e_a - e_b`;
3. `HasRelativeRootSystem i`;
4. for every cocharacter
   `ν : cocharacterLattice (splitTorus.commGroupScheme S (ULift.{u} n))` with
   `IsGenericCocharacter i ν`,
   `Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) = torusCentralizer i`.

## Correspondence with the sources

- **Scope.** Parts 3 and 4 are the conclusions of
  `RelativeRootSystemStatement` and `GenericCentralizerStatement` (module
  `Langlands.GroupScheme.Rational.Statement`) for the diagonal torus of
  `GL_n`, as the task requires. The statement does not assume that `GL_n` is
  connected reductive and does not use those general statements; it asserts
  their conclusions for `GL_n` directly.
- **Maximality and relative roots.** `GL_n` is split and `D_n` is a split
  maximal torus. A split torus containing a maximal torus equals it, so `D_n`
  is a maximal split torus, and the relative roots of `(GL_n, D_n)` in the
  sense of Milne 25.13 are its roots in the sense of Milne 21.6. These are the
  characters `χᵢ − χⱼ`, `i ≠ j`, by Milne 21.36. Part 2 writes `χᵢ` as the
  exponent vector `Pi.single i 1` under `characterLatticeEquiv`. The
  specialization of the relative theory to the split group `GL_n` is derived.
- **Root system and Weyl group.** For `GL_n` the relative root system is the
  root system of type `A_{n-1}` on the span of the `eᵢ − eⱼ`, which is reduced,
  and the relative Weyl group `N(k)/Z(k)` is the symmetric group acting by
  permuting the coordinates (Milne 21.40). Part 3 asserts this in the form of
  `HasRelativeRootSystem`; the root system itself is not named in the
  statement.
- **Generic centralizers.** For `GL_n`, the centralizer of a cocharacter
  `t ↦ diag(t^{ν₁}, …, t^{νₙ})` is the block-diagonal subgroup for the
  partition of the indices by the values `νᵢ`, and it is the diagonal torus
  exactly when the `νᵢ` are pairwise distinct, that is, when
  `⟨eᵢ − eⱼ, ν⟩ = νᵢ − νⱼ ≠ 0` for all `i ≠ j`. Part 4 is the case of
  Borel–Tits 4.15 a) and Milne 25.6 recorded in
  `GenericCentralizerStatement`, stated as an equality of subgroup functors.

## Lean conventions

- The index type `n` lives in `Type` because the published
  `GeneralLinear.groupScheme n R` takes `n : Type`. The split torus of the
  diagonal torus is indexed by `ULift.{u} n`, so that it is a group scheme in
  universe `u`; accordingly part 2 uses `ULift.up a` and `ULift.up b`.
- The cocharacter is named `ν` rather than `λ` because `λ` is a Lean keyword.
