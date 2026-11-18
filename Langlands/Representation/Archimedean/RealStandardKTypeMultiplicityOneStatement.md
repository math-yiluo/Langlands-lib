# A multiplicity-one `O(n)`-type in every real standard module

Module `Langlands.Representation.Archimedean.RealStandardKTypeMultiplicityOneStatement`,
namespace `Langlands.Archimedean`. It is a statement module and contains no proof.

## The statement

`RealStandardKTypeMultiplicityOneStatement : Prop` asserts the following. Let `n : ℕ`, and let
`ds : List RealBlock` have total rank `realRank ds = n`. Then there exist `d : ℕ` and a monoid
homomorphism `τ : O(n) → Matrix (Fin d) (Fin d) ℂ` with these properties:

* `τ` is continuous, and `0 < d`;
* `τ` is irreducible: the only subspaces of `ℂ^d` stable under every `τ k` are `0` and `ℂ^d`;
* the complex vector space `gkIntertwiners (realStandardRep n ds) d τ` has dimension exactly
  `1`. This space consists of the linear maps `T : ℂ^d → V` with `T (τ k x) = ρ k (T x)`, where
  `V` is the space of `O(n)`-finite functions of the real standard module
  `realStandardModule n ds` and `ρ = realStandardRep n ds` is the action of `O(n)` on it.

Here `O(n)` is `Matrix.unitaryGroup (Fin n) ℝ`. In words: some irreducible continuous
representation of `O(n)` occurs in the real standard module of `ds` with multiplicity exactly
one.

The order of the blocks in `ds` is arbitrary, and the exponents are arbitrary complex numbers.

## Source

David A. Vogan, Jr., *Representations of Real Reductive Lie Groups*, Progress in Mathematics 15,
Birkhäuser, 1981 (registered literature source `vogan-1981-representations-real-reductive`).
The book is scanned with two printed pages per PDF page; PDF page `q` carries printed pages
`2q − 18` and `2q − 17`. The free-text note stored with the source registration gives
pp. 418–419 for Theorem 6.6.15. The correct pages are 420–421, as stated below.

* Theorem 6.5.9(b), p. 400 (PDF p. 209): let `X(𝔮, δ ⊗ ν)` be the standard representation
  attached to a set of `θ`-stable data (Definition 6.5.2). Its lambda-lowest `K`-types
  (Definition 5.4.1) form the set `A(𝔮, δ)`, and these `K`-types occur in `X(𝔮, δ ⊗ ν)` with
  multiplicity one. The continuous parameter `ν` is arbitrary.
* Notational Convention 6.6.3, pp. 412–413 (PDF p. 215): through the bijection (6.6.2) between
  sets of `θ`-stable data and sets of character data `(H, γ)`, `X(γ)` denotes the standard
  representation `X(𝔮, H, δ, ν)`, and `A(γ)` denotes its set of lowest `K`-types `A(𝔮, δ)`.
* Definition 6.6.11, p. 418 (PDF p. 218): let `H = TA` be a `θ`-stable Cartan subgroup of `G`,
  and let `MA = G^A` be the Langlands decomposition of the centralizer of `A` in `G`. A set of
  cuspidal data for `G` is a triple `(MA, δ, ν)` with `δ` a **discrete series** representation of
  `M` and `ν ∈ Â`. Limits of discrete series are not allowed.
* Lemma 6.6.12, pp. 418–419 (PDF p. 218): there is a surjective map from sets of character data
  for `G` to sets of cuspidal data for `G`, given by `MA = G^A`, `ν = Γ|_A` and
  `δ = X_M(γ|_T)`. It is bijective on `K`-conjugacy classes. So every set of cuspidal data comes
  from some set of character data.
* Theorem 6.6.14 (Langlands), pp. 419–420 (PDF pp. 218–219): let `(MA, δ, ν)` be a set of
  cuspidal data. Let `P¹ = M¹A¹N¹` be the parabolic subgroup defined by `−Re ν`, and let `δ¹`
  be the associated tempered representation of `M¹` (Definition 6.6.13). The theorem
  considers `π(δ ⊗ ν) = Ind_{P¹}^G δ¹ ⊗ ν¹ ⊗ 1 = Ind_P^G δ ⊗ ν ⊗ 1`, where `P = MA(ÑN¹)`,
  together with its Langlands subrepresentations. (The theorem's printed cross-reference for
  cuspidal data is "Definition 6.6.10"; the definition is printed as 6.6.11.)
* Theorem 6.6.15, pp. 420–421 (PDF p. 219): let `(H, γ)` be a set of character data and
  `(MA, δ, ν)` the corresponding set of cuspidal data. Write `X(δ ⊗ ν)` for the Harish-Chandra
  module of the representation `π(δ ⊗ ν)` of Theorem 6.6.14. Then `X(δ ⊗ ν) ≅ X(γ)`: real
  parabolic induction and `θ`-stable cohomological parabolic induction coincide. The printed
  cross-references in this theorem read "Lemma 6.6.11" and "Theorem 6.6.13". The results meant
  are Lemma 6.6.12 (the map from character data) and Theorem 6.6.14 (the induced
  representations), as printed above.

## Relation to the Lean statement

Take `G = GL_n(ℝ)` and `K = O(n)`. The cuspidal parabolic subgroups of `G` are the block upper
triangular subgroups with blocks of size `1` and `2`. For such a subgroup, the group `M` is a
product of copies of `{±1}`, one for each `1`-block, and of `SL^±(2, ℝ)`, one for each `2`-block.
A discrete series `δ` of `M` is a sign character on each `1`-block and a discrete series of
`SL^±(2, ℝ)`, of lowest `SO(2)`-weight at least `2`, on each `2`-block.

The Library's `realStandardModule n ds` (module `StandardModule`) is a space of functions in the
principal series of the position characters `realPositionCharacter ds`:

* A block `.character d` occupies one position, with the character of `d`.
* A block `.induced d` of weight `m` and exponent `t` occupies two positions, with the characters
  `sgn^{|m|+1} |·|^{t + |m|/2}` and `|·|^{t − |m|/2}`. The rotations in the coordinates of this
  block therefore act with `SO(2)`-weights `k ≡ |m| + 1 (mod 2)`. The Fourier coefficients of
  weight `|k| < |m|` along these rotations must vanish.

There are two kinds of `2`-blocks.

* If `|m| ≥ 1`, the surviving weights are `|k| ≥ |m| + 1` with `k ≡ |m| + 1 (mod 2)`. The block
  representation is the discrete series of `GL_2(ℝ)` of lowest weight `|m| + 1 ≥ 2`, twisted by
  `|det|^t`. Its restriction to `SL^±(2, ℝ)` is a genuine discrete series.
* If `m = 0`, the cutoff is vacuous. The block representation is the whole principal series of
  `GL_2(ℝ)` of the characters `sgn · |·|^t` and `|·|^t`. By induction in stages, the block
  amounts to two `1`-blocks with these characters.

So `realStandardModule n ds` realizes `Ind_{P'}^G δ ⊗ ν ⊗ 1`. Here `P'` is the block upper
triangular parabolic subgroup with the blocks of `ds` in their order, each weight-`0` block
being split into two `1`-blocks. The triple `(MA, δ, ν)` is a set of cuspidal data in the sense
of Definition 6.6.11: `δ` is a sign character on each `1`-position and a genuine discrete series
on each `2`-block of nonzero weight, and `ν` records the exponents.

The restriction to `O(n)` of an induced representation depends only on the restriction of the
inducing data to `O(n) ∩ M`. This is the compact picture:
`Ind_P^G(σ)|_K ≅ Ind_{K ∩ M}^K(σ|_{K ∩ M})` for every parabolic subgroup `P` with Levi factor
`MA`. It does not depend on the order of the blocks, that is on the choice of `P`, or on the
exponents. So the `O(n)`-type multiplicities of `realStandardModule n ds` equal those of
`π(δ ⊗ ν) = Ind_P^G δ ⊗ ν ⊗ 1` for the parabolic subgroup `P = MA(ÑN¹)` of Theorem 6.6.14.
By Lemma 6.6.12, `(MA, δ, ν)` corresponds to some set of character data `(H, γ)`. By
Theorem 6.6.15, `X(δ ⊗ ν) ≅ X(γ)`, the `θ`-stable standard representation of Notational
Convention 6.6.3. By Theorem 6.5.9(b), every lowest `O(n)`-type of `X(γ)` occurs in it exactly
once. The Lean statement keeps only this consequence: some irreducible `O(n)`-type has
multiplicity one. It does not formalize Vogan's notion of lowest `K`-type, and the
identification above is background, not part of the Lean statement.

## Use

The module `CuspidalArchimedeanIrreducibleReductionStatement` states that this proposition
implies `CuspidalArchimedeanStandardIrreducibleStatement`. A nonzero vector in the image of the
one-dimensional intertwiner space is mapped to a multiple of itself by every `O(n)`-equivariant
endomorphism.
