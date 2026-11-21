# Irreducible real standard modules are generic

Module `Langlands.Representation.Archimedean.RealIrreducibleStandardGenericStatement`,
namespace `Langlands.Archimedean`.

## Statement

`RealIrreducibleStandardGenericStatement` is a proposition; nothing is proved in this module.
For every `n : ℕ` and every `ds : List RealBlock` with `realRank ds = n`, it assumes that the
`O(n)`-finite functions of `realStandardModule n ds`, with right translation
`realStandardRep n ds` and right derivatives `realStandardLie n ds`, form an irreducible
`(𝔤, K)`-module (`IsIrreducibleGKModule`). It concludes
`IsRealGenericGKModule n (realStandardLie n ds)`. That predicate (module
`Langlands.Representation.Archimedean.GKModule`) asks for:

- a nonzero linear functional `ℓ` on the `O(n)`-finite functions, with no continuity condition;
- real numbers `a₀, …, a_{n-1}`, where `aᵢ ≠ 0` whenever `i + 1 < n`;
- for every strictly upper triangular real matrix `X` and every vector `v`,
  `ℓ(π(1 ⊗ X) v) = (i · ∑ᵢ aᵢ X_{i,i+1}) · ℓ(v)`, where `π = realStandardLie n ds`.

The factor `i · ∑ᵢ aᵢ X_{i,i+1}` is the differential of the nondegenerate unitary character
`u ↦ exp(i ∑ᵢ aᵢ u_{i,i+1})` of the upper unipotent group `N(ℝ)`.

The rank premise `realRank ds = n` makes the block positions of `ds` match the matrix size, as in
the Library statement `RealGenericStandardUnitaryClassificationStatement`. For `n = 0` the
conclusion only asks for a nonzero functional, because the only matrix is zero; irreducibility
includes `Nontrivial`.

## Use

`RealGenericStandardUnitaryClassificationStatement` has no genericity premise. Its Markdown says
that genericity comes from the irreducible standard presentation, citing the remark after
Badulescu–Renard Theorem 8.1. This proposition records that step. A proof of it, combined with
the theorem `realGenericStandardUnitaryClassification_of_generic` of
`RealGenericStandardUnitaryClassificationOfGenericStatement` (the target with genericity as an
extra premise), proves the target:
`fun n ds hr hirr hunit => realGenericStandardUnitaryClassification_of_generic n ds hr hirr
(h n ds hr hirr) hunit`.

## Provenance

The proposition is derived; no source states it for the Library's models. It specializes the
converse half of the following theorem.

**Badulescu–Renard**, *Unitary dual of GL(n) at archimedean places and global Jacquet–Langlands
correspondence*, Compositio Math. 146 (2010), Theorem 8.1, p. 1131 (PDF p. 18,
`badulescu-renard-2010-unitary-dual`): "Any generic irreducible representation of any quasi-split
real reductive group is irreducibly induced from a generic limit of discrete series; and,
conversely, a representation which is irreducibly induced from a generic limit of discrete series
is generic." The paragraph after it says: "In the case of GL(n, R), all discrete series are
generic; so by Theorem 3.1, all essentially tempered representations are generic." The section
introduction attributes Theorem 8.1 to Vogan and Kostant [Kos78, Vog78], with "generic"
equivalent to "large".

**The Library's standard model is such an induced representation.** The Markdown of
`Langlands.Representation.Archimedean.StandardModule` (Derived choices 1, 3, 4 and 5) gives
this description.

- `realStandardModule n ds` is normalized smooth induction, from the block upper triangular
  parabolic subgroup given by the order of `ds`, of the tensor product of the blocks. A character
  block is a character of `GL₁(ℝ)`. An induced block of weight `m ≠ 0` and exponent `t` is
  `D_{|m|} ⊗ |det|^t` on `GL₂(ℝ)`, an essentially discrete series representation.
- An induced block of weight zero gives the principal series of its two characters `sgn|·|^t`
  and `|·|^t`. So it can be replaced by these two character blocks.
- The `O(n)`-finite functions are the Harish-Chandra module of this induced representation.

After the weight-zero replacement, the representation is induced from a parabolic subgroup with
Levi factor `GL₁(ℝ)^a × GL₂(ℝ)^b`. Write the Levi as `MA` with `M = {±1}^a × SL^±₂(ℝ)^b`. The
inducing representation is a discrete series representation of `M`: a character of each
`{±1}` and `D_ℓ` on each `SL^±₂(ℝ)`. It is tensored with the character of `A` given by the
exponents. Every block order defines a parabolic subgroup, and Theorem 8.1 does not require the
Langlands order. The discrete series of `GL₁(ℝ)` and `GL₂(ℝ)` are generic by the remark above.
So when the Harish-Chandra module is irreducible, the representation is irreducibly induced from
a generic discrete series, and Theorem 8.1 makes it generic.

**The algebraic form of genericity.** `IsRealGenericGKModule` asks for a Whittaker functional
on the Harish-Chandra module itself, in its full algebraic dual. Theorem 8.1 rests on two
results in the folder source `provided-7fc98c3cf1cf4a28ee355a474ea2850645ab4bb5a37e25028414c938744c0cdf`.

- Vogan, *Gelfand–Kirillov dimension for Harish-Chandra modules*, Invent. Math. 48 (1978),
  Definition 6.1 and Theorem 6.2, p. 89 (PDF p. 15). By (f) ⇒ (a), an irreducible `(𝔤, K)`-module
  infinitesimally equivalent to `Ind(δ' ⊗ ν' ⊗ 1)` is large, that is, its annihilator is the
  minimal primitive ideal. Here `δ'` is a limit of discrete series whose Harish-Chandra chamber has
  all simple roots noncompact. For `SL^±₂(ℝ)` the only root is noncompact.
- Kostant, *On Whittaker vectors and representation theory*, Invent. Math. 48 (1978),
  Theorem 6.8.1, p. 182 (PDF p. 82). For an irreducible Harish-Chandra module `V` whose
  annihilator is a minimal primitive ideal, the full dual of `Ṽ = V^{a₁} ⊕ ⋯ ⊕ V^{a_d}`
  (display (6.8.1), the twists by elements of order two) contains nonzero Whittaker vectors.
  Remark 6.7.2, p. 181 (PDF p. 81), says connectedness of `G` is not needed. From §6.2,
  pp. 168–169 (PDF pp. 68–69), the character `η` of `𝔫` is nonsingular and purely imaginary on
  the real form `𝔫₀`. As in the proof of Theorem 6.9, p. 183 (PDF p. 83), a Whittaker vector of
  `Ṽ` has a nonzero component in some `V^{aᵢ}`. That component is a Whittaker vector of `V` for
  a twisted character, which is again nonsingular and purely imaginary on `𝔫₀`.

Kostant and Vogan state these results for semisimple, respectively linear reductive, groups.
Badulescu–Renard apply them to `GL(n, ℝ)`.

**Matching the Library formula.** Let `η(X) = i ∑ᵢ bᵢ X_{i,i+1}` on real strictly upper
triangular `X`, with real `bᵢ ≠ 0`. In the dual module `X` acts on `w` by `v ↦ w(-X v)`. So a
Whittaker vector `w` with `X · w = η(X) w` satisfies `w(π(X) v) = -η(X) w(v)`. This is the
Library condition with `ℓ = w` and `aᵢ = -bᵢ`.

The same condition also follows from a continuous Whittaker functional `λ` on a smooth
globalization, with `λ(g · f) = ψ(g) λ(f)` for `g ∈ N(ℝ)` and `ψ(u) = exp(i ∑ᵢ aᵢ u_{i,i+1})`.
The `K`-finite vectors are dense, so the restriction `ℓ` of `λ` to them is nonzero. For
strictly upper triangular `X`, the superdiagonal of `exp(tX)` is `t X_{i,i+1}`. Differentiating
`λ(exp(tX) · v) = ψ(exp(tX)) λ(v)` at `t = 0` gives the Library formula.
