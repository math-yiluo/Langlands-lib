# Reduction of the real generic standard-parameter statement

Worker 5066 wrote this module for Task 5975 (`3889357f-30ab-4e7b-9624-ca6d3d61208e`). The
task's target is the Library's `Langlands.Archimedean.RealGenericStandardParameterStatement`
(module `Langlands.Representation.Archimedean.GKModule`). It says that every irreducible
admissible generic `(𝔤𝔩_n(ℝ), O(n))`-module `(ρ, π)` on a complex vector space `V` has some
`ds : List RealBlock` with `HasRealStandardParameter n ρ π ds`. That is, `realRank ds = n`
and there is an injective `(𝔤, K)`-equivariant linear map from the `O(n)`-finite part of
Worker 35's standard module `realStandardModule n ds` into `V`.

This module splits the target into two statements and proves that together they imply it.
The first is the Langlands classification in quotient form. The second says that the
standard module of a generic Langlands quotient is irreducible. All declarations are in the
namespace `Langlands.Archimedean`. The Library's `RealBlock`, `realRank`, `RealCharacterData`
and `ComplexCharacterData` are in `Langlands.LocalFactor.Archimedean`.

## Definitions

### `realBlockExponent : RealBlock → ℝ`

- `realBlockExponent (.character d) = d.exponent.re`;
- `realBlockExponent (.induced d) = d.exponent.re`.

A character block `d : RealCharacterData` is the character `x ↦ sgn(x)^ε |x|^t` of
`GL_1(ℝ) = ℝ^×`, with `ε = d.parity` and `t = d.exponent`. An induction block
`d : ComplexCharacterData`, of weight `m` and exponent `t`, contributes the two positions
`p, p + 1` of the standard module, with characters `sgn^(|m|+1) |·|^(t + |m|/2)` and
`|·|^(t - |m|/2)` (`realInducedFirstCharacter`, `realInducedSecondCharacter`). For `m ≠ 0`
it is the block `D_|m| ⊗ |det|^t` of `GL_2(ℝ)` in Knapp's notation (Knapp 1994, (2.2b),
p. 400, and (3.5), p. 403). Both positions carry the character `|·|^t` up to the shift `±|m|/2`
inside the block. In both cases `t` is the exponent of the block's quasicharacter at each of
its diagonal positions, and `realBlockExponent` is its real part.

Provenance: internal, read off the Library's block conventions in
`Langlands/LocalFactor/ArchimedeanAttachment.lean` (`RealCharacterData`,
`ComplexCharacterData`) and `Langlands/Representation/Archimedean/StandardModule.lean`.

### `IsRealLanglandsOrdered (ds : List RealBlock) : Prop`

`ds.Pairwise fun x y => realBlockExponent y ≤ realBlockExponent x`. In words, if `x` comes
before `y` in `ds`, then `Re t_y ≤ Re t_x`. So the real parts of the exponents are
non-increasing along the list.

Provenance (source, with a correction). This is the dominance condition of the Langlands
classification for `GL_n(ℝ)` (Knapp 1994, Theorem 1(a), condition (2.5), p. 400). With it the
induced representation `I(σ₁, …, σ_r)` has a unique irreducible quotient `J(σ₁, …, σ_r)`. The
Library's standard module consists of functions `f` with `f(b g) = χ(b) δ_B^{1/2}(b) f(g)` for
`b` in the upper triangular Borel subgroup, under right translation. For such left-equivariant
functions, the closed positive chamber of the upper triangular parabolic subgroup `Q` is
`⟨Re ν, α⟩ ≥ 0` for the roots `α = e_i - e_j` (`i < j`) of `Q`. Here `ν` is the
diagonal parameter whose entry at each position of block `j` is `t_j`. The condition therefore
reads `Re t₁ ≥ Re t₂ ≥ ⋯ ≥ Re t_r`.

Knapp's (2.5) is printed as `n₁⁻¹ Re t₁ ≥ n₂⁻¹ Re t₂ ≥ ⋯ ≥ n_r⁻¹ Re t_r`, where `n_j ∈ {1, 2}`
is the size of block `j`. His blocks (2.2) tensor with `a ↦ |det a|^t` on the positive scalar
matrices of size `n_j`, so the per-coordinate exponent of a block of size 2 is `t`, not `t/2`.
The factors `n_j⁻¹` disagree with the chamber computation: with the trace form on
`𝔞 = {(h₁, h₂ 1₂)}` of the Levi subgroup `GL₁ × GL₂`, the root `e₁ - e₂` pairs with the
parameter of `(|·|^{t₁}, D ⊗ |det|^{t₂})` as `t₁ - t₂`. For example, on `GL₃(ℝ)` with
`t₁ = 3/10` on the `GL₂` block followed by `t₂ = 2/10` on a `GL₁` block, the diagonal parameter
`(3/10, 3/10, 2/10)` is dominant, but the printed (2.5) fails (`3/20 < 2/10`). This module
uses the chamber condition `Re t₁ ≥ ⋯ ≥ Re t_r`. In the Library's left-equivariant
realization, this is the order in which the Langlands quotient is a quotient. For the reverse
order on `GL₂(ℝ)`, `Ind(|·|^{-1/2}, |·|^{1/2})` has the trivial representation as a
subrepresentation and the discrete series as a quotient.

### `IsRealStandardIntertwiner n ρ π ds B : Prop`

Here `ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V`,
`π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V`, `ds : List RealBlock` and
`B : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ] V`. The predicate is
the conjunction of:

1. for every `k ∈ unitaryCompact ℝ n` and every `f`, the right translate
   `Whittaker.rightTranslation ℂ (GeneralLinear n ℝ) k f` is again in
   `kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)` (bundled as `∃ hf`), and
   `B ⟨R(k) f, hf⟩ = ρ ⟨(k : Matrix), k.2⟩ (B f)`;
2. for every real matrix `X` and every `f`, the right derivative
   `rightDerivative (matrixModel ℝ n) X f` is again in that space (bundled as `∃ hf`), and
   `B ⟨R(X) f, hf⟩ = π (1 ⊗ₜ X) (B f)`.

Provenance: internal. These are verbatim the last two clauses of the Library's
`HasRealStandardParameter`, whose Markdown (`GKModule.md`) explains them.
`hasRealStandardParameter_iff` records that `HasRealStandardParameter n ρ π ds` is,
definitionally, `realRank ds = n ∧ ∃ A, Function.Injective A ∧ IsRealStandardIntertwiner n ρ π
ds A`.

## Statements

### `RealLanglandsQuotientStatement.{uV}`

For every `n : ℕ`, every complex vector space `V : Type uV` and every `ρ`, `π` with
`IsRealGKModule n ρ π`, `IsIrreducibleGKModule ρ π` and `IsAdmissibleGKModule ρ`, there are
`ds : List RealBlock` and `B` such that:

- `realRank ds = n`;
- `IsRealLanglandsOrdered ds`;
- `B : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ] V` with `B ≠ 0`;
- `IsRealStandardIntertwiner n ρ π ds B`.

Because `V` is irreducible and the image of an intertwiner is stable under `ρ` and `π`, the
map `B` is onto. So `V` is a quotient of the `O(n)`-finite part of the standard module.

Provenance (source). This is Knapp 1994, Theorem 1(a)–(b), p. 400 (`knapp-1994-archimedean-llc`),
with the order condition corrected as above. Every irreducible admissible representation of
`GL_n(ℝ)` is infinitesimally equivalent to the unique irreducible quotient
`J(σ₁, …, σ_r)` of some `I(σ₁, …, σ_r)` whose parameters satisfy the dominance condition. Here
it is stated for algebraic `(𝔤, K)`-modules in the sense of `GKModule` and the Library's
realization of `I(σ₁, …, σ_r)` as `realStandardModule`. A proof must also show that
`realStandardModule n ds` and its `O(n)`-finite part are the classical induced representation
and its Harish-Chandra module. For an induction block of weight `m ≠ 0`, the vanishing of the
Fourier coefficients of weight `|k| < |m|` along the rotations in the block's coordinates cuts
out, at every point, the discrete series `D_|m|` inside the principal series of `GL₂(ℝ)` on
that block. So the standard module is `I(σ₁, …, σ_r)` induced in stages. The statement
does not need genericity.

### `RealGenericLanglandsQuotientInjectiveStatement.{uV}`

For every `n : ℕ`, every complex vector space `V : Type uV`, every `ρ`, `π`, every
`ds : List RealBlock` and every
`B : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ] V`, assume:

- `IsRealGKModule n ρ π`, `IsIrreducibleGKModule ρ π`, `IsAdmissibleGKModule ρ` and
  `IsRealGenericGKModule n π`;
- `realRank ds = n` and `IsRealLanglandsOrdered ds`;
- `B ≠ 0` and `IsRealStandardIntertwiner n ρ π ds B`.

Then `B` is injective.

Provenance (derived). As above, `B` is onto, so `V` is the Langlands quotient of the
standard module of `ds`. The statement says that this standard module is irreducible when its
Langlands quotient is generic. For real groups this is Vogan's theorem: if `J(ν, σ)` is
generic, then `I(ν, σ)` is irreducible. Casselman–Shahidi 1998 report it on p. 562
(`casselman-shahidi-1998-standard-modules-generic`), citing D. Vogan, *Gelfand–Kirillov
dimension for Harish-Chandra modules*, Invent. Math. 48 (1978), 75–98. That paper is not
registered.

Casselman–Shahidi's report concerns genericity in the sense of continuous Whittaker
functionals. Genericity here is the algebraic form `IsRealGenericGKModule`: a nonzero
functional on the `K`-finite vectors, with no continuity. Getting from it to genericity of the
representation (a continuous Whittaker functional) is a separate step, attributed to Kostant
(1978) and Matumoto (1987). Those papers are not registered, and this step is not verified
here; see `GKModule.md`. So the statement combines two inputs: Vogan's theorem as reported by
Casselman–Shahidi, and this unverified passage from algebraic to continuous genericity.

Ties `Re t_x = Re t_y` are allowed. Blocks with equal real exponents together form an
irreducible tempered representation twisted by a positive character: unitary induction from
discrete series is irreducible for `GL_n(ℝ)`. So the standard module of a Langlands-ordered
list is still a standard module `I(ν, σ)` with `σ` tempered and `ν` strictly dominant for a
coarser parabolic subgroup. The standard modules of generic representations are Jacquet's
generic induced representations (Jacquet 2009, `jacquet-2009-archimedean-rankin-selberg`,
pp. 3–4). His Theorem 2.1 and Remark 2.2, which the task objective names, concern
Rankin–Selberg integrals of these representations; they do not prove the irreducibility used
here.

The order hypothesis is necessary. On `GL₂(ℝ)` the list
`[.character (|·|^{-1/2}), .character (|·|^{1/2})]` is not Langlands ordered. Its standard
module `Ind(|·|^{-1/2}, |·|^{1/2})` maps onto the generic discrete series with the trivial
representation as kernel.

### `RealGenericStandardParameterReductionStatement.{uV}`

`RealLanglandsQuotientStatement.{uV} → RealGenericLanglandsQuotientInjectiveStatement.{uV} →
RealGenericStandardParameterStatement.{uV}`.

Provenance: internal; the reduction is proved in the module.

## Proofs

- `hasRealStandardParameter_iff` is `Iff.rfl`: `IsRealStandardIntertwiner` repeats the last two
  clauses of `HasRealStandardParameter`.
- `realGenericStandardParameterReduction` proves the reduction statement. Given `(ρ, π)`
  irreducible, admissible and generic, `RealLanglandsQuotientStatement` gives `ds` with
  `realRank ds = n`, `IsRealLanglandsOrdered ds` and a nonzero intertwiner `B`.
  `RealGenericLanglandsQuotientInjectiveStatement`, applied to the same data and the
  genericity hypothesis, shows that `B` is injective. Then `ds`, the rank equation, `B`, its
  injectivity and its two intertwining clauses are exactly `HasRealStandardParameter n ρ π ds`.
