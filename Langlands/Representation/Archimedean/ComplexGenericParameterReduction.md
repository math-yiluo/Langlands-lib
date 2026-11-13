# Reduction of the complex generic standard-parameter statement

Worker 52 wrote this module for task `f488188c-5411-4314-bc62-8e2ff8f5c7cb` (Task 5977). The
task's target is the Library's `Langlands.Archimedean.ComplexGenericStandardParameterStatement`
(module `Langlands.Representation.Archimedean.GKModule`). It says that every irreducible
admissible generic `(𝔤𝔩_n(ℂ), U(n))`-module `(ρ, π)` has `HasComplexStandardParameter n ρ π ds`
for some `ds : List ComplexCharacterData`. This module splits the target into two statements
and proves that they imply it. All declarations are in the namespace `Langlands.Archimedean`.
The Lean names `IsComplexGKModule`, `IsIrreducibleGKModule`, `IsAdmissibleGKModule`,
`IsComplexGenericGKModule`, `HasComplexStandardParameter`, `kFiniteFunctions`,
`complexStandardModule`, `unitaryCompact`, `rightDerivative` and `matrixModel` are the
Library's; see `GKModule.md` and `StandardModule.md`.

## Definitions

### `IsComplexLanglandsOrdered ds`

For `ds : List ComplexCharacterData`, `IsComplexLanglandsOrdered ds` is
`ds.Pairwise fun d e => e.exponent.re ≤ d.exponent.re`: whenever `d` comes before `e` in the
list, `Re(e.exponent) ≤ Re(d.exponent)`. So the real parts of the exponents do not increase
along the list.

Provenance. A `ComplexCharacterData` `d` is the character
`z ↦ (z/‖z‖)^{d.weight} ‖z‖^{2 d.exponent}` of `ℂˣ` (field `character_eq`). This is Knapp's
building block `[z]^l |z|_ℂ^t` with `l = d.weight` and `t = d.exponent`
(`knapp-1994-archimedean-llc`, (4.1), p. 405; `|z|_ℂ = |z|²`). The definition is Knapp's
condition (4.3), `Re t₁ ≥ Re t₂ ≥ ⋯ ≥ Re t_n`, under which the induced representation
`I(σ₁, …, σ_n)` of (4.2) has a unique irreducible quotient (Theorem 4(a), p. 405).

The condition is the same for the Library's standard module. Knapp's `ind_B^G` is unitary
induction as in his book (Chapter VII): functions `F` with
`F(x b) = σ(b)⁻¹ δ_B(b)^{-1/2} F(x)` and `G` acting by left translation. The map
`F ↦ f`, `f(g) = F(g⁻¹)`, carries it to the functions with `f(b g) = σ(b) δ_B(b)^{1/2} f(g)`
and `G` acting by right translation. These are the functions of the Library's
`principalSeries ℂ n (complexPositionCharacter ds)` = `complexStandardModule n ds`: there
`diag(a) u ↦ ∏ᵢ χᵢ(aᵢ) |aᵢ|_ℂ^{(n-1)/2 - i}` is `σ δ_B^{1/2}` for the upper triangular Borel
subgroup. Both use the same character `σ` of the diagonal torus, so (4.3) carries over
unchanged. Jacquet uses the same order: his induced representations `I_{σ,u}` are induced
from the *lower* parabolic subgroup with `Re u₁ ≤ ⋯ ≤ Re u_r`
(`jacquet-2009-archimedean-rankin-selberg`, pp. 3–4 and Lemma 2.5, p. 9). Conjugating by the
antidiagonal permutation matrix moves the lower Borel subgroup to the upper one and reverses
the order of the characters, so for `GL_n(ℂ)` this is again non-increasing real parts for
the upper Borel subgroup. The trivial representation is a check: it is a quotient, by
`f ↦ ∫_K f(k) dk`, of the principal series with `σ = δ_B^{1/2}`. That has exponents
`tᵢ = (n-1)/2 - i`, which decrease.

### `IsComplexStandardIntertwining n ρ π ds A`

For `ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V`,
`π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V`,
`ds : List ComplexCharacterData` and a linear map
`A : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n) →ₗ[ℂ] V`,
`IsComplexStandardIntertwining n ρ π ds A` is the conjunction of:

1. for every `k : unitaryCompact ℂ n` and every `f`, the right translate
   `Whittaker.rightTranslation ℂ (GeneralLinear n ℂ) k f` is again in
   `kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)` (membership `hf`), and
   `A ⟨_, hf⟩ = ρ ⟨(k : Matrix), k.2⟩ (A f)`;
2. for every complex matrix `X` and every `f`, `rightDerivative (matrixModel ℂ n) X f` is again
   in that space (membership `hf`), and `A ⟨_, hf⟩ = π (1 ⊗ₜ X) (A f)`.

The memberships are bundled as `∃ hf`. In words, `A` is a `(𝔤, K)`-intertwining map from the
`U(n)`-finite functions of the standard module of `ds` to `(ρ, π)`, with `𝔤𝔩_n(ℂ)` acting on
functions by right derivatives along real directions.

Provenance: internal. The two clauses are verbatim the last two clauses of
`HasComplexStandardParameter`.

## Theorems

- `hasComplexStandardParameter_iff n ρ π ds`: `HasComplexStandardParameter n ρ π ds` holds iff
  `ds.length = n` and there is `A` with `Function.Injective A` and
  `IsComplexStandardIntertwining n ρ π ds A`. Proof: `Iff.rfl`. The two sides unfold to the
  same term.
- `surjective_of_isComplexStandardIntertwining n hirr hA h0`: if
  `IsIrreducibleGKModule ρ π`, `IsComplexStandardIntertwining n ρ π ds A` and `A ≠ 0`, then
  `A` is surjective.

  Proof. Apply the second clause of `IsIrreducibleGKModule` to `W = LinearMap.range A`.
  - `W` is `ρ`-stable. For `k : Matrix.unitaryGroup (Fin n) ℂ`, the unit
    `Unitary.toUnits k : GeneralLinear n ℂ` lies in `unitaryCompact ℂ n` (proof `k.2`). The
    first clause, applied to it and `f`, gives `ρ k (A f) = A ⟨_, hf⟩ ∈ W`, since
    `⟨(Unitary.toUnits k : Matrix), k.2⟩` is `k` by definition.
  - `W` is `π`-stable. Fix `w = A f` and induct on `Y : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ`
    with `TensorProduct.inductionOn`. For a pure tensor `z ⊗ₜ X`, write it as
    `z • (1 ⊗ₜ X)`. Then `π (z ⊗ₜ X) (A f) = z • π (1 ⊗ₜ X) (A f) = z • A ⟨_, hf⟩` by the
    second clause, which lies in `W`. Sums follow from `map_add` and `add_mem`.

  So `W = ⊥` or `W = ⊤`. `W = ⊥` means `A = 0` (`LinearMap.range_eq_bot`), which contradicts
  `h0`. `W = ⊤` is surjectivity (`LinearMap.range_eq_top`).

## Statements

### `ComplexLanglandsQuotientStatement.{uV}`

For every `n : ℕ`, every complex vector space `V : Type uV` and every `ρ`, `π` with
`IsComplexGKModule n ρ π`, `IsIrreducibleGKModule ρ π` and `IsAdmissibleGKModule ρ`, there are
`ds : List ComplexCharacterData` with `ds.length = n` and `IsComplexLanglandsOrdered ds`, and a
linear map `A` from `kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)` to `V`
with `A ≠ 0` and `IsComplexStandardIntertwining n ρ π ds A`. Genericity is not assumed.

Provenance (derived). This is the existence half of the Langlands classification of
`GL_n(ℂ)`, due to Zhelobenko and Naimark (`knapp-1994-archimedean-llc`, Theorem 4(a)–(b),
p. 405). Every irreducible admissible representation is the unique irreducible quotient
`J(σ₁, …, σ_n)` of `I(σ₁, …, σ_n)`, with characters `σⱼ` satisfying (4.3), up to
infinitesimal equivalence. On Harish-Chandra modules, the quotient map
`I(σ)_K → J(σ)_K` composed with an isomorphism `J(σ)_K ≅ V` is a nonzero `(𝔤, K)`-map. Two
more standard facts are needed to apply this to the algebraic modules of `GKModule`:

- every irreducible admissible `(𝔤, K)`-module is the Harish-Chandra module of an irreducible
  admissible representation (Harish-Chandra; Casselman–Wallach globalization), or
  equivalently the classification holds for `(𝔤, K)`-modules directly;
- `I(σ)_K` is `kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)` with right
  translation and right derivatives. This includes the facts that `U(n)`-finite smooth
  functions in the principal series are stable under right derivatives, and that the Lie
  algebra action is that of the real Lie algebra `𝔤𝔩_n(ℂ)`, extended complex-linearly.

By `surjective_of_isComplexStandardIntertwining`, any such `A` is onto, so `V` is a quotient
of the standard module. The statement asks only for `A ≠ 0`, which is weaker than asking for
a surjection.

### `ComplexGenericStandardInjectiveStatement.{uV}`

For every `n : ℕ`, every complex vector space `V : Type uV`, every `ρ`, `π`, every
`ds : List ComplexCharacterData` and every linear map `A` from
`kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)` to `V`: if
`IsComplexGKModule n ρ π`, `IsIrreducibleGKModule ρ π`, `IsAdmissibleGKModule ρ`,
`IsComplexGenericGKModule n π`, `ds.length = n`, `IsComplexLanglandsOrdered ds`,
`Function.Surjective A` and `IsComplexStandardIntertwining n ρ π ds A`, then `A` is injective.

Provenance (derived). `V` is then the Langlands quotient of the standard module of `ds`, and
`A` is injective iff that standard module is irreducible as a `(𝔤, K)`-module. Its kernel is
`ρ`- and `π`-stable by the two clauses. For a generic Langlands quotient this is the theorem
that the standard module is irreducible:

- Jacquet (`jacquet-2009-archimedean-rankin-selberg`, Lemma 2.5 and the paragraph after it,
  p. 9): if `Re u₁ ≤ ⋯ ≤ Re u_r` (the Langlands order for his lower-parabolic induction, see
  above) and the Langlands quotient of `I_{σ,u}` admits a nonzero continuous `ψ`-form, then
  `I_{σ,u}` is irreducible. He refers to Vogan (Invent. Math. 48, 1978) for an algebraic
  proof.
- Casselman–Shahidi (`casselman-shahidi-1998-standard-modules-generic`, introduction,
  printed p. 562, PDF page 3) state that for `F = ℝ` Vogan proved this for quasi-split
  groups. `GL_n(ℂ)`, regarded as a real group, is quasi-split.

These sources speak of continuous Whittaker functionals on the smooth representation, while
`IsComplexGenericGKModule` asks for an algebraic functional on the Harish-Chandra module
`V`. The passage between the two is the theorem that an irreducible Harish-Chandra module
with a nonzero algebraic Whittaker functional for a nondegenerate character is large, and
that large irreducible modules of quasi-split groups are generic (Kostant 1978; Matumoto 1987;
Vogan 1978). These sources are not registered in the project's literature. The character
`X ↦ i Re(∑ aᵢ X_{i,i+1})` of `IsComplexGenericGKModule` is nondegenerate on both factors
of `ℂ ⊗_ℝ 𝔤𝔩_n(ℂ) ≅ 𝔤𝔩_n(ℂ) × 𝔤𝔩_n(ℂ)`, because all `aᵢ ≠ 0`.

The Langlands order cannot be dropped. For `GL_2(ℂ)`, the principal series with
`σ = δ_B^{-1/2}`, whose exponents `-1/2, 1/2` increase, consists of the functions on
`B \ G` and contains the constants, the trivial representation. Its quotient by them is the
other composition factor, which is infinite-dimensional and generic (it is equivalent to a
tempered principal series). So there a surjection onto a generic irreducible module is not
injective.

### `ComplexGenericParameterReductionStatement.{uV}`

`ComplexLanglandsQuotientStatement.{uV} → ComplexGenericStandardInjectiveStatement.{uV} →
ComplexGenericStandardParameterStatement.{uV}`.

Provenance: internal; it records the split of the target.

## Proof of the reduction

`complexGenericParameterReduction : ComplexGenericParameterReductionStatement.{uV}`.

Proof. Assume `h₁` and `h₂`, and let `n`, `V`, `ρ`, `π` satisfy the four hypotheses of the
target. `h₁` gives `ds` with `ds.length = n`, `IsComplexLanglandsOrdered ds` and `A ≠ 0` with
`hA : IsComplexStandardIntertwining n ρ π ds A`.
`surjective_of_isComplexStandardIntertwining` makes `A` surjective. `h₂`, applied to the
hypotheses, `ds.length = n`, the order, surjectivity and `hA`, makes `A` injective. The
triple `⟨ds, ds.length = n, A, injectivity, hA⟩` is `HasComplexStandardParameter n ρ π ds`.
