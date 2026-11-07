# Three lemmas of Tadić's exhaustion argument

Author: Worker 1792. This pair states three results from Tadić's 1986 paper as
Prop-valued definitions: Lemma 4.8(ii) (existence of the factorization only),
Lemma 6.3, and Corollary A.6(ii) extended from two factors to finitely many.
It also states their conjunction. **None of these assertions is proved here.** The
module proves no theorem. It adds no axiom, no `sorry`, and no structure field
assuming the existence of anything.

All new names lie in `Langlands.Classification`, in module
`Langlands.Representation.Classification.TadicExhaustionLemmasStatement`. The
module imports `Classification.TadicMultisegments`, which supplies Tadić's
`a(n,d)^ρ` (`tadicMultisegment`), his set `X_k` (`IsTadicXBlock`) and his
statement `(U^m)` (`TadicSocleUnitarity`).

These three results are the ones of Tadić's appendix argument (A.10) for the
exhaustion `TadicUnitaryDualExhaustion` that no published statement covers yet.

## Source

M. Tadić, *Classification of unitary representations in irreducible
representations of general linear group (non-Archimedean case)*, Ann. Sci.
ÉNS (4) 19 (1986), 335–382, literature ID `tadic-1986-unitary`. PDF page =
printed page − 333.

- Lemma 4.8: printed p.360 (PDF p.27); its proof continues on p.361.
- Lemma 6.3: printed p.366 (PDF p.33).
- Corollary A.6: printed p.375 (PDF p.42).
- Notation: `ℕ` is the set of positive integers (p.339); `C` is the set of
  cuspidal classes and `C^u` the unitary ones; `a(n,d)^ρ` is defined in §4.6
  (p.358) with the segments of §3.1; `L(a)` is defined in §5.2 (p.361); `⟨a⟩` is
  Zelevinsky's representation; `×` is normalized parabolic induction (§1.1).

## Parameters and conventions

The parameters are an arbitrary prime `p` with `[Fact p.Prime]`,
`F : PadicField.{uF} p` and `T : F.TopologicalData`, all explicit in the four
definitions. The field universe `uF` and the representation universe `uV` are
independent. Every representation is an actual smooth complex representation
`SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)` with
`letI := T.topology`. This is the carrier universe of
`TadicUnitaryDualExhaustion`. Cuspidal data and multisegments are
`T.CuspidalDatum.{max uF uV, uF}` and `T.Multisegment.{max uF uV, uF}`. No
admissibility or finite-dimensionality condition is imposed.

- *Irreducible* is Mathlib's `Representation.IsIrreducible`.
- *Unitarizable* is the Library's `IsUnitarizable`: some positive definite
  Hermitian form on the carrier is preserved by the actual action.
- `ρ.IsUnitary` is the published `CuspidalDatum.IsUnitary`: `ρ` lies in `C^u`.
- Products are the published normalized upper-block products
  `(T.normalizedProductInductionFunctor B).obj σ` for a block shape
  `B : BlockShape N` and representations `σ i` of `GL_(B.size i)`. This is the
  product used in `TadicUnitaryDualExhaustion`.
- `a.IsLanglandsHead π` is the published `Multisegment.IsLanglandsHead` of
  `Classification.LanglandsData`. It says that for some precedence-ordered
  ordering of `a` and some segment heads `π_i` (each the irreducible head of the
  product attached to its segment, Tadić's `L(Δ_i)` of §5.1), `π` is the
  irreducible head of the normalized product of the `π_i`. This is Tadić's
  `L(a)`, the unique irreducible quotient of `λ(a)` (§5.2).
- `a.IsZelevinskySocle π` is the published `Multisegment.IsZelevinskySocle`: the
  same with segment socles and the irreducible socle. This is Zelevinsky's
  `⟨a⟩`.

Neither relation asserts independence of the ordering. Each is a relation, not a
choice of representative. Isomorphisms `π ≅ σ` are isomorphisms of smooth
representations in the published category.

## Lemma 4.8(ii): `TadicBlockReduction F T`

Tadić p.360: "Let `m ≥ 1`. Suppose that `(U^(m-1))` holds. Let
`X_(m-1) = {⟨a(n,d)^ρ⟩, π(⟨a(n,d)^ρ⟩, α); n, d ∈ ℕ, ρ ∈ C^u, (nd) deg ρ ≤ m-1,
0 < α < 1/2}`. Then … (ii) Set
`I(Ĝ_m) = Ĝ_m \ {⟨a(n,d)^ρ⟩; n, d ∈ ℕ, ρ ∈ C^u, (nd) deg ρ = m}`. If
`π ∈ I(Ĝ_m)`, then there exist `σ_1, …, σ_l ∈ X_(m-1)` such that
`π = σ_1 × … × σ_l`. Representations `σ_1, …, σ_l` are determined uniquely up to
a permutation."

`TadicBlockReduction F T` asserts: for every `m : ℕ`, if
`TadicSocleUnitarity F T m` holds, then every irreducible unitarizable `π` on
`GL_(m+1)` satisfies the following. Suppose there are no cuspidal datum `ρ`
with `ρ.IsUnitary` and no `n, d > 0` (with `hd : 0 < d`) such that
`(tadicMultisegment ρ n d hd).IsZelevinskySocle π`. Then there are a block shape
`B : BlockShape (m + 1)` and representations `σ i` of `GL_(B.size i)` with
`IsTadicXBlock m (σ i)` for every `i`, and an isomorphism
`π ≅ (T.normalizedProductInductionFunctor B).obj σ`.

Correspondence with the source:

- Tadić's `m ≥ 1` is `m + 1` here, so his `(U^(m-1))` is
  `TadicSocleUnitarity F T m` and his `X_(m-1)` is `IsTadicXBlock m`. The
  module `TadicMultisegments` explains why these match Tadić's `(U^m)` and
  `X_k`. Its complementary members use `ν^α σ × ν^(-α) σ` with
  `σ = ⟨a(n,d)^ρ⟩`, which is Hermitian, so this agrees with Tadić's
  `π(σ, α) = ν^α σ × ν^(-α) σ^+`.
- `π ∈ I(Ĝ_m)` means `π` is irreducible, unitarizable, and not of the form
  `⟨a(n,d)^ρ⟩` with `n, d ∈ ℕ` and `ρ ∈ C^u`. The degree condition
  `(nd) deg ρ = m` is automatic: by `tadicMultisegment_rank_eq_of_isZelevinskySocle`
  a Zelevinsky socle of `a(n,d)^ρ` on `GL_(m+1)` has `n d deg ρ = m + 1`.
  The exclusion is stated for `π` itself. A representation isomorphic to a
  Zelevinsky socle of `a(n,d)^ρ` is itself one, by composing the socle
  embedding with the isomorphism, so this is Tadić's exclusion of an isomorphism
  class.
- Tadić's equality `π = σ_1 × … × σ_l` holds in his Grothendieck ring `R`,
  where the product is commutative. Since `π` is irreducible, it means that the
  actual product is irreducible and isomorphic to `π`. The Lean conclusion is
  an actual isomorphism with the normalized product over a block shape of total
  rank `m + 1`, for some order of the factors. The block shape records the ranks
  of the `σ i` in that order.
- Only existence is stated. The uniqueness clause of (ii) and part (i) (members of
  `X_(m-1)` are irreducible unitarizable, and so are their products) are not
  stated.

## Lemma 6.3: `TadicRectangleHeadSocleDistinct F T`

Tadić p.366: "Let `n, d ∈ ℕ` and `n < d`. Then
`t(⟨a(n,d)^ρ⟩) ≠ ⟨a(n,d)^ρ⟩`, `ρ ∈ C`, i.e. `L(a(n,d)^ρ) ≠ ⟨a(n,d)^ρ⟩`."
Here `≠` compares irreducible classes, and `ρ` is any cuspidal class, not
necessarily unitary.

`TadicRectangleHeadSocleDistinct F T` asserts: for every cuspidal datum `ρ`, all
`n, d` with `hd : 0 < d`, `0 < n` and `n < d`, every `N`, and all
representations `π, π'` of `GL_N` with
`(tadicMultisegment ρ n d hd).IsLanglandsHead π` and
`(tadicMultisegment ρ n d hd).IsZelevinskySocle π'`, there is no isomorphism
`π ≅ π'`. The positivity `0 < n` is Tadić's `n ∈ ℕ`; for `n = 0` the
multisegment is empty and the statement would be false. The condition `0 < d`
is required by the construction and follows from `0 < n < d`. The statement
quantifies over all Langlands heads and all Zelevinsky socles, so it does not
depend on the choice of a representative or of an ordering.

## Corollary A.6(ii), finite form: `IrreducibleLanglandsHeadProduct F T`

Tadić p.375: "(ii) Let `a, b ∈ M(S(C))`. If `L(a) × L(b)` is irreducible then
`L(a) × L(b) = L(a + b)`."

`IrreducibleLanglandsHeadProduct F T` asserts: for every `n`, every block shape
`B : BlockShape n`, multisegments `a i` and representations `π i` of
`GL_(B.size i)` indexed by the blocks, if `(a i).IsLanglandsHead (π i)` for
every `i` and the normalized product
`(T.normalizedProductInductionFunctor B).obj π` is irreducible, then that
product is a Langlands head of the multiset sum `∑ i, a i`. This is
`L(a_1) × ⋯ × L(a_k) = L(a_1 + ⋯ + a_k)` whenever the left side is irreducible.

This finite form is derived from the two-factor source statement and is stated
here because the exhaustion argument applies it to a product of finitely many
blocks. It is a generalization, so the derivation belongs to a proof of the
statement. The derivation is by induction on the number of blocks. Normalized
parabolic induction is exact and sends nonzero representations to nonzero ones,
so a proper nonzero subrepresentation of `L(a_1) × ⋯ × L(a_(k-1))` would give one
of the whole product after inducing in stages. So `L(a_1) × ⋯ × L(a_(k-1))` is
irreducible and, by induction, a Langlands head of `a_1 + ⋯ + a_(k-1)`. The
two-factor statement applied to it and `L(a_k)` gives the claim. For `k = 2`
the finite form is the source statement; the cases `k = 0` and `k = 1` are
degenerate.

Tadić's `=` is equality of irreducible classes, while the Lean conclusion is the
relation for the given product itself. The two agree: a representation
isomorphic to an irreducible head of a standard product is again an irreducible
head of it, by composing the quotient map with the isomorphism, which keeps its
kernel.

## The conjunction

`TadicExhaustionLemmaStatements F T` is
`TadicBlockReduction F T ∧ TadicRectangleHeadSocleDistinct F T ∧
IrreducibleLanglandsHeadProduct F T`, with universes `.{uF, uV}` passed through.
