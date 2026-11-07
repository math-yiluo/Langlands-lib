# Bernstein's unitary product and shifted highest-derivative theorems

Authors: Worker 1808 (Lean module and Markdown) and Worker 1775 (independent
source and normalization check). This pair states the three parts of Bernstein's theorem on
unitary representations of `GL_n` over a p-adic field, as Tadic 1986, Theorem
2.5 uses them. Every assertion is a Prop-valued definition. **No part is proved
here.** The pair has no axioms, no proof holes and no structure fields that
assume a result. Two helper definitions are added: a Hermitian predicate and an
abbreviation for the shifted highest derivative.

## Parameters, universes and normalizations

All names are in `Langlands.Classification`. Fix `{p : ℕ} [Fact p.Prime]`,
`F : PadicField.{uF} p` and `T : F.TopologicalData`. Every statement installs
`letI := T.topology`; no canonical topology is used. The field universe `uF`
and the representation universe `uV` are independent. All representations are
actual smooth complex representations
`SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)`. This is the
carrier universe of `Langlands.Classification.TadicUnitaryDualExhaustion`.
Normalized induction and the derivative functors keep that universe.
No admissibility or finite-dimensionality hypothesis is added.

Library notions, used by Lean name:

- `Representation.IsIrreducible` (Mathlib): `IsSimpleOrder` on the lattice of
  subrepresentations, so `⊥ ≠ ⊤` and every subrepresentation is `⊥` or `⊤`.
- `IsUnitarizable` (`Unitary.Basic`): existence of an invariant positive
  definite Hermitian form on the carrier, with no completion or topology.
- `T.normalizedProductInductionFunctor B`, for `B : GeneralLinear.BlockShape n`
  (`Induction.BlockFactors`). It is normalized parabolic induction from the
  standard upper block parabolic, applied to the external tensor product of
  the blocks. This is the product `σ_1 × ⋯ × σ_r` of the sources.
- `T.segmentFactor A s` (`Classification.Segments`): the twist
  `ν^s A = A ⊗ |det|^s` by `T.determinantPowerCharacter r s`, which is
  `realPowerCharacter (T.determinantNorm r) s`. The absolute value is
  residue-normalized, so `|ϖ| = q⁻¹`.
- `Langlands.Derivative.generalLinearDerivative T ψ N k hk : GL_N → GL_(N-k)`
  (`Derivative.Iteration`). For `k ≥ 1` it is restriction to the mirabolic
  `P_N`, then `(Φ⁻)^(k-1)`, then `Ψ⁻`. These are the Bernstein-Zelevinsky
  normalized minus functors of `Derivative.MirabolicMinus`.
- `Langlands.Derivative.GeneralLinearHighestDerivativeOrderData T ψ π`
  (`Derivative.GeneralLinearHighestDerivativeOrder`). Its fields are a positive
  order `k ≤ N` whose derivative is nonzero (`Nontrivial`), and the vanishing
  (`Subsingleton`) of every derivative of higher order `j ≤ N`. Thus `k` is the
  depth of `π`. The Library's `chooseGeneralLinearHighestDerivativeOrder`
  produces such data for every nonzero `π` of positive rank, so the
  quantification in part 3 is not vacuous.

## The Hermitian condition

`HasNonzeroInvariantSesquilinearForm ρ`, for any monoid `G` and complex
representation `ρ : Representation ℂ G V`, is

```
∃ b : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ, b ≠ 0 ∧ ∀ (g : G) (v w : V), b (ρ g v) (ρ g w) = b v w
```

`b` is conjugate-linear in the first variable and linear in the second. This is
the convention of `Langlands.UnitarizabilityContinuationStatement`, made into a
named predicate.

Provenance: Tadic §2.1 (p.345) calls `π` Hermitian when `π ≅ π⁺`. Here `π⁺` is
the complex conjugate of the contragredient, the Hermitian contragredient.
Bernstein §7.8 (p.86) uses the same Hermitian contragredient. For irreducible
admissible `π`, an isomorphism `π → π⁺` is the same as a nonzero invariant
sesquilinear form. By Schur's lemma such a form is unique up to a scalar, so a
scalar multiple of it is Hermitian. This equivalence is standard background,
not proved here. Part 2 uses the sesquilinear-form predicate as its definition
of Hermitian.

## Part 1: irreducibility of unitary products

`BernsteinUnitaryProductIrreducibility F T` says the following. Take any `n`,
any `B : BlockShape n` and any family
`σ : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)`
with every `σ i` irreducible and unitarizable. Then the entire normalized
product `(T.normalizedProductInductionFunctor B).obj σ` is irreducible and
unitarizable.

Source: Tadic 1986, Theorem 2.5(i), p.346: "If `π₁, π₂ ∈ Irr^u` then
`π₁ × π₂ ∈ Irr^u`". Bernstein 1984, Corollary 8.2 a), p.89: if `π`, `σ` are
irreducible and unitarizable, then `π × σ` is irreducible and unitarizable.

## Part 2: unitarity of the factors of an irreducible unitary product

`BernsteinUnitaryProductFactorUnitarity F T` says the following. Take any `n`,
`B` and `σ` as above. Suppose every `σ i` is irreducible and satisfies
`HasNonzeroInvariantSesquilinearForm`, and the entire normalized product is
irreducible and unitarizable. Then every `σ i` is unitarizable.

Source: Tadic 1986, p.346, right after Theorem 2.5. Tadic says the only form of
2.5(ii) the paper uses is: "If `π₁, π₂ ∈ Irr` are Hermitian and `π₁ × π₂` is
irreducible unitarizable, then `π₁` and `π₂` are unitarizable." The full
2.5(ii), without irreducibility of the product, is Bernstein 1984, Corollary
8.2 b), p.89. It is not stated here.

## Part 3: unitarity of the shifted highest derivative

`shiftedHighestDerivative F T ψ hd` is an abbreviation. Here `hd` is
`GeneralLinearHighestDerivativeOrderData T ψ π` for
`π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)`. It unfolds to

```
T.segmentFactor ((Derivative.generalLinearDerivative T ψ N hd.order hd.le_rank).obj π) (1 / 2)
```

This is the representation `ν^(1/2) π^(h)` of `GL_(N - hd.order)`, where
`h = hd.order`.

`BernsteinShiftedHighestDerivativeUnitarity F T` says the following. Take any
`N` with `0 < N`, any unitary additive character
`ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology`, and any irreducible
unitarizable `π` of `GL_N`. Then for every `hd`, the representation
`shiftedHighestDerivative F T ψ hd` is irreducible and unitarizable.

Sources:

- Tadic 1986, Theorem 2.5(iii), p.346: "If `π ∈ Irr^u` then `π' ∈ Irr^u`".
- Tadic §1.16, pp.344–345. For a segment `Δ = [ρ, ν^i ρ]`, it sets
  `Δ⁻ = [ρ, ν^(i-1) ρ]` if `i ≥ 1` and `Δ⁻ = ∅` if `i = 0`, and
  `Δ' = ν^(1/2) Δ⁻`. For `a = (Δ₁, …, Δ_m)` it sets `a⁻ = (Δ₁⁻, …, Δ_m⁻)` and
  `a' = (Δ'₁, …, Δ'_m)`. Then `⟨a⁻⟩` is the highest derivative of
  `π = ⟨a⟩`, and `π' = ⟨a'⟩` is the highest shifted derivative. These formulas
  were checked on the rendered pages.
- Bernstein 1984, §7.2, pp.81–82. It defines the derivatives
  `π^(k) = Ψ⁻(Φ⁻)^(k-1)(π|_P)` with the functors of [BZ2, §3], the depth `h`
  and the highest derivative `π^(h)`. It also defines the shifted derivatives
  `π^[k] = ν^(1/2) · π^(k)`, where `ν^(1/2)(g) = |det g|^(1/2)`.
- Bernstein 1984, §7.4, the unitarizability criterion for G-modules. An
  irreducible unitarizable `π` has a unitarizable highest shifted derivative
  `π^[h]`; this is condition (ii). §7.4 begins on printed p.83 (PDF page 34).
  The task contract and the literature pointer cite it as p.82, which holds
  §7.2–§7.3. The rendered page was checked.
- Bernstein 1984, Theorem in §7.7, p.85, quoting Zelevinsky [Z1, 8.1]. The
  highest shifted derivative `⟨a⟩^[h]` is isomorphic to the irreducible `⟨a'⟩`.
- The Remark after §7.4, p.83, says that for irreducible unitarizable `π` the
  derivative `π^[h]` is irreducible and unitarizable, using the results of §8.
  The Remark calls it the highest derivative, but by the notation of §7.2 it
  is the highest *shifted* derivative `ν^(1/2) π^(h)`. The unshifted highest
  derivative `π^(h)` is also irreducible, but in general it is not
  unitarizable. For `π = 1_(GL_2)`, the check below gives
  `π^(1) = ν^(-1/2)`. At a uniformizer this character has absolute value
  `q^(1/2) > 1`, so it preserves no positive definite Hermitian form. Part 3
  states the shifted assertion only.

### The twist exponent

In the Library, `Ψ⁻` (`Mirabolic.psiMinus T n`) is the coinvariants for the
trivial character of `V_(n+1)`, twisted by
`psiMinusCharacter T n = realPowerCharacter (T.determinantNorm n) (-(1 / 2 : ℝ))`.
`Φ⁻` is the `ψ`-twisted coinvariants, twisted by the restriction of
`|det|^(-1/2)` to `P_(n+1)`. This is BZ 1977 §1.8(b), §3.2, with
`mod_U^(-1/2)` written as `|det|^(-1/2)`, as `Derivative/MirabolicMinus.md`
records. Bernstein §7.2 uses the same functors. `T.segmentFactor` twists by the
same family `realPowerCharacter (T.determinantNorm r) s`.

The module `Derivative.MirabolicMinus` defines these functors with explicit
determinant characters and does not itself compare them with BZ 1977's Haar
modulus `mod_V`. The Library proves that comparison elsewhere, in
`Derivative.MirabolicHighestLayerLift` (namespace
`Langlands.Derivative.Mirabolic.HighestLayer`). There,
`map_inv_mul_haar` and `map_inv_mul_haar_iff` show that the Haar modulus of
conjugation by `levi g` on the radical is `|det g|`. Then
`psiMinusCharacter_eq_modulus` and `phiMinusCharacter_eq_modulus` identify both
minus characters with the `-1/2` power of that modulus. So the Library's
`Ψ⁻` and `Φ⁻` are BZ 1977's normalized functors. This pair uses the
determinant-normalized functors directly and adds no comparison hypothesis.

Check on the trivial representation `1` of `GL_2`:

- Order 1. `generalLinearDerivative T ψ 2 1 _` is a rank transport, then
  restriction to `P_2`, then `(Φ⁻)^0 = 𝟭`, then `Ψ⁻ : P_2 → GL_1`. The radical
  `V_2` acts trivially, so the coinvariant quotient is all of `ℂ`, and `GL_1`
  acts trivially before the twist. The twist `psiMinusCharacter T 1` then gives
  `|det|^(-1/2) = ν^(-1/2)` on `GL_1`.
- Order 2. Here the first step is `Φ⁻ : P_2 → P_1`. The character
  `θ(u) = ψ(u₁₂)` is nontrivial because `ψ` is. Choose `u` with `θ(u) ≠ 1`.
  Then every vector `ξ` of the trivial representation equals
  `(1 - θ(u))⁻¹ (ξ - θ(u) ξ)`, so the coinvariants and the order-2 derivative
  are zero.
- Hence the highest order is `1`, and the highest derivative is `ν^(-1/2)` on
  `GL_1`. `T.segmentFactor _ (1/2)` multiplies it by
  `realPowerCharacter (T.determinantNorm 1) (1/2) = ν^(1/2)`. The product is
  `|det|^0`, the trivial character of `GL_1`.

This agrees with Tadic. In Zelevinsky's convention `1_(GL_2) = ⟨Δ⟩` for
`Δ = [ν^(-1/2), ν^(1/2)]`, and `⟨Δ⟩` is the unique irreducible subrepresentation
of `ν^(-1/2) × ν^(1/2)`. Then `Δ⁻ = [ν^(-1/2)]` and
`Δ' = ν^(1/2) Δ⁻ = [1_(GL_1)]`. So the highest derivative is `ν^(-1/2)` and
`π' = ⟨a'⟩ = 1_(GL_1)`. The exponent `+1/2` is therefore the source's
exponent for the Library normalization. This computation is recorded here and
not formalized.

## Conjunction

`BernsteinUnitaryStatements F T` is the conjunction
`BernsteinUnitaryProductIrreducibility F T ∧ BernsteinUnitaryProductFactorUnitarity F T ∧ BernsteinShiftedHighestDerivativeUnitarity F T`,
with universe parameters `.{uF, uV}`.

## Derived formulation choices

- **Finite families.** The sources state parts 1 and 2 for two factors. The
  task contract fixes the finite-family form over all
  `B : BlockShape n`. A proof can reduce it to the binary form by induction on
  the number of blocks, using transitivity of normalized parabolic induction.
  For part 2 it also needs two facts about the partial product of the
  remaining blocks: it is irreducible because induction is exact, and Hermitian
  because the Hermitian contragredient commutes with normalized induction. This
  reduction is a proof obligation, not supplied here.
- **Rank zero.** For `n = 0`, `B` has no blocks. The empty product is the
  one-dimensional representation of the trivial group `GL_0`. This is the unit
  `1 ∈ Irr G_0` of the sources' ring `R` (Bernstein §7.5, `R_0 = ℤ`). Part 1
  then asserts it is irreducible and unitarizable, and part 2 is vacuous.
  A single block (`B.length = 1`) gives one-block induction from `GL_n` to
  itself.
- **Highest order `N`.** In part 3, `hd.order = N` is allowed, for example for
  generic `π`. Then the derivative lies on `GL_0`, the twist is trivial, and
  the statement concerns the unit `1 ∈ R_0`. This is the sources' case where
  every segment of `a'` is empty (Tadic §1.16 sets `Δ⁻ = ∅` for `i = 0`;
  Bernstein §7.6–7.7 put `⟨Δ'⟩ = 1 ∈ R_0` when `Δ' = ∅`).
- **Additive character.** The Library's derivative depends on a chosen
  nontrivial unitary additive character `ψ`; the sources' derivative does not,
  up to isomorphism. Part 3 quantifies over every `ψ` and every `hd`. The order
  `hd.order` is determined by `π` and `ψ`, since it is the greatest order with
  nonzero derivative. `0 < N` is the contract's hypothesis. It also follows
  from `hd.positive` and `hd.le_rank`.
- **Unitarizability.** The Library already proves that normalized products of
  unitarizable blocks are unitarizable (`glNormalizedInductionUnitarity`,
  `Induction.UnitaryProof`). The new content of part 1 is irreducibility.
  Part 1 restates both conclusions, as Tadic 2.5(i) does.

## Sources

- Marko Tadic, *Classification of unitary representations in irreducible
  representations of general linear group (non-archimedean case)*, Ann. Sci.
  ENS (4) 19 (1986), 335–382. Registered as `tadic-1986-unitary`, at
  `/home/taskhub/central-library/Tadic--Classification of unitary representations in irreducible representations of GL(n)--1986.pdf`,
  SHA-256 `08e4e1e7c1ccc1e340999287867bc0448f3d8f4bab49906fbf1deda866ae4683`.
  The PDF page is the printed page minus 333. Pages 344–346 (PDF 11–13) were
  read on the rendered pages: §1.16, §2.1 and Theorem 2.5 with its weak form.
- J. N. Bernstein, *P-invariant distributions on GL(N) and the classification
  of unitary representations of GL(N) (non-archimedean case)*, Lecture Notes in
  Math. 1041 (1984), 50–102. Registered as `bernstein-1984-p-invariant`, at
  `/home/taskhub/central-library/Bernstein--P-invariant distributions on GL(N) and the classification of unitary representations of GL(N) (Non-archimedean case)--1983.pdf`,
  SHA-256 `b050423087ee36592c4747ba6f3c9a9fdef9c8e4b8919e3737cf7ecdfcc94ab2`.
  The PDF page is the printed page minus 49. Read: §7.1–§7.2 (pp.81–82),
  §7.3–§7.4 (pp.82–83), §7.5–§7.9 (pp.84–87), §8.1–§8.2 (pp.87–89). The
  rendered pages 82, 83 and 89 were checked.
- Zelevinsky 1980 (Ann. Sci. ENS 13), Theorem 8.1, is cited through
  Bernstein §7.7 and Tadic §1.16 only; it was not read for this pair.

No errata entry for either source was found in the supplied literature index or
the public notes.

## Proof boundary

Nothing here is proved. A proof of part 1 needs Bernstein's irreducibility
argument. That argument uses the P-module unitarizability criterion (§7.3,
proved in §9), the highest shifted derivative of products, and G-positivity
(§8.1–§8.2). A proof of part 2 needs the weak form of 2.5(ii), plus the
finite-family reduction above. A proof of part 3 needs Zelevinsky's computation
of highest derivatives of irreducibles (irreducibility of `π^(h)`) and
Bernstein's criterion §7.4 (unitarizability of `π^[h]`), in the Library's
derivative normalization.
