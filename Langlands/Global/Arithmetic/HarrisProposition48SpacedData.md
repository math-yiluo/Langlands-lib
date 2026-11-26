# Even real degree and weights at distance at least two in Proposition 4.8

This module defines two clauses added to the datum of Harris (1998), Proposition 4.8,
and to the problems of its induction: the base field has even real degree, and the
inducing Hecke character has weights at distance at least two. The published
`IsProposition48Datum` and the published problem predicates are unchanged.

The clauses restrict the construction to the range in which it can apply the theorem
of Clozel and Kottwitz in the form with multiplicity of Henniart 2001, §5.5, with two
hypotheses added to Henniart's. His §5.5 gives the multiplicity `a ≥ 1` under an
algebraic regular infinitesimal character and one split place with a discrete series
component. The added conditions are:

- even real degree, which holds for the fields of Henniart's construction because they
  contain the real quadratic field `R` of his §5.1 (printed p. 177); it is the range in
  which Clozel 1991, Théorème 5.7 (printed p. 142), needs only one split place with a
  discrete series component;
- regular highest weight, the hypothesis of Kottwitz 1992, remark after Theorem 1
  (printed p. 658), under which the cohomology of his Shimura varieties lies in the
  middle degree. For `GL_n` the infinitesimal character of highest weight `μ` has the
  ordered entries `μ_i + (n + 1)/2 − i`; subtracting this `ρ` shift lowers each gap
  between adjacent entries by one. So the highest weight is regular (strictly
  decreasing) exactly when the entries of the infinitesimal character are at distance at
  least two.

The module proves the elementary facts about the clauses. Their passage to the Mackey
children is in `HarrisProposition48SpacedInheritance`, and their construction in the
datum is in `HenniartHarrisDatumSpacedProof`.

## Even real degree

- `Harris.HasEvenRealDegree E`: `Even (Module.finrank ℚ (maximalRealSubfield E))`. For a
  CM field `E = E₀ K₀` with `E₀` totally real and `K₀` imaginary quadratic, `E₀` is the
  maximal totally real subfield (`[E : E₀] = 2`), so this is the condition `[E₀ : ℚ]`
  even.
- `finrank_eq_two_mul_finrank_maximalRealSubfield`: `[E : ℚ] = 2 [E⁺ : ℚ]` for a CM field.
  It follows from the tower law and Mathlib's instance that `E/E⁺` is quadratic.
- `hasEvenRealDegree_iff`: for a CM field, even real degree is `4 ∣ [E : ℚ]`.
- `HasEvenRealDegree.of_algebra` and `HasEvenRealDegree.of_ringEquiv`: the condition passes
  to CM extensions (`[D : ℚ] = [D : E][E : ℚ]`) and along ring isomorphisms.
- `hasEvenRealDegree_of_sq_pos`: a CM field containing a square root `x` of a positive
  rational `d` that is not a square has even real degree. The published
  `mem_maximalRealSubfield_of_sq_pos` puts `x` in `E⁺`, and the published
  `squareRoot_finrank` gives `[ℚ(x) : ℚ] = 2`, which divides `[E⁺ : ℚ]`.

## Weights at distance at least two

- `Harris.rotation E τ x`: for an infinite place `τ` of `E` and `x ∈ E_τˣ`, the number
  `z / z̄` with `z = extensionEmbedding τ x`.
- `Harris.IsRelativelySpaced E χ`, for a Hecke character `χ` of `E' ⊇ E`. Let `τ` be a
  place of `E` and `w ≠ w'` places of `E'` above it. For each integer `k` with `|k| ≤ 1`
  there is `x ∈ E_τˣ` such that the component of `χ` at `w`, read on `E_τˣ` through the
  completion map, differs from the component at `w'` times `rotation(x)^k`.

  Meaning at a complex place `τ` of `E`. Let `χ` be algebraic and conjugate inverse,
  with integral infinity type `t` after the twist of Harris 1998, p. 195, so
  `t(σ) + t(σ̄)` is constant. Let `σ, σ'` be the embeddings of `E'` at `w, w'` that extend
  the embedding of `τ`. The quotient of the two components on `ℂˣ` is then
  `z ↦ (z / z̄)^{t(σ) − t(σ')}`. Since `z ↦ z / z̄` maps `ℂˣ` onto the unit circle, this
  quotient equals `(z / z̄)^k` for all `z` exactly when `t(σ) − t(σ') = k`. So the
  condition at `τ` says `|t(σ) − t(σ')| ≥ 2`. For the automorphic induction `Π` of `χ`
  from `E'` to `E`, the numbers `t(σ)` are the entries of the infinitesimal character
  of `Π` at the embedding of `τ`, up to a common shift, so the condition is regular
  highest weight of `Π` there. This interpretation is not proved in Lean.

  At a real place `τ` of `E` the rotation is identically `1`, and the three tests for
  `k = 0, ±1` are the single test that the two components differ on `ℝˣ`; there the
  predicate has no numerical meaning of this kind. The base fields of Proposition 4.8 are
  CM fields, hence totally complex. For a totally complex `E` the test `k = 0` alone is
  the published `IsRelativelyRegular` (Harris 1998, Definition 2.3).
- `IsRelativelySpaced.isRelativelyRegular`: for a totally complex `E`, the case `k = 0`.
The next two results assume that the base `K` is totally complex (`IsTotallyComplex K`),
as the base fields of Proposition 4.8 are. Then every completion extension `L_w / K_v` at
infinity is `ℂ / ℂ`, of degree one, and the local norm is the identity. Over a real base
place both results fail in general: for `K = ℚ`, `L = ℚ(∛2)` and `ν` the inverse idelic
modulus, the complex component of `ν ∘ N` at `x = 2` is `1/4` while `ν` at the real place
is `1/2`; and `ξ = ν⁻¹ ∘ N` is relatively spaced (its restrictions are `|x|` and `|x|²`,
the rotation being `1`) while `ξ · (ν ∘ N) = 1` is not.

- `normComp_infiniteComponent_completionMap`: for a totally complex `K`, the component of
  `ν ∘ N_{L/K}` at a place `w` above `v`, read on `K_vˣ`, is the component of `ν` at `v`.
  Its proof follows the argument of the private lemma of the same name in
  `HarrisNormTwistInfinityProof`.
- `IsRelativelySpaced.mul_normComp`: for a totally complex `K`, a norm twist `ξ · (ν ∘ N)`
  keeps the weights at distance at least two. The twist multiplies the components at all
  places above `v` by the same character of `K_vˣ`, which cancels. This is the twist of
  Henniart 2001, §5.11, which moves all weights at a place by the same amount.
- `isRelativelySpaced_of_weights`: for totally complex number fields `E ⊆ E'`, a
  character `X` of anticyclotomic infinity type `A`,
  times a character `Y` whose components agree at all places above each place of `E`,
  is relatively spaced when `|A(σ) − A(σ')| ≥ 2` for the lifted embeddings at distinct
  places above a common place. The proof evaluates at `z = exp(iθ)`, an element of `E_τ`
  because `E_τ → ℂ` is onto at a complex place, with
  `θ = π / (2(A(σ) − A(σ') − k))`. It uses the published `infiniteComponent_completionMap`
  and `exp_zpow_mul_star_zpow` of `HarrisDatumArchimedean`, as in the published
  `isRelativelyRegular_of_weights`.

## The clauses in the datum and in the problems

- `Harris.IsProposition48SpacedDatum e χ χs K₀ P Ps ξ`: the published
  `IsProposition48Datum e χ χs K₀ P Ps ξ`, `HasEvenRealDegree E` and
  `IsRelativelySpaced E ξ`.
- `Proposition48Problem.IsSpaced Q`: `HasEvenRealDegree Q.E` and
  `IsRelativelySpaced Q.E Q.ξ`.
- `Proposition48Problem.IsSpaced.withCorrectedCharacter`: the parity correction of the
  induction (`withCharacters (correctedCharacter ν) χ χs`) keeps both clauses. The base
  field is unchanged and the corrected character is the norm twist `ξ · (ν ∘ N)`.

All results in this module are proved; only the standard axioms are used.

## Sources

- G. Henniart, *Sur la conjecture de Langlands locale pour `GL_n`*, J. Théor. Nombres
  Bordeaux 13 (2001), §5.1 (printed p. 177: the real quadratic field `R` in all fields of
  the construction), §5.5 (printed pp. 178–179: the theorem with multiplicity, under a
  regular infinitesimal character), §5.11 (printed p. 182: the twist by `φ`
  with `φ_τ(z) = (τz/|τz|)^{±1}`). Registered `henniart-2001-langlands-locale-gln-jtnb`,
  SHA256 `c9db009ee2f2e561d834b9e1ef07a8b27ff40d0edd19546d3351f38f39b2dac5`.
- M. Harris, *The local Langlands conjecture for `GL(n)` over a `p`-adic field, `n < p`*,
  Invent. Math. 134 (1998), Definition 2.3 and p. 195 (the twist `‖·‖^{(n−1)/2}`),
  Proposition 4.8 (pp. 201–203). Registered `harris-1998-local-langlands`, SHA256
  `7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`.
- L. Clozel, *Représentations galoisiennes associées aux représentations automorphes
  autoduales de `GL(n)`*, Publ. Math. IHÉS 73 (1991), Théorème 5.7, printed p. 142.
  Registered `clozel-1991-selfdual-galois`, SHA256
  `9de7c13c9ae108e481de170327a06e44845cf87a6aabc1d5600176ee695e91ac`.
- R. E. Kottwitz, *On the `λ`-adic representations associated to some simple Shimura
  varieties*, Invent. Math. 108 (1992), remark after Theorem 1, printed p. 658.
  Registered `kottwitz-1992-lambda-adic-simple-shimura`, SHA256
  `749af5541a59187e6f9d1089dec9a0e591a2059173da739c7384ff3a7d0dd799`.
