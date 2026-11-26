# The descent step of Proposition 4.8 from Theorem 1.2 with multiplicity

This module reduces the descent step of Harris's Proposition 4.8, in the form that takes
Harris's Theorem 1.2 with multiplicity as input, to five named inputs, following
Henniart 2001, §§5.9–5.12. The descent step is the statement
`Proposition48MultiplicitySingletonDescentSelectionTCStatement` (module
`HarrisProposition48MultiplicityStatement`): over a prime cyclic step `D/E` with a single
Mackey class, a stable, conjugate self-dual Mackey constituent `S` over `D` has a cyclic
descent to `E` that is a weak automorphic induction of the problem's character `ξ`. The
inputs are stated here as proposition definitions; the reduction is proved. All
declarations are in namespace `Langlands.Global.Harris`.

## Source

G. Henniart, *Sur la conjecture de Langlands locale pour `GL_n`*, J. Théor. Nombres
Bordeaux 13 (2001), §§5.9–5.12, printed pp. 180–182. In the second case of §5.9 the
representation `Π_{j+1}` over `F_{j+1}` is invariant under `Gal(F_{j+1}/F_j)` and comes
by base change from a cuspidal `Π` over `F_j`; by Harris 1998, proof of Lemma 1.6, `Π` is
the twist by a finite-order character `μ` of a `Π'` with `Π' ∘ c ≅ Π'^∨`.

- §5.10 (`d_j` odd). `Π'` is algebraic and regular, and the theorem of §5.5 (cited there
  as Théorème 5.6) gives `a ≥ 1` and a semisimple `ℓ`-adic `T` with
  `L(T_w, s) = L(Π'_w, s + (d_j − 1)/2)^a` at almost every place. Its restriction to
  `Gal(Q̄/F_{j+1})` has the L-factors of `a` copies of a twist of `Σ_{j+1}`. Hence there
  is a semisimple complex `Σ_T` with the L-factors of `T`, of the form
  `Σ_T = (twist) ⊗ Σ_j ⊗ (χ_1 ⊕ … ⊕ χ_a)`, each `χ_i` a character of `F_j` trivial on the
  norms from `F_{j+1}`. From `(*)` the L-function `L(Σ_T ⊗ Σ_T^∨, s)` has a pole of order
  `a²`, which is possible only if all `χ_i` equal one `χ`. Then `Π_j = (χ^{−1} ∘ det) ⊗ Π`
  is associated with `Σ_j`.
- §5.11 (`d_j` even). `Π'` is not algebraic in Henniart's normalization; he twists it by
  `φ ∘ N ∘ det` for a character `φ` with `φ ∘ c = φ^{−1}` and archimedean components
  `z ↦ (z / |z|)^{±1}`, and argues as in §5.10.
- §5.12. Existence of `φ`, from the triviality of the quadratic character of `F/F^c` on
  the relevant ideles and the extension of characters from a closed subgroup of a
  locally compact abelian group.

## Helpers (proved)

- `eq_of_pow_eq_pow_of_eval_zero`: two complex polynomials with constant term `1` whose
  `a`-th powers agree, `a > 0`, are equal (their root multisets agree and the constant
  terms fix the leading coefficients).
- `Langlands.GaloisRepresentation.residueCharacteristic_eq_of_natCast_mem` identifies the residue characteristic of a finite place containing a rational prime `p` with `p`. [Finite-place residue characteristics](../../Galois/FinitePlaceResidueCharacteristic.md)
- `realIntermediateField E`: the maximal totally real subfield of `E` as an intermediate
  field over `ℚ`; it is totally real, `HasEvenRealDegree.even_finrank_realIntermediateField`
  gives `Even [E⁺ : ℚ]` from `HasEvenRealDegree E` (module `HarrisProposition48SpacedData`),
  and `realIntermediateField_sup_eq_top` shows that for a CM field `E` and a totally
  complex subfield `K₀`, `E⁺ ⊔ K₀ = ⊤`: some `z ∈ K₀` is not fixed by the complex
  conjugation `c`, `b = (z − c z)/2` lies in `E⁺ ⊔ K₀` and satisfies `c b = −b ≠ 0`, and
  every `y` is `(y + c y)/2 + ((y − c y)/(2b)) b` with both coefficients in `E⁺`. These
  supply the CM decomposition `E = E₀ K₀` asked for by the theorem with multiplicity.

## Named inputs

Each input quantifies over the data of the descent step: a problem `Q` with
`Q.IsAuxiliaryValid` and `Q.IsSpaced`, an intermediate field `D` with
`Q.IsPrimeCyclicStep D` and one Mackey class, `IsCMField D`, `r ≥ 1`, and a cuspidal
realization `S` of rank `r + 1` over `D` with unitary central character, conjugate
self-dual, a Mackey constituent (`Q.IsMackeyConstituent D 1`) and stable under
`Gal(D/E)`.

- `IsHenniartTwistingCharacter φ`, for a Hecke character `φ` of a CM field: `φ` is
  conjugate inverse and at every infinite place `v` its component is
  `z ↦ (z / |z|)^ε` for some `ε = ±1`, read through the embedding of the completion.
- `HenniartTwistingCharacterStatement` (§5.12): every CM field has such a character.
- `Proposition48DescentTheorem12TwistStatement` (Harris 1998, proof of Lemma 1.6;
  Henniart 2001, §§5.9, 5.11): if every class `c` over `E` of which `S` is a weak base
  change has regular highest weight and a supercuspidal component at the auxiliary place
  `Q.Ps.v`, then, given a twisting character `φ` of `E`, every cyclic descent `S₀` of `S`
  has a determinant twist `T₀ = S₀ ⊗ (ψ ∘ det)` (`IsDeterminantMultiple ψ`) that is
  conjugate self-dual, has regular highest weight and is supercuspidal at `Q.Ps.v`. In
  Henniart's argument `ψ = μ^{−1}`, multiplied by `φ ∘ N` when his descent is not
  algebraic. Here the descents are assumed to have regular highest weight (the hypothesis
  of the descent step), so the finite-order twist of Lemma 1.6 suffices; in the problems of
  the Library the parity of the inducing character has already been corrected by a norm
  twist (the published `IsAuxiliaryParityNormalization`), whose role is that of Henniart's
  §5.11 twist.
- `Proposition48DescentRestrictionCharactersStatement` (§5.10, first part): let `η` be a
  Hecke character of `E` with norm kernel `D` (`HasNormKernel`), `S₀` a cyclic descent of
  `S`, and `T₀ = S₀ ⊗ (ψ ∘ det)` conjugate self-dual with regular highest weight. If for
  every prime `ℓ` and `ιℓ : ℂ ≃+* ℚ̄_ℓ` there are `a > 0` and a semisimple continuous
  representation of rank `a (r + 1)` with `IsHenniartAssociatedAt T₀ ιℓ R a`, then there
  are `a > 0`, exponents `i : Fin a → ℕ` with `i k < [D : E]`, a spectral system `s` of
  `T₀` and spectral systems `t k` weakly induced from `ξ · ((ψ η^{i k}) ∘ N_{E'/E})` such
  that at almost every place `s.eulerPolynomial v ^ a = ∏_k (t k).eulerPolynomial v`.
  This is Henniart's passage from the L-factors of the restriction to `Gal(Ē/D)` (by
  Chebotarev's density theorem and semisimplicity) to the `a` characters `χ_k = η^{i k}`
  trivial on the norms from `D` (by Frobenius reciprocity).
- `Proposition48DescentPairPoleStatement` (§5.10, second part): in the same situation,
  if `s.eulerPolynomial v ^ a = ∏_k (t k).eulerPolynomial v` at almost every place, with
  `t k` weakly induced from `ξ · ((ψ η^{i k}) ∘ N)` and `i k < [D : E]`, then all `i k`
  are equal. The partial L-function of the pair `(T₀, T₀^∨)` has a simple pole at `s = 1`,
  so its `a²`-th power has a pole of order `a²`; the product side has a pole of order the
  number of pairs `(k, l)` with `i k = i l`, since the induced representations stay
  irreducible on `D` (one Mackey class) and are pairwise distinct for distinct exponents
  below `[D : E]`.
- `Proposition48DescentUntwistStatement` (§5.10, end): if `T₀ = S₀ ⊗ (ψ ∘ det)` is a weak
  automorphic induction of `ξ · ((ψ η^i) ∘ N)`, then some class `c` over `E` of which `S`
  is a weak base change is a weak automorphic induction of `ξ` (namely `S₀ ⊗ η^{−i}`,
  again a descent of `S` because `η` is trivial on the norms from `D`).

Besides the theorem with multiplicity, Henniart's proofs of these inputs use the pole of
the L-function of a pair, strong multiplicity one, Chebotarev's density theorem, Frobenius
reciprocity and, for §5.12, the extension of characters from a closed subgroup of a
locally compact abelian group. None of the inputs is proved here.

## The reduction

`Proposition48DescentMultiplicityReductionStatement`: `HenniartTwistingCharacterStatement`,
`Proposition48DescentTheorem12TwistStatement`,
`Proposition48DescentRestrictionCharactersStatement`,
`Proposition48DescentPairPoleStatement` and `Proposition48DescentUntwistStatement`
imply `Proposition48MultiplicitySingletonDescentSelectionTCStatement`.

`proposition48DescentMultiplicityReduction` proves it; only the standard axioms are used.
The proof:

1. The published `HeckeCharacter.cyclicNormKernelCharacter` gives a character `η` of `E`
   with norm kernel `D`; a generator `σ` of the cyclic group `Gal(D/E)` is chosen.
2. The input `CyclicStableDescentTCStatement` of the descent step (published, Arthur–Clozel,
   Lemma III.6.3) gives a descent `S₀` of the stable class `S`.
3. The twisting character of `E` and the twist input give `ψ` and
   `T₀ = S₀ ⊗ (ψ ∘ det)`, conjugate self-dual, of regular highest weight and
   supercuspidal at `Q.Ps.v`.
4. Theorem 1.2 with multiplicity applies to `T₀` over `E`, with `E₀ = realIntermediateField E`
   (even degree from `Q.IsSpaced`), `K₀` the split imaginary quadratic field of the
   problem (`E₀ ⊔ K₀ = ⊤` by `realIntermediateField_sup_eq_top`), and the residue
   characteristic of `Q.Ps.v`, which is the problem's prime `p`
   (`residueCharacteristic_eq_of_natCast_mem`), split in `K₀`.
5. The restriction input gives `a`, the exponents `i k` and the spectral systems; the pole
   input makes all exponents equal to `i₀ = i 0`.
6. At almost every place the Euler polynomials of the `t k` coincide with that of `t 0`,
   so `s.eulerPolynomial v ^ a = (t 0).eulerPolynomial v ^ a`. Both polynomials have
   constant term `1` (`eulerPolynomial_eval_zero`), so `eq_of_pow_eq_pow_of_eval_zero`
   gives `s.eulerPolynomial v = (t 0).eulerPolynomial v`: `T₀` is a weak automorphic
   induction of `ξ · ((ψ η^{i₀}) ∘ N)`.
7. The untwist input gives the required descent of `S` that is a weak automorphic
   induction of `ξ`.

The published input `CuspidalSpectralRigidityTCStatement` of the descent step is not
used by this proof.

## Sources

- G. Henniart, *Sur la conjecture de Langlands locale pour `GL_n`*, J. Théor. Nombres
  Bordeaux 13 (2001), §5.5 (printed pp. 178–179) and §§5.9–5.12 (printed pp. 180–182,
  PDF pp. 15–17). Registered `henniart-2001-langlands-locale-gln-jtnb`, SHA256
  `c9db009ee2f2e561d834b9e1ef07a8b27ff40d0edd19546d3351f38f39b2dac5`.
- M. Harris, *The local Langlands conjecture for `GL(n)` over a `p`-adic field, `n < p`*,
  Invent. Math. 134 (1998), Lemma 1.6 and its proof (printed pp. 188–189), Proposition 4.8
  and the singleton case of its proof (printed pp. 201–203). Registered
  `harris-1998-local-langlands`, SHA256
  `7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`.
