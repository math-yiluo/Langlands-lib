# Harris (1998), Theorem 1.2, with multiplicity: Henniart's form

This module states the theorem of Clozel and Kottwitz in the form with multiplicity
of Henniart 2001, §5.5, under three added hypotheses: those that the variant of the
construction of Harris's Proposition 4.8 taking this theorem as input supplies. It
defines Henniart's normalized Euler polynomial and the association of a continuous
`ℓ`-adic representation with a cuspidal class with multiplicity `a`. Nothing here
proves the theorem.

## Source

G. Henniart, *Sur la conjecture de Langlands locale pour `GL_n`*, J. Théor. Nombres
Bordeaux 13 (2001), §5.5, printed pp. 178–179 (PDF pp. 13–14). Henniart states the
starting global result of Harris 1998, §4, "a theorem essentially due to Clozel,
using the work of Kottwitz". Let `F₊` be totally real, `I` imaginary quadratic,
`F = F₊ I` with complex conjugation `c`, `ℓ` a prime and `ℂ ≅ ℚ̄_ℓ`.

> Théorème. Let `Π` be a cuspidal automorphic representation of `GL_n(𝔸_F)` such that
> (i) `Π^c ≅ Π^∨`; (ii) `Π` is algebraic at infinity and regular; (iii) at at least one
> finite place of residue characteristic split in `I`, the component of `Π` is a
> discrete series. Then there are an integer `a ≥ 1` and a semisimple `ℓ`-adic
> representation `Σ : Gal(F̄/F) → GL_{an}(ℚ̄_ℓ)` such that at almost every finite place
> `v` of `F`, `L(Σ_v, s) = L(Π_v, s + (n − 1)/2)^a`.

Henniart's Remark (p. 179) says that Harris's earlier article [Ha1] (Harris 1997,
Invent. Math. 129, in Henniart's bibliography, p. 187) presents an argument of Taylor for
taking `a = 1`, which needs `ℓ`-adic Hodge–Tate theory, and that `a = 1` is not needed for
his Theorem 5.1 (the construction of Harris 1998, §4); his §§5.9–5.12 use the theorem
with this `a`. Harris 1998, printed p. 185, credits the argument for `a = 1` in its
Theorem 1.2 to Taylor and refers to the earlier article for it.

## The three added hypotheses

The statement adds three hypotheses to Henniart's. They are not part of his §5.5;
they are the hypotheses that the variant of the construction of Harris 1998,
Proposition 4.8, in which this theorem with multiplicity replaces Theorem 1.2,
supplies at every application.

- **`[E₀ : ℚ]` even.** Henniart 2001 applies the theorem only over fields containing
  the real quadratic field `R` of §5.1 (printed p. 177), so the totally real subfield
  has even degree. Clozel 1991, Théorème 5.7 (printed p. 142), then needs only one
  split place with a discrete series component; a second one is required when
  `2 | n`, `4 ∤ n` and `d = [F₊ : ℚ]` is odd.
- **Supercuspidal component.** Every application of the theorem inside the
  construction is to a representation with a supercuspidal component at the split
  auxiliary place (Harris 1998, Proposition 4.8, printed p. 201, and the inductive
  hypothesis in its proof, printed p. 202). The hypothesis is stronger than
  Henniart's discrete series hypothesis (iii).
- **Regular highest weight.** `c.HasRegularHighestWeight`
  (`Langlands/Automorphic/RegularHighestWeight`): the highest weight is strictly
  decreasing at every embedding index, so the weights at each complex embedding are
  at distance at least `2`. This implies the published `IsRegularAlgebraic`
  (Henniart's (ii)). The printed Proposition 4.8 does not supply it: it assumes only
  that the inducing Hecke character is relatively regular, and Harris's Remark
  (printed p. 202) notes that its infinity type may even be chosen so that, at a
  selected archimedean place, the representations of the induction have the
  infinitesimal character of a one-dimensional representation, whose highest weight
  is constant. The variant obtains regular highest weight by an additional choice:
  the infinity type of the inducing Hecke character has exponents at distance at
  least `2` at each complex place. Regular highest weight is the hypothesis of
  Kottwitz 1992, remark after Theorem 1 (printed p. 658), under which the cohomology
  of his Shimura varieties is concentrated in the middle degree `dim S_K`, by the
  theorems of Vogan and Zuckerman (1984, Theorems 5.5 and 5.6). Kottwitz's groups (§1,
  printed pp. 654–655) allow products of unitary groups of signatures `(n(i), n(i'))`;
  the construction uses the signature of Clozel 1991, Hypothèse 5.1 (printed p. 131):
  `(n − 1, 1)` at one real place and definite at the others. For it `dim S_K = n − 1`,
  and the argument passes to `SU(n − 1, 1)`; see the page of
  `Langlands/Automorphic/RegularHighestWeight`.

The rank-one case `n = 1` is excluded (`1 ≤ r`).

## Definitions

All in namespace `Langlands.GaloisRepresentation` unless noted.

- `henniartEulerPolynomial α q`: for `α : Eigenvalues n` and a natural number `q`, the
  polynomial `α.eulerPolynomial.comp (C (q^{-(n-1)/2}) * X)`, that is
  `∏ᵢ (1 − q^{−(n−1)/2} αᵢ X)`. Its inverse at `X = q^{−s}` is
  `L(π_v, s + (n − 1)/2)` when `α` are the Satake parameters of `π_v`. The real power
  `q^{−(n−1)/2}` is `Real.rpow`, the positive root.
- `Langlands.Automorphic.CuspidalOperatorRealization.IsoClass.IsHenniartAssociatedAt c ιL R a`,
  for a topological field `L`, a ring homomorphism `ιL : ℂ →+* L` and a continuous
  representation `R : Objects E L` of `Gal(Ē/E)` (the published objects of
  `Langlands/Galois/CoefficientRepresentation`): some spectrum `s` with the published
  `HasSpectralSystem c s` (local factor carriers in universe `uW`) is such that for all
  but finitely many finite places `v` and `v ∉ s.exceptional`, the published
  `HasEulerPolynomialAt R v` holds with the polynomial
  `(henniartEulerPolynomial (s.eigenvalues v hv) q_v ^ a).map ιL`, `q_v` the published
  `residueCardinality v`. `HasEulerPolynomialAt` (`Langlands/Galois/CompatibleFamily`)
  says that `R` is trivial on the actual inertia group at `v` and that
  `det(1 − R(g) X)` is that polynomial for a lift `g` of geometric Frobenius.

## The statement

`Harris1998Theorem12CuspidalMultiplicityStatement` quantifies over

- a number field `E : Type uE` with `IsCMField E` and `CompactSpace (AdeleQuotient E)`,
  as in the published `Harris1998Theorem12CuspidalStatement`;
- intermediate fields `E₀ K₀` of `E/ℚ` with `E₀` totally real, `K₀` of degree `2` and
  totally complex, `E₀ ⊔ K₀ = ⊤` (that is `E = E₀ K₀`), and `Even [E₀ : ℚ]`;
- `r ≥ 1`, an irreducible cuspidal class `c` of rank `n = r + 1` and a finite place `v`.

Hypotheses: `c.HasRegularHighestWeight`, `c.IsConjugateSelfDual` (the published
`π^∨ ≅ π ∘ c` for `IsCMField.complexConj E`, Henniart's (i)), a supercuspidal
component of `c` at `v` (`HasSupercuspidalComponent`, local factor carriers in `uW`),
and `Harris.IsSplitImaginaryQuadratic (residueCharacteristic v) K₀`.

Conclusion: for every prime `ℓ` and every isomorphism of fields
`ιℓ : ℂ ≃+* PadicAlgCl ℓ` (Mathlib's algebraic closure `ℚ̄_ℓ` of `ℚ_ℓ`, with the topology
of its spectral norm), there are a natural number `a` and a continuous representation
`R : Objects E (PadicAlgCl ℓ)` of `Gal(Ē/E)` with carrier in universe `uV` such that
`0 < a`, `R` has dimension `a (r + 1)` over `ℚ̄_ℓ`, `R` is semisimple (Mathlib's
`Representation.IsSemisimpleRepresentation`), and
`c.IsHenniartAssociatedAt ιℓ R a`. So at almost every finite place `v`,
`L(R_v, s) = L(c_v, s + (n − 1)/2)^a` through `ιℓ`.

## Conventions and scope

- **Normalization.** Henniart's: geometric Frobenius at `v` has the eigenvalues
  `q_v^{−(n−1)/2} tᵢ`, with `tᵢ` the Satake parameters, and the Euler polynomial is
  `det(1 − Frob_v X)` (the published `eulerPolynomial`). Clozel's representation of
  1991, Théorème 5.3 (printed p. 132), is Henniart's tensored with the `(1 − n)`-th
  power of the cyclotomic character: since the cyclotomic character takes the value
  `q_v^{−1}` at geometric Frobenius, its eigenvalues are `q_v^{(n−1)/2} tᵢ`, the
  normalization of the published `clozelEulerPolynomial α 1 q`. The multiplicity `a`
  is the same.
- **Coefficients and semisimplicity.** As in Henniart's statement, the prime `ℓ` and
  the isomorphism `ℂ ≅ ℚ̄_ℓ` are fixed first, and the witness is one continuous
  semisimple representation with coefficients in `ℚ̄_ℓ` whose Euler polynomials are
  compared through that isomorphism. No compatibility between different primes `ℓ` is
  asserted, and no number field of coefficients is asked for.
- **Unramified matching only.** No ramified local compatibility is asserted, and no
  statement about the place `v` is made.
- **No purity.** No weight of the Frobenius eigenvalues is asserted.

## Relation to the published form of Theorem 1.2

The published `Harris1998Theorem12CuspidalStatement` (module
`Langlands/Galois/Harris1998ExistenceStatement`) and the statement here are
different statements; the Library claims no implication between them.

1. **Eigenvalues.** The published conclusion is a finite family of compatible
   collections over a number field of coefficients, each pure of some weight `w_k`,
   whose Euler polynomials match the spectrum only after Harris's unitary
   normalization `β ↦ β/|β|` of each reciprocal root. It fixes the
   Frobenius eigenvalues of a summand only up to that normalization, as
   `q_v^{w_k/2} tᵢ`. The statement here fixes them exactly, as `q_v^{−(n−1)/2} tᵢ`.
   For one summand the two agree after the twist by the `(w_k + n − 1)/2`-th power of
   the cyclotomic character, which exists when `w_k ≡ n − 1 (mod 2)`. The published
   statement does not determine the parity of `w_k`.
2. **Local hypothesis.** The published hypothesis is a square-integrable component at
   the split place; the hypothesis here is a supercuspidal component. The Library
   has local theorems in the direction supercuspidal to square-integrable
   (`unitarizableSupercuspidal_isSquareIntegrable` in
   `Langlands/Representation/Classification/UnitarySupercuspidalInductionTempered` and
   `supercuspidal_isEssentiallySquareIntegrable` in
   `Langlands/Representation/RankinSelberg/TemperedTwistSupercuspidalPoleClassification`);
   whether they give `HasSquareIntegrableComponent` for a cuspidal class is not
   examined here.
3. The statement here also adds `[E₀ : ℚ]` even, regular highest weight and `n ≥ 2`,
   fixes the coefficient prime `ℓ` and `ℂ ≅ ℚ̄_ℓ` instead of a compatible system over a
   number field, asks for semisimplicity, and drops purity and the multiplicity one of
   the published conclusion.

## Sources

- G. Henniart, *Sur la conjecture de Langlands locale pour `GL_n`*, J. Théor. Nombres
  Bordeaux 13 (2001), §5.1 (printed p. 177), §5.5 (printed pp. 178–179, PDF pp.
  13–14). Registered `henniart-2001-langlands-locale-gln-jtnb`, SHA256
  `c9db009ee2f2e561d834b9e1ef07a8b27ff40d0edd19546d3351f38f39b2dac5`.
- M. Harris, *The local Langlands conjecture for `GL(n)` over a `p`-adic field,
  `n < p`*, Invent. Math. 134 (1998), Theorem 1.2, printed p. 185; Proposition 4.8,
  its proof and the Remark in the proof, printed pp. 201–202. Registered
  `harris-1998-local-langlands`, SHA256
  `7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`.
- M. Harris, *Supercuspidal representations in the cohomology of Drinfel'd upper half
  spaces; elaboration of Carayol's program*, Invent. Math. 129 (1997), 75–119, cited as
  [Ha1] by Henniart. Registered `harris-1997-drinfeld-cohomology`.
- L. Clozel, *Représentations galoisiennes associées aux représentations
  automorphes autoduales de `GL(n)`*, Publ. Math. IHÉS 73 (1991), Théorème 5.3
  (printed p. 132, PDF p. 37), Hypothèse 5.1 (printed p. 131) and Théorème 5.7 (printed
  p. 142, PDF p. 47). Registered
  `clozel-1991-selfdual-galois`, SHA256
  `9de7c13c9ae108e481de170327a06e44845cf87a6aabc1d5600176ee695e91ac`.
- D. A. Vogan, Jr. and G. J. Zuckerman, *Unitary representations with non-zero
  cohomology*, Compositio Math. 53 (1984), Theorems 5.5 and 5.6, printed pp. 74–75.
  Registered `vogan-zuckerman-1984-unitary-nonzero-cohomology`, SHA256
  `ccaaf5ad243ccb85d3db629ff7677ca5b80b7e2d71e502d21fa1b773863b78a4`.
- R. E. Kottwitz, *On the `λ`-adic representations associated to some simple Shimura
  varieties*, Invent. Math. 108 (1992), §1, printed pp. 654–655, and remark after
  Theorem 1, printed p. 658.
  Registered `kottwitz-1992-lambda-adic-simple-shimura`, SHA256
  `749af5541a59187e6f9d1089dec9a0e591a2059173da739c7384ff3a7d0dd799`.
