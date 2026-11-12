# Taylor's removal of the cohomological multiplicity

Author: Worker 34. This module states, as an unproved `Prop`, the Galois
theoretic core of Taylor's argument: a `λ`-adic representation whose
Frobenius characteristic polynomials are `m`-th powers, and whose Hodge-Tate
decomposition at a place above `ℓ` has `n` distinct twists each occurring `m`
times, is up to semisimplification the `m`-th power of an `n`-dimensional
representation. Clozel's and Kottwitz's constructions give a representation
`W_λ` with the first property; this statement removes the multiplicity `m`.

## Source

M. Harris, *Supercuspidal representations in the cohomology of Drinfel'd upper
half spaces; elaboration of Carayol's program*, Invent. Math. 129 (1997),
75-119. Registered original `harris-1997-drinfeld-cohomology`, SHA256
`aea284b917442459028b710dbfd9ae537631490504f3bc6d54a1e76ee697e0d9`.

- Theorem 2, printed p.100 ("due to Kottwitz, Clozel, and Taylor"), and the
  following paragraph: "Taylor's contribution, contained in an unpublished
  letter to Clozel [T], was to verify that the semi-simplification of
  `W_ℓ(GG, Gπ)` decomposes as the direct sum of `m` copies of a single
  `n`-dimensional Galois representation, where `m` is the multiplicity."
- "Sketch of the proof of Taylor's theorem", printed pp.102-103 (checked
  against the page images). `L` is a number field, `λ` a prime of `L` of
  residue characteristic `ℓ`, `T_ℓ` the primes of `𝒦` dividing `ℓ`, and
  `W_λ = [H^{n-1}(S_N, L_λ)[Gπ] ⊗ GJL(π_v)^*]^{GG}_{SS(𝒦)}` is a
  semisimplification. "The data Taylor requires from [C3] and [K] are the
  existence, for every place `v` of `𝒦`, `v ∉ T`, of a monic polynomial
  `P_v(X) ∈ L[X]` of degree `n`, and a continuous representation
  `r_λ : Γ → GL(W_λ)`, unramified outside `T ∪ T_ℓ`, such that, for
  `v ∉ T ∪ T_ℓ`, `r_λ(Frob_v)` has characteristic polynomial `P_v(X)^m`",
  with `Frob_v` a geometric Frobenius. For `v ∈ T_ℓ`, Faltings' theorem gives
  the Hodge-Tate decomposition `W_λ ⊗_{ℚ_ℓ} C_v ≅ ⊕_{i=1}^{n} L_λ^m ⊗_{ℚ_ℓ}
  C_v(1 - i)` as `Γ_v`-modules. The conclusion: "`W̄_λ = U_λ^m`, for some
  `Γ`-module `U_λ` defined over a finite extension of `L_λ`. Standard
  arguments then show that the `U_λ` fit into a compatible family as `λ`
  varies."

The original letter of Taylor [T] has not been read; it was not available.
Only Harris's printed sketch is used.

## Library objects used

- `LambdaAdic K L lam`, `Objects`, `characteristicPolynomial`, `atFinitePlace`
  (published `Langlands/Galois/CoefficientRepresentation`): continuous
  representations of `Gal(K̄/K)` on finite-dimensional vector spaces over a
  topological field, their characteristic polynomials, and restriction to a
  decomposition group through the completion `K_v`.
- `HasEulerPolynomialAt`, `residueCharacteristic` (published
  `Langlands/Galois/CompatibleFamily`): unramifiedness at `v` with a geometric
  Frobenius lift `g` and Euler polynomial `det(1 - ρ(g) X)`, which is the
  reverse of the characteristic polynomial.
- `CompletionPadic.residuePrime`, `padicAlgebra`, `padicAlgebraAt`,
  `padicFieldAt` (published `Langlands/Global/CompletionPadic` and
  `CompletionPadicTower`): the canonical `ℚ_ℓ`-algebra structures of the
  completions and their finite dimension.
- `HodgeTate.HasHodgeTateDecomposition` (from
  `Langlands/Galois/Local/HodgeTate`, in this candidate).
- Mathlib's `moduleTopology`.

## Definitions

- `HasHodgeTateDecompositionAt lam A v hv n m k`: for a place `v` of `K` with
  the same residue prime `ℓ` as `λ` (`hv`), with `K_v` and `L_λ` regarded as
  `ℚ_ℓ`-algebras, the restriction `atFinitePlace v A` has a Hodge-Tate
  decomposition `C_v ⊗_{ℚ_ℓ} W ≅ ⊕_{i<n} ((C_v ⊗_{ℚ_ℓ} L_λ)(k i))^m`, linear over
  `C_v` and `L_λ` and equivariant for `Gal(K̄_v/K_v)`.
- `TaylorMultiplicityRemovalStatement`: for all number fields `K` and `L`, a
  finite place `λ` of `L`, `A : LambdaAdic K L λ` (Harris's `r_λ` on `W_λ`),
  natural numbers `n` and `m`, a finite set `T` of places of `K`,
  polynomials `P_v ∈ L[X]` and twists `k : Fin n → ℤ`, if
  1. `m > 0` and `k` is injective;
  2. for `v ∉ T`, `P_v` is monic of degree `n`;
  3. for `v ∉ T` whose residue characteristic differs from that of `λ`
     (`v ∉ T ∪ T_ℓ`), `A` is unramified at `v` with Euler polynomial the
     reverse of `P_v^m` (characteristic polynomial `P_v(X)^m` of geometric
     Frobenius);
  4. for some place `v` with residue prime `ℓ`,
     `HasHodgeTateDecompositionAt lam A v hv n m k`;

  then there are a field `Λ` with an `L_λ`-algebra structure, finite
  dimensional over `L_λ` and topologized by `moduleTopology L_λ Λ` (its unique
  Hausdorff vector-space topology), and a continuous representation
  `U : Objects K Λ` such that
  - `U` has rank `n`;
  - for every `g ∈ Gal(K̄/K)`, the image in `Λ[X]` of the characteristic
    polynomial of `A(g)` is the `m`-th power of the characteristic polynomial
    of `U(g)`;
  - for `v ∉ T` with residue characteristic different from that of `λ`, `U`
    is unramified at `v` with Euler polynomial the reverse of `P_v`.

## Faithfulness and conventions

- **Semisimplification.** Harris's `W_λ` is already a semisimplification, and
  the conclusion `W̄_λ = U_λ^m` is an isomorphism of semisimple
  representations. The Library has no semisimplification of Galois
  representations, so the conclusion is stated through characteristic
  polynomials: by the Brauer-Nesbitt theorem (characteristic zero), equality
  of the characteristic polynomials of `A ⊗ Λ` and `U^m` for all `g` is
  equivalent to `(A ⊗ Λ)^{ss} ≅ (U^{ss})^m`. Replacing `U` by `U^{ss}` changes
  nothing in the statement.
- **Compatible family.** The last conclusion is Harris's remark that the `U_λ`
  "fit into a compatible family": their Frobenius polynomials at `v ∉ T ∪ T_ℓ`
  are `P_v`, independent of `λ`. The representations `U_λ` are over finite
  extensions of `L_λ`, not over `L_λ` itself, so they are not assembled into
  a Library `Collection` here.
- **Twists.** Harris's decomposition is the case `k i = -i` for `i : Fin n`
  (the twists `C_v(1 - i)`, `i = 1, …, n`, of the trivial coefficient system).
  For the general coefficient systems of Harris (1999), Theorem 5.7(i), the
  twists are distinct but not consecutive. The statement allows any injective
  `k`; Taylor's argument only uses that the `n` twists are distinct and that
  each occurs `m` times.
- **One place above `ℓ`.** Faltings' theorem gives the decomposition at every
  `v ∈ T_ℓ`; Taylor's argument fixes one such `v` ("We assume `v ∈ T_ℓ`"). The
  hypothesis asks for one place.
- **Base field.** Harris's base field is the CM field `𝒦`. Taylor's argument
  uses no property of `𝒦` beyond being a number field (Chebotarev density and
  Sen's theorem at one place), and the statement is made for every number
  field `K`.
- **Geometric Frobenius.** As in the published `HasEulerPolynomialAt`.
- **Universes.** `Λ` lies in the universe of `L` and the carrier of `U` in that
  of `A`.

## Source discrepancy in the proof sketch

Harris prints (p.103): "Let `B ⊃ T` be a Borel subgroup and a maximal torus of
`H`, … and let `N ⊂ H` denote the stabilizer of the pair `(B, T)` in `H`. Then
`H = H⁰ · N = N · H⁰` and `H⁰ ∩ N = 1`." The last equality is false as
printed: `T ⊂ H⁰` stabilizes the pair `(B, T)`, so `T ⊂ H⁰ ∩ N`. What holds,
for connected reductive `H⁰`, is `H⁰ ∩ N = N_{H⁰}(B, T) = T`. The statement
above is not affected: it records hypotheses and conclusion only, and no
proof is given here. A proof must not use the printed equality.

The sketch also asserts that `H⁰` "is reductive by Hodge-Tate theory". For
the semisimple `W_λ` of the source, reductivity follows from semisimplicity of
the representation; this remark is not used here.

## Scope

- Only the statement is formalized. Sen's theorem, the Zariski closure of the
  image, Chebotarev density and Brauer-Nesbitt are not formalized.
- The application to Shimura varieties, where Kottwitz's and Clozel's results
  give the hypotheses and Faltings' theorem the Hodge-Tate decomposition, is a
  separate obligation (Harris 1997, Theorem 2; Harris 1999, Theorem 5.7(i)).
