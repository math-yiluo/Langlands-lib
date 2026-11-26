# The geometric endpoint of Harris's Theorem 1.2 with multiplicity

This module states the endpoint of the geometric construction of the theorem of Clozel
and Kottwitz in Henniart's form with multiplicity: the middle-degree cohomology given by
Clozel's transfer and Kottwitz's theorem, twisted by the Galois character of Clozel's
correcting abelian character (an Artin character over a totally real base field, not
necessarily one in the CM case of the endpoint; see "The route to the endpoint" below), without labelled Hodge–Tate weights, without purity
and without semisimplicity. It names semisimplification as an
input and proves that the endpoint and semisimplification imply
`Harris1998Theorem12CuspidalMultiplicityStatement` (module
`Langlands/Galois/Harris1998MultiplicityStatement`). The published
`HarrisEvenGeometricPowerStatement` of `Langlands/Galois/HarrisEvenGeometricStatement`,
with purity and labelled weights, is unchanged.

## Definitions

Namespace `Langlands.GaloisRepresentation` unless noted.

- `Langlands.Automorphic.CuspidalOperatorRealization.IsoClass.IsClozelAssociatedAt c ιL R a`:
  as `IsHenniartAssociatedAt` of `Harris1998MultiplicityStatement`, with the published
  `clozelEulerPolynomial (s.eigenvalues v hv) 1 q_v` (that is `∏ᵢ (1 − q_v^{(n−1)/2} tᵢ X)`)
  in place of Henniart's polynomial. This is Clozel's arithmetic normalization:
  geometric Frobenius has the eigenvalues `q_v^{(n−1)/2} tᵢ`, as in Clozel 1991,
  Théorème 5.3 (printed p. 132), and in the published `HarrisPowerSystem`.
- `HarrisEvenGeometricMultiplicityStatement`: the hypotheses of
  `Harris1998Theorem12CuspidalMultiplicityStatement` (CM field `E = E₀ K₀` with
  `[E₀ : ℚ]` even, `r ≥ 1`, regular highest weight, conjugate self-duality, a
  supercuspidal component at a finite place split in `K₀`). The conclusion: for every
  prime `ℓ` and isomorphism `ιℓ : ℂ ≃+* PadicAlgCl ℓ`, there are `a > 0` and a
  continuous representation `R : Objects E (PadicAlgCl ℓ)` of dimension `a (r + 1)` with
  `c.IsClozelAssociatedAt ιℓ R a`. No semisimplicity is asked for.
- `GaloisSemisimplificationStatement`, a named input: for a field `K`, a topological
  field `L` that is a topological ring, and a continuous representation
  `A : Objects K L`, there is a continuous representation `B : Objects K L` that is
  semisimple, has the dimension of `A`, has the characteristic polynomial of `A` at
  every element, and is trivial at every element at which `A` is trivial. The direct sum
  of the Jordan–Hölder factors of `A` is such a `B`. The statement is not proved here.
- `Harris1998MultiplicityOfEvenGeometricStatement`: the implication endpoint →
  semisimplification → `Harris1998Theorem12CuspidalMultiplicityStatement`.

Both this endpoint and the published `HarrisEvenGeometricPowerStatement` assume
`[E₀ : ℚ]` even, with the same binder. Compared with the published statement, the
endpoint drops the purity and monic-root conditions of `HarrisPowerSystem`, the labelled
Hodge–Tate weights `HarrisLabelledWeights` and the prescribed embedding `ι ∘ j = e`. It
fixes the coefficient prime `ℓ` and `ℂ ≅ ℚ̄_ℓ` instead of a compatible collection over a
number field. Its archimedean and local hypotheses are strengthened: regular highest
weight (`HasRegularHighestWeight`) in place of regular algebraicity
(`IsRegularAlgebraic`), which it implies by the published
`Langlands.Automorphic.CuspidalOperatorRealization.IsoClass.HasRegularHighestWeight.isRegularAlgebraic`,
and a supercuspidal component in place of
a square-integrable one at the finite place `v` split in `K₀`. The page of
`Harris1998MultiplicityStatement` compares the two local hypotheses.

## Proved results

- `henniartEulerPolynomial_eq_clozel_comp`: for `α : Eigenvalues (r + 1)` and
  `q > 0`, `henniartEulerPolynomial α q` equals `clozelEulerPolynomial α 1 q` composed
  with `C (q^{−r}) * X`. The proof composes the two scalings of the variable and uses
  `q^{r/2} q^{−r} = q^{−r/2}` for the positive real power (`Real.rpow_add`).
- `HasEulerPolynomialAt.of_charpoly_eq`: if `B` has the characteristic polynomials of
  `A` and is trivial wherever `A` is, then `B` has the Euler polynomial of `A` at every
  place where `A` has one. Triviality on inertia passes from `A` to `B`, and the Euler
  polynomial is the reversed characteristic polynomial of the pulled-back action.
- `harris1998Multiplicity_of_evenGeometric` proves
  `Harris1998MultiplicityOfEvenGeometricStatement`; only the standard axioms are used.
  Given `ℓ` and `ιℓ`, the endpoint gives `a`, `R` and a spectrum `s`. The proof twists `R`
  by the published `geometricCyclotomicPower E ℓ φ (−r)`, `φ` the continuous algebra map
  `ℚ_ℓ → ℚ̄_ℓ`. This is the twist by the `r`-th power of the cyclotomic character `χ_cyc`,
  since that character with exponent `k` is `χ_cyc^{−k}`. The rank is unchanged (same
  carrier). At every place not above `ℓ`, all but finitely many by the published
  `eventually_residueCharacteristic_not_dvd`, the published
  `HasEulerPolynomialAt.geometricCyclotomicTwist` gives the Euler polynomial
  `P_v(q_v^{−r} X)`. By the lemma above this is
  `ιℓ(henniartEulerPolynomial(s_v)^a)`. A semisimplification from the input then has
  the same Euler polynomials by `HasEulerPolynomialAt.of_charpoly_eq`.

So the reduction twists the endpoint by `χ_cyc^{n−1}` and then takes a
semisimplification. At the good places the Euler polynomials of the two normalizations
are related by the scaling `X ↦ q_v^{−(n−1)} X`, with the same multiplicity `a`; the
inverse scaling `X ↦ q_v^{n−1} X` corresponds to the twist by `χ_cyc^{1−n}`. A global
identification of Henniart's representation with the twist of the endpoint itself,
rather than with a semisimplification of that twist, would need the endpoint to be
semisimple, which it is not asked to be.

## The route to the endpoint

The endpoint is to be obtained by the geometric construction of Clozel 1991, §5, with
Kottwitz's theorem in the middle degree in place of purity. Its inputs are:

- the one-place division algebra: the published `ClozelOnePlaceExistenceStatement`
  (namespace `Langlands.Shimura.FiniteUnitary`, module
  `Langlands/Shimura/Unitary/ClozelOnePlaceExistenceStatement`), available for even
  `[E₀ : ℚ]` with one split place carrying a discrete series component (Clozel 1991,
  Théorème 5.7);
- Clozel's transfer of `Π` to the unitary group of that division algebra, with the
  occurrence of the transferred representation in the middle-degree cohomology of the
  associated Shimura varieties;
- Kottwitz's theorem without purity: `CMHarrisKottwitzTraceIdentityStatement` and
  `CMHarrisKottwitzRegularMiddleDegreeStatement` (module
  `Langlands/Shimura/PEL/HarrisTaylorCMKottwitzRegularStatement`). The vanishing outside
  the middle degree comes from the theorems of Vogan and Zuckerman for a regular highest
  weight, not from purity.

In the rest of this section the notation is Clozel's: `F` is his totally real base
field, `F_c` his CM field, `E = R F_c` his reflex field, `r^T` the unramified parameter normalized by
his (5.3), printed p. 131, `r^T_v(Φ_v) = q_v^{(1−n)/2} t_{π,v}` with `Φ_v` a geometric
Frobenius and `t_{π,v}` the Hecke matrix, and `τ_p` the local component at `p` of the
representation of the similitude group (Kottwitz writes `π_p`).

Clozel identifies the reflex field of the Shimura varieties with the compositum
`F_c R` of his CM field and the reflex field of the CM type; his argument uses `n > 2`
(§5.2, printed p. 134). For the CM type induced from `K₀`, the published
`Langlands.Global.CMType.clozelReflexField_inducedFromImaginaryQuadratic` computes
this compositum: it is the image of the CM field. The field of the actual Kottwitz
cocharacter class is computed separately by the published
`Langlands.Shimura.CentralSimpleUnitaryData.kottwitzCocharacterReflexField_eq_distinguishedImage`
(module `Langlands/Shimura/Unitary/CocharacterReflexField`): under
`3 ≤ n ∨ ∃ τ, τ ≠ CH.distinguished` it is the image of the CM field under the
distinguished embedding, a copy of the base field of the endpoint. That hypothesis also
covers `n = 2` here: `[E₀ : ℚ]` is even and positive, so `E₀` (Clozel's `F`) has a
second real embedding, as in the published
`Langlands.Shimura.FiniteUnitary.realReflexField_eq_distinguishedImage_of_onePlaceParity`
(module `Langlands/Shimura/Unitary/ClozelOnePlaceExistenceReduction`).

Kottwitz's polynomial `P(τ_p, E_w)` is the characteristic polynomial of
`[(r ∘ φ_w(τ_p))(Φ_w)] · q_w^{(n−1)/2}` (Clozel's (5.10), printed p. 136). This is
Kottwitz's definition, printed p. 656: `V(π_p, E_v) = (r ∘ φ_{E_v}(π_p)) ⊗ Z`, where `Z`
takes the value `(√p)^{[E_v : ℚ_p] dim S_K}` at geometric Frobenius, and `dim S_K = n − 1`
in the signature `(n − 1, 1)` used here. By Kottwitz's theorem and the concentration in
the middle degree, `Φ_w` has characteristic polynomial `P(τ_p, E_w)^a` on `W^{n−1}`
(Clozel's (5.12), printed p. 136, and printed p. 142).

Over a totally real base field (Clozel's §5.2, Théorème 5.3), (5.31), printed p. 141,
computes the parameter action alone: `(r ∘ φ_w(τ_p))(Φ_w) = r^T(Φ_w) q_w^{(n−1)/2}
α_{E,w}(ϖ_w)`, with `α_E` an Artin character of `𝔸_E^×`. So `P(τ_p, E_w)` is the
characteristic polynomial of `r^T(Φ_w) q_w^{n−1} α_{E,w}(ϖ_w)`. In the same-field case
(`E_w = F_v`, so `q_w = q_v` and `r^T(Φ_w) = q_w^{(1−n)/2} t_{π,v}`) its eigenvalues are
`q_w^{(n−1)/2} tᵢ α_{E,w}(ϖ_w)`. Clozel's system is `W = W^{n−1} ⊗ α_E` (printed
p. 142), where class field theory reads the Artin character as a Galois character. To
give the conclusion of Théorème 5.3, `trace r_λ(Φ_w^m) = a · trace r^T(Φ_w^m) q_w^{m(n−1)}`,
this Galois character must take the value `α_{E,w}(ϖ_w)^{−1}` at `Φ_w`, cancelling the
scalar `α_{E,w}(ϖ_w)`. The eigenvalues of `Φ_w` on `W` are then the `q_w^{(n−1)/2} tᵢ`,
each with multiplicity `a`.

The endpoint lies in the CM case (Clozel's §5.3, Théorème 5.7, printed pp. 142–144),
where Clozel argues directly with the conjugate self-dual `π_c`. At an archimedean place
`u` the central character of `π_c` is `z^{P_u} z̄^{Q_u}` ((5.32)–(5.33), printed p. 143).
Let `P = Σ_{u | ∞} P_u`. The character `χ` used to extend the descended representation
to the similitude group must satisfy `χ_∞(−1) = (−1)^P`. Clozel takes `χ_∞ = 1` for `P`
even and `χ_∞(x) = x` for `P` odd. Correspondingly he lets `S(ℂ) ≅ ℂ^×` act on the
coefficient system trivially, or by `z ↦ z^{−1}`. For `P` odd, `χ` is not an Artin
character, and the coefficient system has weight `1` instead of `0`. This translates the
weights in (5.11)–(5.12) (printed pp. 143–144). So in the CM case the abelian character
that corrects `W^{n−1}` in the place of `α_E` need not be an Artin character, and the
weights are translated by the weight of the coefficient system. The hypotheses of the endpoint do not fix the parity of `P`; even `[E₀ : ℚ]` concerns the
one-place division algebra. Théorème 5.7 has the conclusion of Théorème 5.3, with `r^T`
attached to `π_c` as in §5.1. One input of the endpoint, beside Clozel's transfer and the
occurrence in the middle degree, is the following good-place Frobenius comparison: the twist of
`W^{n−1}` by the `λ`-adic Galois character attached to this correcting character has, at almost every
place, the eigenvalues `q_w^{(n−1)/2} tᵢ` of `IsClozelAssociatedAt`, each with
multiplicity `a`. There is no rank-one case. This module states the endpoint with these
inputs as the specification of the geometric construction and proves none of them; its
proved results are the reduction above and its two lemmas.

## Sources

- G. Henniart, *Sur la conjecture de Langlands locale pour `GL_n`*, J. Théor. Nombres
  Bordeaux 13 (2001), §5.5, printed pp. 178–179: the semisimple `Σ` with
  `L(Σ_v, s) = L(Π_v, s + (n − 1)/2)^a` for a fixed `ℓ` and `ℂ ≅ ℚ̄_ℓ`. Registered
  `henniart-2001-langlands-locale-gln-jtnb`, SHA256
  `c9db009ee2f2e561d834b9e1ef07a8b27ff40d0edd19546d3351f38f39b2dac5`.
- L. Clozel, *Représentations galoisiennes associées aux représentations
  automorphes autoduales de `GL(n)`*, Publ. Math. IHÉS 73 (1991), (5.2)–(5.3), printed
  p. 131; Théorème 5.3, printed p. 132; the reflex field `E = F_c R` for `n > 2`, §5.2,
  printed p. 134; (5.10) and (5.12), printed p. 136; (5.31),
  printed p. 141; the end of the proof of Théorème 5.3 on printed p. 142
  (`P(Φ_w, W^{n−1}) = P(τ_p, E_w)^a` and `W = W^{n−1} ⊗ α_E`); and §5.3, Théorème 5.7
  and its proof, printed pp. 142–144, with (5.32)–(5.33). Registered
  `clozel-1991-selfdual-galois`, SHA256
  `9de7c13c9ae108e481de170327a06e44845cf87a6aabc1d5600176ee695e91ac`.
- R. E. Kottwitz, *On the λ-adic representations associated to some simple Shimura
  varieties*, Invent. Math. 108 (1992), the definition of `V(π_p, E_v)`, printed p. 656;
  Theorem 1, printed p. 657; and the remark on regular highest weight, printed p. 658.
  Registered
  `kottwitz-1992-lambda-adic-simple-shimura`, SHA256
  `749af5541a59187e6f9d1089dec9a0e591a2059173da739c7384ff3a7d0dd799`.
