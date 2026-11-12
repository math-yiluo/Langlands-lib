# Clozel's compatible systems for conjugate self-dual representations

Author: Worker 34. This module states Clozel's existence theorems for
compatible systems of `λ`-adic representations attached to cuspidal regular
algebraic representations `π_c` of `GL(n)` over a CM field with
`π_c ≅ σ(π̃_c)`, before the multiplicity is removed. The statements are `Prop`
definitions; nothing here proves them. They are the inputs that Harris (1998,
Theorem 1.2) and Harris (1999, Theorem 5.9(i)) cite, together with Kottwitz's
zeta functions and Taylor's removal of the multiplicity.

## Sources

- L. Clozel, *Représentations galoisiennes associées aux représentations
  automorphes autoduales de GL(n)*, Publ. Math. IHÉS 73 (1991). Registered
  original `clozel-1991-selfdual-galois`, SHA256
  `9de7c13c9ae108e481de170327a06e44845cf87a6aabc1d5600176ee695e91ac`. Read and
  checked against the page images: §5.1, (5.1)-(5.3) and Définition 5.2
  (p.131); Théorème 5.3 and Corollaires 5.4.1-5.4.2 (p.132); §5.3 and
  Théorème 5.7 (p.142).
- L. Clozel, *On the cohomology of Kottwitz's arithmetic varieties*, Duke
  Math. J. 72 (1993). Registered original `clozel-1993-kottwitz-cohomology`,
  SHA256 `cfc3a238c923958759ad6d5b0deedffe47b34c3749630463730b066b9402491b`.
  Read: §2.3 (pp.764-766), §2.4-2.5 (pp.766-771), §2.6 with Theorems 2.5 and
  2.6 (pp.771-772, checked against the page image).

### Clozel (1991)

(5.2)-(5.3), p.131: for an unramified `π_v`, `r_v(Φ_v) = t_{π,v}` is the Hecke
matrix, `Φ_v` a geometric Frobenius and local reciprocity sending `Φ_v` to a
uniformizer, and `r_v^T(Φ_v) = q_v^{(1-n)/2} t_{π,v}`.

Théorème 5.3, p.132 (totally real case). There exist (i) a number field
`L ⊂ ℂ`, (ii) a finite set `S` of primes, (iii) an integer `a > 0`, (iv) a
compatible system `W = (W_λ, r_λ)` of `λ`-adic representations of `Gal(Ē/E)`,
`λ` running over the places of `L`, such that "`W` est pur de poids `n − 1`,
les représentations `W_λ` sont non ramifiées en dehors des places divisant
`S` et, pour `p ∉ S` et `λ ∤ p`, on a, pour toute place `w` de `E` divisant
`p`, `trace r_λ(Φ_w^m) = a · trace r^T(Φ_w^m) q_w^{m(n−1)}` pour tout `m ≥ 0`."

§5.3 and Théorème 5.7, p.142 (CM case). `F_c` is a CM field, `F` its maximal
real subfield, `σ` the nontrivial element of `Gal(F_c/F)`, `Σ` a CM type of
`F_c` and `E = R F_c` the reflex field of §5.1. "Soit `π_c` une représentation
cuspidale, algébrique, régulière, de `GL(n, 𝔸_{F_c})` vérifiant les conditions
suivantes : (i) `π_c ≅ σπ̃_c` ; (ii) il existe une place `v₀` de `F` (et une
seconde place `v₁ ≠ v₀` si `2 | n`, `4 ∤ n` et `d` est impair) déployée(s)
dans `F_c` telle(s) que `(π_c)_{v₀}` (et `(π_c)_{v₁}` s'il y a lieu) appartienne
à la série discrète. Alors les conclusions (i)-(iv) du théorème 5.3 sont
vraies pour `π_c`." Here `(π_c)_v = ⊗_{w | v} π_{c,w}` and `d = [F : ℚ]`.

### Clozel (1993)

Theorem 2.6, p.772: "Assume `π_c` is a cuspidal, algebraic, regular
representation of `GL(n, 𝔸_{F_c})` such that `π_c ≅ σπ̃_c`, and
`(π_c)_{u₀} = ⊗_{v | u₀} (π_c)_v` is supercuspidal for a place `u₀` of `F` split in
`F_c`. Then there exists a compatible system of `λ`-adic representations of
`Gal(Ē/E)` associated to `π_c`." The proof (p.772, for Theorem 2.5) replaces `π`
by the residual representation `J(π, 2)` of `GL(2n)`, so that `4 | 2n`; the
supercuspidal hypothesis makes its component at `u₀` elliptic ("If `π_{u₀}` is
only square-integrable, `J(π, 2)_{u₀}` is no longer elliptic in general"). §2.6
opens: "We describe the new results rather informally, the details being as
in [10]", and for Theorem 2.5 "For the precise formula relating `π` and
`(W_λ, r_λ)`, we refer to [10, Thm. 5.3]."

## Library objects used

- `CuspidalOperatorRealization.IsoClass K r`, `IsRegularAlgebraic`,
  `IsConjugateSelfDual` (`π^∨ ≅ π ∘ c` for the CM conjugation, equivalently
  `π_c ≅ σπ̃_c`), `HasSupercuspidalComponent` and `HasSpectralSystem`
  (published), and `HasSquareIntegrableComponent` (published
  `Langlands/Automorphic/SquareIntegrableComponent`, introduced with the
  Harris 1998 Theorem 1.2 statement).
- `Harris.conjPlace K v`: `c(v)`. A place `v` of `K` with `c(v) ≠ v` lies above a
  place of `F` split in `K`, and `v`, `c(v)` are the two places above it.
- `CMType K` (published) and `CMType.clozelReflexField`,
  `CMType.toClozelReflexField` (from `Langlands/Global/CMReflexField`, in this
  candidate).
- `Collection`, `HasEulerPolynomialAt`, `HasRank`, `IsPureCompatible`,
  `residueCharacteristic`, `residueCardinality` (published
  `Langlands/Galois/CompatibleFamily`), `unitaryEulerPolynomial` (published
  `Langlands/Galois/UnitaryNormalization`), `Eigenvalues.power` and
  `Eigenvalues.eulerPolynomial` (published).
- Mathlib's `Ideal.inertiaDeg` for the residue degree `f(w | v)`.

## Definitions

All in `Langlands.GaloisRepresentation`. Let `E = Σ.clozelReflexField ι₀`, a
number field, made a `K`-algebra by `ι₀`.

- `clozelEulerPolynomial α f q = ∏_{α} (1 − q^{(n−1)/2} α^f X)` for `n` complex
  eigenvalues `α`. For a place `w` of `E` above a place `v` of `K` with residue
  degree `f` and `q = q_w = q_v^f`, Clozel's `q_w^{n−1} r^T(Φ_w)` is
  `q_w^{n−1} (q_v^{(1−n)/2} t_{π,v})^f = q_w^{(n−1)/2} t_{π,v}^f`; this polynomial is
  its `det(1 − · X)`.
- `IsClozelSystem Σ ι₀ c ι S a W`: Clozel's conclusions for a cuspidal class `c`
  of `GL_n(𝔸_K)`, `n = r + 1`, with `L`, `ι : L → ℂ`, `S : Finset ℕ`, `a` and a
  collection `W` of `λ`-adic representations of `Gal(Ē/E)` over all finite
  places of `L`:
  - `0 < a`; every `W_λ` has rank `a n`; `W` is compatible and pure of weight
    `n − 1 = r`;
  - there are `P_w ∈ L[X]` such that for every place `w` of `E` whose residue
    characteristic is not in `S` and every `λ` of different residue
    characteristic, `W_λ` is unramified at `w` with Euler polynomial `P_w`;
  - there is a spectral system `s` of an actual presentation of `c` such that
    for every such `w` and the place `v` of `K` below it, `v` is outside the
    exceptional set of `s` and
    `ι(P_w) = clozelEulerPolynomial (s at v) f(w|v) q_w ^ a`.
- `IsClozelUnitarySystem Σ ι₀ c ι S a m W`: the same, with purity of weight
  `m` and the last identity replaced by
  `unitaryEulerPolynomial (ι(P_w)) = (Euler polynomial of the f-th powers of s at v)^a`.

## Statements

- `Clozel1991Theorem57Statement`: for a CM field `K` (with the cuspidal-class
  instance `CompactSpace (AdeleQuotient K)`), `r ≥ 2` and a cuspidal class `c` of
  `GL_{r+1}(𝔸_K)` that is regular algebraic and conjugate self-dual; a place `v₀`
  with `c(v₀) ≠ v₀` at which `c` has square-integrable components at `v₀` and at
  `c(v₀)`; and, if `2 ∣ n`, `4 ∤ n` and `d = [K : ℚ]/2` is odd, a second place `v₁`
  with `c(v₁) ≠ v₁`, `v₁ ∉ {v₀, c(v₀)}` and square-integrable components at `v₁`
  and `c(v₁)`. Then for every CM type `Σ` and `ι₀ ∈ Σ` there are `L`, `ι`, `S`,
  `a` and `W` with `IsClozelSystem`.
- `Clozel1993Theorem26Statement`: as above with `r ≥ 1`, with supercuspidal components at
  `v₀` and `c(v₀)` and no parity condition; the conclusion is
  `IsClozelUnitarySystem` for some `L`, `ι`, `S`, `a`, `m` and `W`.

## Faithfulness and conventions

- **Trace identities.** For `λ ∤ p`, Clozel's identities for all `m ≥ 0` say that
  `r_λ(Φ_w)` and `a` copies of `q_w^{n−1} r^T(Φ_w)` have the same traces of all
  powers, which in characteristic zero is the equality of their characteristic
  polynomials (`m = 0` gives the rank `a n`). The statement uses the
  equivalent Euler polynomials `det(1 − · X)`. "Non ramifiées en dehors des
  places divisant `S`" is read, as the identities require, for `λ ∤ p`.
- **Geometric Frobenius and Hecke matrices.** Clozel's `Φ_w` is geometric, as in
  the published `HasEulerPolynomialAt`. His `t_{π,v}` is the Hecke matrix with
  local reciprocity sending `Φ_v` to a uniformizer; the Library's spectral
  systems are the Satake parameters of actual presentations, on which the
  spherical Hecke operators act in the unitary normalization. The Satake
  correspondence identifying them is not proved in the Library.
- **Discrete series and supercuspidality at a split place.** At a place `v₀` of
  `F` split in `F_c`, `(π_c)_{v₀}` is the tensor product of the components at the
  two places `v, c(v)` of `K` above `v₀`; both are required. Square-integrable
  components are those of `Langlands/Automorphic/SquareIntegrableComponent`
  (irreducible, square-integrable modulo the center with unitary central
  character), which for conjugate self-dual `π_c` is Clozel's discrete series.
- **Parity.** `Clozel1991Theorem57Statement` retains the second place in the
  "mauvais cas" `2 | n`, `4 ∤ n`, `d` odd. `Clozel1993Theorem26Statement` removes it
  at the cost of the stronger supercuspidal hypothesis; the literature
  registration of `clozel-1993-kottwitz-cohomology` records that Theorem 2.6 is
  not a replacement for Harris 1998, Theorem 1.2 with square-integrable
  components only. Harris attributes the
  remaining bad-parity cases to Blasius (unpublished). The base change to a
  totally real quadratic `F'/F` of Clozel's Corollaire 5.4.2, which yields
  representations over a larger `E'`, is a totally real statement and is not
  formalized.
- **Association in Theorem 2.6.** Clozel describes §2.6 informally and refers
  to Théorème 5.3 for the precise formula. The doubling `J(π_c, 2)` produces
  Frobenius eigenvalues `q_w^{n−1} t^f` rather than `q_w^{(n−1)/2} t^f`, so the
  weight `n − 1` and the twist of Théorème 5.3 cannot be asserted from the
  printed text. The statement therefore asserts association after Harris's
  unitary normalization, purity of some weight `m`, and the multiplicity `a`.
  Together with purity and the Ramanujan bound that purity implies, this gives
  eigenvalues `q_w^{m/2} t^f`.
- **Reflex field.** `E = Σ.clozelReflexField ι₀ ⊂ ℂ` contains `ι₀(K)` and can be
  larger. For Harris's CM type induced from an imaginary quadratic subfield,
  `E = ι₀(K)` (`clozelReflexField_inducedFromImaginaryQuadratic`). This is the
  case used by Harris (1998, Theorem 1.2) and Harris (1999, Theorem 5.9(i)).
- **Hypothesis 5.1 and the unitary group.** Clozel's choices of the division
  algebra, involution and signatures (Hypothèse 5.1, `j₀ = {ι₀, cι₀}`) enter
  only through the proof and the integer `a = a(π, F_c, U, Σ)`, which is
  existential here.
- **Rank.** Clozel (1991), §1.2, printed p.101: "dans le § 5, on supposera que
  `n > 2` pour le calcul du corps reflex". `Clozel1991Theorem57Statement`
  therefore assumes `n = r + 1 ≥ 3` (`2 ≤ r`). Clozel (1993), §1.2, printed
  p.762, assumes `n ≥ 3` for the degree of the division algebra; §2.6 uses
  "notation unrelated to the previous notation", and its doubling works with
  the algebra of degree `2n`, so `Clozel1993Theorem26Statement` assumes
  `n ≥ 2` (`1 ≤ r`), the range in which Harris (1999, §1, `n > 1`) cites it.

## Scope

Not formalized here: the transfer of `π_c` to the unit group of a division
algebra and to the unitary group (Clozel 1991, §4, Proposition 4.8; Clozel
1993, Proposition 2.3), Kottwitz's zeta-function identity for the associated
Shimura varieties, the removal of the multiplicity `a` (see
`Langlands/Galois/TaylorMultiplicityRemovalStatement`), and any ramified local
compatibility.
