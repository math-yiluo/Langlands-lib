# Kottwitz's theorem on the λ-adic cohomology of the CM Shimura varieties

This module states, as an unproved proposition, Theorem 1 of Kottwitz (1992),
*On the λ-adic representations associated to some simple Shimura varieties*,
printed p. 657. It is stated for the Library's CM Shimura varieties `S_U` of
Harris's signature and the Library's `λ`-adic cohomology with coefficients in
an algebraic representation of the unitary similitude group. The declaration
is `CMHarrisKottwitzLambdaAdicStatement`, in namespace
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`. Its elaborated type is `Prop`.

## Kottwitz's theorem

Kottwitz's setting (printed pp. 654–657) is the following. `D` is a division
algebra with center a CM field `F`, of dimension `n²` over `F`, with an
involution of the second kind. `G` is the group of similitudes
`G(R) = {x ∈ D ⊗ R : x x* ∈ R^×}`. A homomorphism `h₀ : ℂ → D ⊗ ℝ` gives a
Shimura datum, with reflex field `E`. Kottwitz uses `h = (h₀|ℂ^×)^{-1}`
(p. 654). The coefficients are a representation `ξ` of `G` on a
finite-dimensional vector space over a number field `L`, irreducible over `L̄`.
The level `K` is small. `π_f` is an admissible representation of `G(A_f)` over
`L`, irreducible over `L̄`, and
`W^i(π_f) = Hom_{H_L}(π_f^K, H^i(S_K(ℂ), F_ξ))`, with
`W^i(π_f)_λ = W^i(π_f) ⊗_L L_λ` carrying the action of `Gal(Ē/E)`. Kottwitz
defines an integer `a(π_f)`. He fixes a finite set `S_bad` of primes outside
of which (a) `G` is quasi-split over `ℚ_p` and split over an unramified
extension, (b) `K = K^p K_p` with `K_p` hyperspecial, and (c) a function
`f_{π_f}` that cuts out `π_f` factors through the unit of the spherical Hecke
algebra at `p`. Write `π_f = π_p ⊗ π^p`. The weight morphism of `h` gives an
integer `w(ξ)`, because `ξ` is irreducible.

**Theorem 1.** (a) `a(π_f) ≠ 0` if and only if `W^i(π_f) ≠ 0` for some `i`.
(b) Suppose `a(π_f) ≠ 0`, and let `v` be a place of `E` over a prime
`p ∉ S_bad`. Then `π_p` is unramified. Let `r` be a root of `P(π_p, E_v)`. If
`a(π_f)` is positive (resp. negative), there is an even (resp. odd) `i` between
`0` and `2 dim S_K` such that `r` is an algebraic number all of whose complex
absolute values equal `q_v^{(i + w(ξ))/2}`. `P(π_p, E_v)` is uniquely a product
`∏_{i=0}^{2 dim S_K} P_i(π_p, E_v)` of monic polynomials over `L` with every
root of `P_i` of weight `i + w(ξ)`. For a place `λ` of `L` over a prime other
than `p`, `W^i(π_f)_λ` is unramified at `v`, and the characteristic polynomial
of the geometric Frobenius `Φ_v` on it is `P_i(π_p, E_v)^{|a(π_f)|}`.

## The Library's data

The section variables are those of `HarrisTaylorCMLambdaTower`, without the
coefficient prime, the coefficient place and the degree. They are the central
simple unitary data `D : CentralSimpleUnitaryData E F A n`, the charts
`C : HarrisSignatureCharts D.toSecondKindInvolution n Φ` for Harris's CM-type
section `Φ = harrisCMSection E (algebraMap L F) τ₀`, the conditional statements
`preservation … htor`, the representability statement `q`, the coefficient
field `K` (Kottwitz's `L`), the algebraic representation
`ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W` (Kottwitz's
`ξ`), the statements `existence` and `geometry`, the rigidity hypothesis
`hRigid` at every small level, and the level `U : SmallCMLevel D`. In the Lean
names, `E` is the totally real field, `F` the CM field and `L` the imaginary
quadratic field of Harris's CM type. Kottwitz's `F₀`, `F` and `L` are therefore
`E`, `F` and `K` here.

Kottwitz's level `K` is the Library's ordinary level
`(inverseOpposite U.obj).subgroup` of `GG(A_f)`. Kottwitz's `G` is the similitude
group of `D.rationalInvolution`. Kottwitz's `dim S_K` is `n − 1`, the dimension
for Harris's signature: `(n − 1, 1)` at the distinguished real place `τ₁ = C.distinguished`
and `(n, 0)` at the others.

Several bound variables of the statement are written with local notations:

* `τλ`, for a place `lam` of `K`, is `π_f ⊗_K K_λ`, the representation
  `(Module.End.baseChangeHom K K_λ V).toMonoidHom.comp πf` of `GG(A_f)` on
  `K_λ ⊗_K V`;
* `towerλ` is `cmHarrisLambdaTowerExtendScalars … ℓ ρ … lam i K_λ`, the tower
  cohomology `H^i(S, W)_λ` as a representation over `K_λ`;
* `vθ`, for a prime `p₀` and `θ : ℂ →+* PadicAlgCl p₀`, is the place
  `(harrisPlace p₀ θ (Φ C.distinguished)).1` of `F`, the place given by
  `θ ∘ Φ τ₁`;
* `derivedInstances ℓ` is the family, over all small levels, of the
  derived-category instances that the Library's cohomology uses for the
  coefficient prime `ℓ`.

Kottwitz's `W^i(π_f)_λ` is the Library's Hecke multiplicity space
`cmHarrisLambdaTowerHeckeMultiplicity … ℓ ρ … lam i K_λ (τλ) U`, that is,
`Hom_{H(U)}((π_f ⊗ K_λ)^U, H^i(S, W)_λ^U)` over the level Hecke algebra of `U`
over `K_λ`, with `Gal(F̄/F)` acting by composition. As a continuous Galois
representation it is `cmHarrisLambdaHeckeMultiplicityObjects`. This is the
convention of `HarrisTaylorCMLambdaTower`: the Hecke action is transported from
the tower, and under the fixed-vector comparison
`CMHarrisLambdaTowerFixedVectorComparison` the `U`-fixed vectors of the tower
are the level-`U` cohomology. Kottwitz's Betti multiplicity space, tensored with
`K_λ`, agrees with it by flat base change of `Hom` and the comparison between
Betti and étale cohomology. These identifications are not formalized.

## The statement

`CMHarrisKottwitzLambdaAdicStatement D C preservation … htor q ρ existence
geometry hRigid U : Prop` says the following. Assume:

* `_hdiv : ∀ a : A, a ≠ 0 → IsUnit a`: `A` is a division algebra (Kottwitz's
  `D`).
* `_hn : 3 ≤ n ∨ ∃ τ, τ ≠ C.distinguished`. Under this hypothesis the reflex
  field is `Φ τ₁ (F)` (the published `reflexField_eq_distinguishedImage`), so
  Kottwitz's places `v` of `E` are the places of `F` and `E_v = F_v`. The
  excluded case is `n = 2` with `E = ℚ`. There the reflex field is `ℚ`, and
  Kottwitz's theorem concerns `Gal(ℚ̄/ℚ)`, which the Library's cohomology over
  `F` does not carry.
* `_hρ`: `ρ` is irreducible over `K̄`. This means the representation
  `g ↦ ρ.act K̄ g` of the points of the group over `K̄ = AlgebraicClosure K` on
  `K̄ ⊗_K W` is irreducible (`Representation.IsIrreducible`). Since the points
  over an algebraically closed field are Zariski dense, this is irreducibility
  of the algebraic representation over `K̄`.
* `w : ℤ` and `_hw`: every rational similitude `g` over `K` whose underlying
  unit is a central scalar `t ∈ K^×` acts on `W` by `t^{-w}`
  (`ρ.rationalAction g x = t^{-w} • x`). This makes `w` Kottwitz's `w(ξ)`; see
  the section on the weight below.
* `πf : Representation K D.rationalInvolution.FiniteAdelicPoints V` with
  `_hadm : Langlands.IsAdmissible πf` and `_hirr`: the scalar extension
  `K̄ ⊗_K πf` is irreducible.

Then there is `a : ℤ` (standing for `a(π_f)`) with the following two
properties.

**(a)** For every coefficient prime `ℓ` (a finite place of `ℚ`), with the
derived-category instances `derivedInstances ℓ` and
`HasDerivedCategory (ModuleCat (HarrisCoefficientIntegers K ℓ))`, and every
place `lam : FinitePlacesAbove K ℓ`: if the fixed-vector comparison holds in
every degree, then `a ≠ 0` if and only if, for some degree `i`, the Hecke
multiplicity space `W^i(π_f)_λ` is nontrivial.

**(b)** There is a finite set `S : Finset ℕ` such that the following holds for
every prime `p₀ ∉ S` (with `[Fact p₀.Prime]`), every standard unramified chart
`c : UnramifiedChart D.toSecondKindInvolution (rationalPrimePlace p₀) n`, and
every smooth representation
`πp : SmoothRep K (LocalPoints D.toSecondKindInvolution (rationalPrimePlace p₀))`.
Assume:

* `KottwitzUnramified.IsUnramifiedAt (rationalPrimePlace p₀) F`: `F` is
  unramified at `p₀`;
* the level is `K_{p₀} × K^{p₀}` with `K_{p₀} = c.level`: under the published
  splitting `finiteAdelicPointsSplit p₀`, the image of the level is
  `(c.level.comap (dividingLocalMap p₀ ⟨rationalPrimePlace p₀, _⟩)).prod Kaway`
  for some subgroup `Kaway` of the prime-to-`p₀` points. This is the form of
  the published `IsKottwitzGoodPrime`, with the chart named;
* `πp` is the `p₀`-component of `π_f`: there is a representation `πaway` of the
  prime-to-`p₀` points over `K` such that `π_f` is equivalent to the tensor
  product of `πp ∘ finiteLocalMap (rationalPrimePlace p₀)` and `πaway` composed
  with the second projection of the splitting;
* `a ≠ 0`.

Then:

1. `c.IsSphericalIrreducible K̄ πp`: `F` is unramified at `p₀`, `K̄ ⊗_K πp` is
   irreducible, and `πp` has a nonzero `c.level`-fixed vector. This is
   Kottwitz's "`π_p` is unramified", together with irreducibility over `K̄`,
   which follows from that of `π_f`.
2. For every `θ : ℂ →+* PadicAlgCl p₀`, every square root
   `s : SqrtPrime (rationalPrimePlace p₀) K̄` of `p₀`, and every `P : K[X]`
   with `IsKottwitzPolynomial c θ hΦ C.hodgeFunction _ πp s P` (that is, `P` is
   Kottwitz's `P(π_{p₀}, E_v)` for the place `v = vθ`), write
   `q_v = Ideal.absNorm vθ.asIdeal`. Then:
   * (roots) for every embedding `ι : K →+* ℂ` and every complex root `z` of
     `P^ι`, there is `i ≤ 2(n − 1)` with `i` even if and only if `0 < a`, such
     that `z` is a Weil number of weight `i + w` for `q_v`
     (`Langlands.Cohomology.Weights.IsWeilNumber`: `z` is algebraic and all its
     conjugates have absolute value `q_v^{(i + w)/2}`);
   * (factorization) there is `Pf : Fin (2(n − 1) + 1) → K[X]` with
     `∏ i, Pf i = P` and each `Pf i` pure of weight `i + w`
     (`IsPurePolynomial q_v (i + w) (Pf i)`: monic, and for every embedding of
     `K` in `ℂ` every complex root is a Weil number of that weight);
   * (uniqueness) every `Q` with these two properties equals `Pf`;
   * (Galois) for every coefficient prime `ℓ ≠ rationalPrimePlace p₀`, with its
     derived-category instances, every place `lam` of `K` above `ℓ`, every
     degree `i ≤ 2(n − 1)`, every fixed-vector comparison `hfix` in degree `i`,
     every continuity hypothesis `hcont` for `H^i(S_U, W)_λ`, and every
     instance that the Hecke multiplicity space is finite-dimensional over
     `K_λ`, the Galois representation
     `cmHarrisLambdaHeckeMultiplicityObjects … lam i K_λ continuous_id hfix U
     hcont (τλ)` satisfies `HasEulerPolynomialAt` at `vθ` with polynomial
     `((Pf i ^ a.natAbs).map (algebraMap K K_λ)).reverse`. That is, it is
     unramified at `vθ`, and a geometric Frobenius at `vθ` has Euler polynomial
     `det(1 − Φ_v X)` equal to the reverse of `P_i^{|a|}`. Since the
     characteristic polynomial of `Φ_v` and `P_i^{|a|}` have nonzero constant
     terms, this says that the characteristic polynomial of `Φ_v` is
     `P_i^{|a|}`, as in Kottwitz.

The coefficient prime `ℓ` and the place `λ` are quantified inside the
statement, after `a` and `S`. So `a` and `S` do not depend on `ℓ`, as in
Kottwitz.

## The weight `w(ξ)`

Kottwitz (p. 657) defines `w(ξ)` through the weight morphism
`w : G_m → Center(G)` of `h` ("see [D1]"). Since `ξ` is irreducible, `ξ ∘ w` is
a character `t ↦ t^{w(ξ)}` of `G_m`. The sign of the weight morphism is fixed
by the purity argument in Kottwitz's §5 (printed p. 661, PDF p. 9). There, an
eigenvalue of `ξ(γ₀)` has absolute value `ξ(q^{−j/2}) = (q^{j/2})^{w(ξ)}`, so
the weight morphism is `t ↦ t^{−1}` (consistent with `h = h₀^{-1}`), and a
central scalar `t` acts through `ξ` by `t^{−w(ξ)}`. The hypothesis `_hw`
states exactly this on the `K`-rational central scalars. These determine the
character, because `K` is infinite. For the standard representation this
gives `w = −1`, the weight of the first homology of the universal abelian
variety.

The statement identifies the Library's coefficient system attached to `ρ` with
Kottwitz's local system `F_ξ`. The Library builds it from level structures on
torsion points of the universal abelian scheme
(`HarrisTaylorCMGeometricCoefficients`, after Harris 1999, §3). For the
standard representation this is the system of torsion points, that is, of
first homology, which is Kottwitz's normalization. This identification is part
of the statement's provenance, not a formalized comparison.

## Relation to the source: specializations and weaker parts

* **Harris's signature.** The Library's `λ`-adic cohomology exists only for
  `HarrisSignatureCharts`, so the statement is the specialization of Kottwitz's
  theorem to signature `(n − 1, 1)` at one real place and `(n, 0)` at the
  others, the signature of the Library's Harris datum. The Library's Shimura
  varieties are schemes over `F`. Under `_hn`, `F` is identified with the
  reflex field `E` through `Φ τ₁` (`harrisReflexCMEquiv`), and the place `v` of
  `E` determined by `θ` is the place `vθ` of `F`. That the Library's `S_U` over
  `F` is Kottwitz's canonical model is not formalized.
* **The integer `a(π_f)`.** Kottwitz defines `a(π_f)` from automorphic
  multiplicities and pseudo-coefficients at infinity. These are not in the
  Library, so the statement only asserts that some integer `a` has properties
  (a) and (b).
* **The set `S_bad`.** Conditions (a) and (b) of Kottwitz's `S_bad` appear as
  explicit hypotheses at `p₀`. Condition (c) involves `f_{π_f}`, which is not
  formalized. It holds outside a finite set of primes, and the statement
  asserts only the existence of some finite set `S` outside of which the
  conclusions hold. It does not say that `S` can be taken to be the set where
  condition (c) fails.
* **Charts.** The Library's `P(π_p, E_v)` (`IsKottwitzPolynomial`) is defined
  using a standard unramified chart `c`. Kottwitz's polynomial depends only on
  the hyperspecial subgroup `K_p`. The statement therefore quantifies over
  every chart whose level is the `p₀`-component of the level.
* **The polynomial `P`.** The statement makes its claims for every `P` related
  to `πp` by `IsKottwitzPolynomial`, for every `θ` and every square root `s`. It
  does not assert that such a `P` exists.
* **Library hypotheses.** The fixed-vector comparison, the continuity of the
  Galois action on `H^i(S_U, W)_λ`, and the finite-dimensionality of the Hecke
  multiplicity space are hypotheses of the Galois clause, because the Library's
  Galois representation `cmHarrisLambdaHeckeMultiplicityObjects` needs them. The
  fixed-vector comparison in every degree is a hypothesis of (a). All three are
  true for the actual cohomology, but they are not proved in the Library.
* **Degrees.** Kottwitz's `0 ≤ i ≤ 2 dim S_K` is `i ≤ 2(n − 1)`. The
  factorization is indexed by `Fin (2(n − 1) + 1)`.
* **Roots and parity.** The roots clause is Kottwitz's statement about the
  roots of `P(π_p, E_v)`, read at every complex embedding of `K`. Given the
  factorization, it is equivalent to `P_i = 1` for every `i` of the wrong
  parity.

## Provenance

R. E. Kottwitz, *On the λ-adic representations associated to some simple
Shimura varieties*, Invent. Math. 108 (1992), §1, printed pp. 654–658
(PDF pp. 2–6; printed page = PDF page + 652): the setting (pp. 654–655), `W^i`
and `W^i(π_f)_λ` (p. 655), `S_bad` and conditions (a)–(c) (pp. 655–656),
`V(π_p, E_v)` and `P(π_p, E_v)` (pp. 656–657), `a(π_f)`, `w(ξ)` and Theorem 1
(p. 657). The purity paragraph used for the sign of `w(ξ)` is in §5, printed p. 661. The source
is `kottwitz-1992-lambda-adic-simple-shimura`, PDF SHA-256
`749af5541a59187e6f9d1089dec9a0e591a2059173da739c7384ff3a7d0dd799`. The
irreducibility hypotheses "over `L̄`" for `ξ` and `π_f` are read from the page
image of printed p. 655.

M. Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39 (1999), Introduction, printed p. 299 (the groups
attached to division algebras), §3, printed pp. 306–308 (the coefficient
systems), and Theorem 5.7(ii), printed p. 313, which cites Kottwitz for the
unramified places. The source is
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, PDF SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

The Library's ingredients are `IsKottwitzPolynomial`, `UnramifiedChart`,
`UnramifiedChart.IsSphericalIrreducible` and the chart conventions of the
Kottwitz modules; the `λ`-adic Hecke multiplicity spaces of
`HarrisTaylorCMLambdaTower`; `HasEulerPolynomialAt`; and `IsWeilNumber` and
`IsPurePolynomial` of `Langlands.Cohomology.Weights`.
