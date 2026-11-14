# Harris (1999), Theorem 5.7(i)–(ii), for the Library's λ-adic cohomology

This module states, as an unproved proposition, parts (i) and (ii) of
Theorem 5.7 of Harris, *Galois properties of cohomological automorphic forms
on GL(n)*, J. Math. Kyoto Univ. 39 (1999), printed p. 313. It is stated for
the Library's CM Shimura varieties of Harris's signature, the Library's
`λ`-adic cohomology with coefficients in an algebraic representation `ρ`, and
the published transfer relation `JL(π_f)`. The declaration is
`CMHarrisTheorem57Statement`, in namespace
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`. Its elaborated type is `Prop`.
Part (iii) is not stated here.

## Harris's theorem

Harris's setting (§§4–5, printed pp. 308–313) is a CM field `𝒦` containing an
imaginary quadratic field `𝒦₀`, a division algebra `ℬ` with involution
defining the unitary similitude group `GG` and its Shimura varieties `S_K`,
and an inner form `GJ` (algebra `𝒟`) that is split at a place `v` of `𝒦`
above a prime `p` split in `𝒦₀`, where `ℬ` is a division algebra. `π` is an
automorphic representation of `GJ` whose component `π_v`, a representation of
`GL(n, 𝒦_v)`, is supercuspidal, and `JL(π_f)` is the representation of
`GG(A_f)` with the same local constituents away from `v` and the local
Jacquet–Langlands transfer of `π_v` at `v` (printed p. 312).
`H^{n−1}(S̄_{K(N)}, W̃)[π]` is the `JL(π_f)`-isotypic component of the
cohomology. `ν̄(π)` is the twisting character of Harris (1998), Erratum,
(E.1)–(E.2). For a representation `σ` pure of some weight, (5.6) defines the
normalized local Artin `L`-function
`L_w(s, σ) = ∏_β (1 − (β/|β|) Nv^{−s})^{−1}`, where `β` runs over the
eigenvalues of a geometric Frobenius at `w` and `|β|` is any complex absolute
value.

**Theorem 5.7.** Assume the factor `ℚ_p^×` of `GJ_p` in the factorization
(4.2) acts trivially on `π`. (i) The semisimplification of the representation
of `Gal(𝒦̄/𝒦)` on `[H^{n−1}(S̄_{K(N)}, W̃)[π] ⊗ ν̄(π)]^*` is the direct sum of
`a(π)` copies of an `n`-dimensional representation `ρ(π)`. (ii) For almost all
places `w` of `𝒦` dividing rational primes `p` at which `π` is unramified, the
normalized local Artin `L`-function of `ρ(π)` at `w` coincides with the
standard local Euler factor `L(s, BC_{𝒦/E}(π)_w)`, where `BC_{𝒦/E}` is
quadratic base change from `GJ` to `GL(n, 𝒦)`.

## The Library's data

The section variables are those of `HarrisTaylorCMKottwitzStatement`: the
central simple unitary data `D : CentralSimpleUnitaryData E F A n` (Harris's
`ℬ` is `A`, and `GG` is the similitude group of `D.rationalInvolution`), the
charts `C` for Harris's CM-type section, the conditional statements
`preservation … htor`, the representability statement `q`, the coefficient
field `K`, the algebraic representation `ρ` of `GG` over `K` (Harris's `W̃`),
the statements `existence` and `geometry`, the rigidity hypothesis `hRigid`,
and a small level `U : SmallCMLevel D`. In the Lean names, Harris's `𝒦` is `F`
and his `𝒦₀` is the imaginary quadratic field `L`, with `ι = algebraMap L F`.

The remaining variables are those of the published
`JacquetLanglands.IsHarrisJacquetLanglandsTransfer`
(`Langlands/JacquetLanglands/HarrisTransfer`), with `σB` taken to be
`D.toSecondKindInvolution`:

* the algebra `D'` of `GJ` with its involution `σJ : SecondKindInvolution E F D'`;
* the prime `p` with `hp : p.Prime`, the place `v` of `ℚ` above it, the place
  `𝔭` of `L` above `v` with `h𝔭` saying that `L_𝔭 = ℚ_p` (so `p` splits in `L`),
  and the place `w₀` of `F` above `𝔭` (Harris's `v`);
* the splitting `s : F_{w₀} ⊗_F D' ≃ M_n(F_{w₀})`, the central division algebra
  `Δ` over `F_{w₀}` with `t : F_{w₀} ⊗_F A ≃ Δ`, and the identifications `f`
  (at the other places above `𝔭`) and `e`, `he` (away from `p`) of `GJ` with
  `GG`.

## The statement

`CMHarrisTheorem57Statement D C preservation … htor q ρ existence geometry
hRigid U σJ p hp v 𝔭 h𝔭 w₀ s Δ t f e he : Prop` says the following.

Assume:

* `_hdiv`: `A` is a division algebra, as Harris's `ℬ` is.
* `πf : Representation ℂ σJ.rationalInvolution.FiniteAdelicPoints V` (Harris's
  `π_f`) and `ρ' : Representation ℂ D.rationalInvolution.FiniteAdelicPoints V'`
  are related by `IsHarrisJacquetLanglandsTransfer … πf ρ'`, that is,
  `ρ' = JL(π_f)`. Both are irreducible and admissible.
* `π_v` is supercuspidal: for the published splitting
  `harrisAwaySplitGL … s : GJ(A_f) ≃ GL_n(F_{w₀}) × HarrisAwayComplement`,
  `πf` is equivalent to `splitTensor` of a supercuspidal representation `πv`
  of `GL_n(F_{w₀})` (`GeneralLinear.IsSupercuspidal`) and a representation of
  the complement. The published transfer relation leaves this hypothesis to
  its consumers.
* The factor `ℚ_p^×` acts trivially: `πf` is trivial on the elements
  `(harrisAwaySplitGL … s).symm (1, ((1, z), 1))`, `z ∈ ℚ_p^×`. In the
  published complement `((Π_{w ≠ w₀} …) × ℚ_p^×) × GJ(A_f^p)`, these are the
  elements of the factor `ℚ_p^×` of (4.2).
* `ξ₀ : HeckeCharacter L` is the central character of `ρ'` on the ideles of
  `L`. For every finite idele `x` of `L` and every `g ∈ GG(A_f)` whose
  underlying unit is the scalar `x`, `ρ' g = ξ₀(x) • id`. Here the scalar of
  `x` in `A_{ℚ,f} ⊗_ℚ A` is the image of `x` under the published
  `finiteAdeleTensorEquiv ℚ L : A_{ℚ,f} ⊗_ℚ L ≃ A_{L,f}` and `L → F → A`, and
  `x` is viewed as an idele class with trivial archimedean component. Harris's
  (E.1) uses `ξ ∘ r_μ`, with `ξ` the central character and
  `r_μ(a) = N_{𝒦/𝒦₀}(a) ∈ 𝒦₀^× ⊂ Z`. So the character that enters `ν̄` is the
  central character restricted to the ideles of `𝒦₀`. Since `L` is dense in
  `L ⊗ ℝ = ℂ`, the finite ideles have dense image in the idele classes, so the
  condition determines `ξ₀`. The transfer preserves central characters, so the
  central character of `π` may be read on `ρ'`.
* `ℓ` is a coefficient prime with the Library's derived-category instances,
  and `lam` a place of `K` above `ℓ`.
* `M` is a topological field extension of `K_λ` with continuous `K_λ → M`, and
  `j : M ≃+* ℂ` is a field isomorphism. This is Harris's identification of
  `ℚ̄_ℓ` with `ℂ`, used to compare complex representations with `ℓ`-adic ones.
* `τ : Representation M GG(A_f) V''` is the model of `JL(π_f)` over `M`
  through `j`: an additive bijection `eτ : V' ≃ V''` with
  `eτ (z • x) = j⁻¹(z) • eτ x` that intertwines `ρ'` and `τ`.
* `hfix`, `hfin`, `hcont`: the Library's fixed-vector comparison in degree
  `n − 1`, and the finite-dimensionality and continuity of
  `H^{n−1}(S_U, W)_λ`.
* `Hπ` is `cmHarrisLambdaIsotypicFixedVectorsObjects … lam (n − 1) M hKM hfix
  U hfin hcont τ`, the `τ`-isotypic part of `H^{n−1}(S_U, W)_λ ⊗ M`. This is
  Harris's `H^{n−1}(S̄_{K(N)}, W̃)[π]`, as a continuous representation of
  `Gal(F̄/F)` over `M`. It is assumed nonzero (`Nontrivial Hπ.val`): `JL(π_f)`
  occurs in the cohomology. Without this hypothesis `ρ(π)` is not defined, and
  part (ii) would assert the existence of a Galois representation for
  every `π`.
* `Lν` is a number field with an embedding `ιν : Lν → ℂ`, and
  `lamν : FinitePlacesAbove Lν ℓ` is a place of `Lν` above the same rational
  prime `ℓ` as `lam`. `ψ : LambdaAdicCharacter F Lν lamν` is a `λ`-adic
  realization of `ν̄(π)` (`Harris.IsNuBarRealization ιν lamν n ξ₀ ψ`): a
  continuous character with values in `Lν_{lamν}^×`.
* `κ : Lν_{lamν} → M` is a ring homomorphism that is continuous
  (`Continuous κ`) and compatible with `ιν` and `j`: `j (κ c) = ιν c` for
  `c ∈ Lν`.

  Then `g ↦ κ(ψ(g))` is a continuous character of `Gal(F̄/F)` with values in
  `M^×`: the composite of the continuous map `ψ`, the continuous inclusion
  `Lν_{lamν}^× → Lν_{lamν}` and the continuous `κ`. At almost all places `w` of
  `F`, its value at a geometric Frobenius is `κ(c)`, where `c ∈ Lν` and
  `j(κ(c)) = ιν(c) = ν̄(π)_w(ϖ_w)`. So it is the realization of `ν̄(π)` with
  values in `M`. Harris forms the tensor product with `ν̄(π)` in one `λ`-adic
  coefficient setting. The hypotheses that `lamν` lies above `ℓ` and that `κ`
  is continuous express this. They exclude abstract transport between
  completions at different primes: an abstract embedding `ℚ_q → M` with
  `q ≠ ℓ` is not continuous, and composing a `q`-adic character with it can
  give values whose `ℓ`-adic absolute value is not `1`. Such a twist cannot
  have the characteristic polynomials of a continuous `ℓ`-adic
  representation. This example is due to the reviewer of an earlier version
  of this statement.

Then there are `a : ℕ` and a continuous representation
`ρπ : Objects F M` of rank `n` (Harris's `a(π)` and `ρ(π)`) such that:

* **(i)** for every `g ∈ Gal(F̄/F)`, the characteristic polynomial of
  `κ(ψ(g⁻¹)) • Hπ(g⁻¹)` equals `charpoly(ρπ(g))^a`. The element
  `g` acts on `[Hπ ⊗ ν̄(π)]^*` by the transpose of
  `(ψ(g) Hπ(g))^{−1} = ψ(g⁻¹) Hπ(g⁻¹)`, which has the same characteristic
  polynomial. So this says that the representations
  `[Hπ ⊗ ν̄(π)]^*` and `ρπ^{⊕a}` have equal characteristic polynomials at every
  element. In characteristic `0` this is equivalent to the equality of their
  semisimplifications (Brauer–Nesbitt). Semisimplifications are compared in
  the same way in the published `TaylorMultiplicityRemovalStatement`.
* **(ii)** there is a finite set `T` of primes such that the following holds
  for every prime `p₀ ∉ T`, every standard unramified chart
  `c : UnramifiedChart D.toSecondKindInvolution (rationalPrimePlace p₀) n`, and
  every `p₀`-component `πp` of `ρ'` (as in `HarrisTaylorCMKottwitzStatement`,
  `ρ'` is equivalent to the tensor product of `πp ∘ finiteLocalMap` and a
  representation of the prime-to-`p₀` points). Let `ξ : c.torus →* ℂˣ` be a
  principal-series parameter of `πp` (`c.HasPrincipalSeriesParameter πp ξ`,
  which includes that `πp` is unramified for the level of `c` and that `F` is
  unramified at `p₀`). Then for every place `w` of `F` above `p₀` there is
  `Q ∈ M[X]` with `HasEulerPolynomialAt ρπ w Q`, so `ρπ` is unramified at `w`
  and `Q = det(1 − Frob_w X)` for a geometric Frobenius, and
  `unitaryEulerPolynomial (Q.map j) = Eigenvalues.eulerPolynomial
  (c.baseChangeEigenvalues ξ w)`.

The left side of the last equation is the published normalization (5.6)
(`Langlands/Galois/UnitaryNormalization`): each reciprocal root `β` of the
Euler polynomial, read in `ℂ` through `j`, is replaced by `β/|β|`. The right
side is `∏_k (1 − t_k X)` for the unitarily normalized Satake parameter
`t = (t_k)` of the unramified base change `BC(π)_w` of `π_{p₀}` to
`GL_n(F_w)`, as defined by the published `UnramifiedChart.baseChangeEigenvalues`
(`Langlands/Shimura/Unitary/KottwitzBaseChange`). At `X = q_w^{−s}` this is the
denominator of `L(s, BC(π)_w)`. Away from `p`, the local constituents of
`π_f` and `JL(π_f)` agree, so the base change of `π` at `w` is read on the
component of `ρ'`. At `p` itself no standard unramified chart exists, since
`A` is not split at `w₀`.

## Relation to the source: specializations and weaker parts

* **The level.** Harris states the theorem at the levels `K(N)` of §4. The
  statement is made at every small level `U`. Parts (i) and (ii) depend only
  on the isotypic component at a level, and Taylor's and Kottwitz–Clozel's
  arguments apply at any small level. This is a generalization of the stated
  level, and part of the unproved obligation.
* **Harris's signature and the Shimura datum.** The Library's `λ`-adic
  cohomology exists only for the Harris-signature charts. That the Library's
  `S_U` over `F`, with the coefficient system attached to `ρ`, is Harris's
  `S̄_{K(N)}` with `W̃` for the Shimura datum used in Harris (1999) is not
  formalized. Harris (1998), Erratum, (E.1)–(E.2), explains that the datum of
  [H1] was the complex conjugate of that of Rapoport–Zink, and that `ν̄` is the
  twisting character for the conjugate datum. The statement uses `ν̄`, as Harris
  (1999) does. Matching this convention with the Library's datum is part of the
  unformalized identification.
* **Hypotheses of the Library.** The fixed-vector comparison, finiteness and
  continuity are hypotheses, because the Library's Galois representation
  `cmHarrisLambdaIsotypicFixedVectorsObjects` needs them. They hold for the
  actual cohomology, but the Library does not prove them.
* **`ν̄(π)`.** The statement is made for every `λ`-adic realization of `ν̄(π)`
  over a number field at a place above `ℓ`, mapped into `M` by a continuous
  embedding compatible with `j`. It does not assert that such a realization
  exists. The realization is not required to be the one in Harris's fixed
  coefficient field. When `M` is Hausdorff, the choice does not matter. Two
  such realizations differ by a continuous `M^×`-valued character that is
  trivial at the Frobenius elements of almost all places. Such a character is
  trivial, by Chebotarev density and because its kernel is closed. Part (i) is
  insensitive to the twist; part (ii) depends on it.
* **`JL(π_f)` and its model.** `JL(π_f)` is given by the published relation,
  which asserts neither existence nor uniqueness. Its model over `M` is
  described relationally through `j`. No construction is assumed.
* **Automorphy.** Harris's `π` is automorphic. The statement does not assume
  automorphy of `π_f` separately. It assumes instead that `JL(π_f)` occurs in
  `H^{n−1}(S_U, W)_λ`.
* **Almost all places.** "Almost all places `w` of `𝒦` dividing rational
  primes `p` at which `π` is unramified" is encoded as all places above primes
  outside a finite set `T`, at which `π_{p₀}` has a principal-series parameter
  for a standard unramified chart. The quantification over charts and
  parameters follows `IsBaseChangeParameterOf`.

## Provenance

M. Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39 (1999): §4, (4.2), printed p. 309 (PDF p. 11; the factor
`ℚ_p^×`); §5, printed p. 312 (`π`, `π_v` supercuspidal, `JL(π_f)`, the
isotypic component); (5.6) and Theorem 5.7, printed p. 313 (PDF p. 15),
checked against the page image. The source is
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, PDF SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

M. Harris, *The local Langlands conjecture for GL(n) over a p-adic field,
n < p*, Invent. Math. 134 (1998), Erratum to [H1], printed pp. 181–182
(`ν(Gπ) = ξ^{−1} ∘ r_μ · |·|^{(n−1)/2}` (E.1), with `r_μ(a) = N_{𝒦/𝒦₀}(a)`
and `r̄_μ = r_μ ∘ c` (E.2)). The source is `harris-1998-local-langlands`,
SHA-256 `7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`.

The Library's ingredients are `IsHarrisJacquetLanglandsTransfer`,
`harrisAwaySplitGL`, `HarrisAwayComplement` and `splitTensor`
(Jacquet–Langlands); `GeneralLinear.IsSupercuspidal`; `HeckeCharacter`,
`finiteAdeleTensorEquiv`, `ideleClassMap` and `finiteIdelesInclusion`;
`Harris.IsNuBarRealization`; the isotypic Galois representation
`cmHarrisLambdaIsotypicFixedVectorsObjects` of `HarrisTaylorCMLambdaTower`;
`HasEulerPolynomialAt` and `unitaryEulerPolynomial`; and `UnramifiedChart`,
`HasPrincipalSeriesParameter` and `baseChangeEigenvalues` of the Kottwitz
modules.
