# Harris (1999), Theorem 5.9(ii): parameter existence and irreducibility at a split supercuspidal place

This module states two derived consequences of Theorem 5.9(ii) of Harris,
*Galois properties of cohomological automorphic forms on GL(n)*, J. Math.
Kyoto Univ. 39 (1999), printed pp. 314–315. Both are unproved propositions,
and both elaborate to `Prop`. They are in namespace
`Langlands.GaloisRepresentation`:

* `Harris1999Theorem59iiParameterStatement` (parameter existence). The
  restriction to the decomposition group at `v` of a suitable family as in
  Theorem 5.9(i) depends only on the local component `Π_v`, the coefficient
  prime `ℓ` and an identification `ℚ̄_ℓ ≅ ℂ`.
* `HarrisSupercuspidalRestrictionIrreducibleStatement` (irreducibility). The
  restriction to the decomposition group at `v` of every family as in
  Theorem 5.9(i) is absolutely irreducible.

The module also defines a helper construction, `scalarExtensionAlong`
(extension of scalars of a finite-dimensional representation along a field
homomorphism).

Neither statement mentions Harris's local parameter `σ(Π_v)` of (5.4)–(5.5).
That parameter is built from the cohomology of the Drinfeld tower `ℳ_N`
(see "Scope"). The module is a faithful
formalization of neither Harris's 5.9(ii) nor Henniart's irreducibility
theorem. It records what Theorem 5.9(ii) implies once its right-hand side
is taken to be an unspecified local map, together with the irreducibility
of `σ(π_v)` that Harris cites. This form is the interface through which
`HarrisSupercuspidalLocalComparisonReduction` reduces the general-coefficient
comparison at a split supercuspidal place to Theorem 5.9(ii).

## Harris's text

Harris's setting is a CM field `𝒦` containing an imaginary quadratic field
`𝒦₀`, and `n = r + 1 > 1`, as in the published
`Harris1999Theorem59iStatement` (module
`Langlands.Galois.Harris1999Theorem59Statement`, whose conventions and
hypotheses this module reuses). Printed p. 313 (PDF p. 15, checked against
the page image), with `F = 𝒦_v`:

> In [H1] (corrected in [H2, Erratum]) a correspondence was defined between
> the set of equivalence classes of supercuspidal representations of
> `GL(n, F)` and the set of equivalence classes of irreducible
> `n`-dimensional complex representations of the Weil group `W_F` of `F`.
> Actually, one correspondence was defined for each rational prime `ℓ`, via
> an identification between the algebraic closures of `𝐐` in `𝐐̄_ℓ` and `𝐂`;
> the irreducibility was proved by Henniart (cf. [BHK]).

There follow formulas (5.4) `σ(π_v) = [σ̃(π_v) ⊗ ν̄(π)_v^{-1}]^*` and (5.5),
which defines `σ̃(π_v)` as a `Gal(F̄/F)`-representation over `𝐐̄_ℓ` cut out
of the semisimplified `H_c^{n−1}(ℳ̆_N, 𝐐̄_ℓ)`. Printed p. 314 (PDF p. 16)
says: "Note that the definition (5.4) and (5.5) of `σ(Π_v)` below is purely
local." Theorem 5.9, printed pp. 314–315 (PDF pp. 16–17, checked against the
page image):

> **Theorem 5.9.** Assume the Galois conjugate `Π^c` of `Π` is isomorphic to
> the contragredient `Π^∨`. Let `v` be a finite place of `𝒦`, split over `K`,
> and suppose the local component `Π_v` at `v` is supercuspidal.
>
> (i) (Clozel, Kottwitz) There is a number field `C` and a compatible family
> of `λ`-adic representations `σ_λ(Π)` of `Gal(𝒦̄/𝒦)`, pure of some weight
> `m`, where `λ` runs over finite places of `C`, such that, for almost all
> finite places `w` of `𝒦` at which `σ_λ(Π)` and `Π_w` are unramified, we
> have equality of local Euler factors `L_w(s, σ_λ(Π)) = L_w(s, Π_w)`. […]
>
> (ii) Fix `λ` of characteristic different from that of `v`, and let `σ_v`
> denote the restriction of `σ_λ(Π)` to a decomposition group `Z_v` of `v`.
> Then `σ_v` is equivalent to `σ(Π_v)`.

Here `Π` is cuspidal of cohomological type (p. 314). The published 5.9(i)
statement reads "split over `K`" as: the place of the maximal totally real
subfield below `v` splits in `𝒦`. It encodes this as
`Harris.conjPlace 𝒦 v ≠ v`, and this module does the same.

## The helper `scalarExtensionAlong`

For a field homomorphism `j : F →+* Ω` and a finite-dimensional representation
`A` of a monoid `G` over `F`, `scalarExtensionAlong j A` is the representation
`g ↦ id_Ω ⊗ A(g)` of `G` on `Ω ⊗[F] A`, where `Ω` is an `F`-algebra
through `j`. It is the `FiniteRepresentation` wrapper, for an arbitrary field
homomorphism, of the Library's unbundled base change
`Langlands.Cohomology.baseChangeRepresentation` (module
`Langlands.Cohomology.DivisibleSystem.ScalarExtension`, for an algebra
`R → S`). The Library's `ladicScalarExtension`
(`Langlands.Correspondence.HenniartLadicClasses`) is the bundled special case
with target `ℂ`, and the helper follows its construction with Mathlib's
`Module.End.baseChangeHom`.

## `Harris1999Theorem59iiParameterStatement`

Binders, in order:

* a CM number field `K` (Harris's `𝒦`) with compact adelic quotient, an
  imaginary quadratic subfield `K₀`, an integer `r ≥ 1` (so `n = r + 1`), and a
  finite place `v` of `K` with `Harris.conjPlace K v ≠ v` (the place of the
  maximal totally real subfield below `v` splits), all as in
  `Harris1999Theorem59iStatement`;
* **there exists** a map `Φ ℓ ιΩ`, for every prime `ℓ` and every field
  isomorphism `ιΩ : PadicAlgCl ℓ ≃+* ℂ` (`PadicAlgCl ℓ` is Mathlib's algebraic
  closure of `ℚ_ℓ`). It sends smooth classes of `GL_{r+1}(K_v)`
  (`SmoothRep.IsoClass ℂ (FiniteLocalGL K (r + 1) v)`) to finite-dimensional
  `ℚ̄_ℓ`-representations of `LocalGroup v`, the absolute Galois group of the
  completion `K_v`. No continuity or other property of `Φ` is asserted;
* for every cuspidal realization `S` of rank `r + 1` and every spectral
  presentation `P` of `S`, such that `S` is regular algebraic and conjugate
  self-dual and the local component `P.localComponent v` is supercuspidal
  (Harris's hypotheses, encoded as in the published 5.9(i) statement and in
  `HasSupercuspidalComponent`);
* **there exist** a number field `L` (Harris's `C`), an embedding
  `ι : L →+* ℂ`, a collection `R` of continuous `λ`-adic representations of
  `Gal(K̄/K)` indexed by all finite places `λ` of `L`, and a weight `m`. These
  satisfy the three conclusions of the 5.9(i) statement: pure compatible of
  weight `m`, of rank `r + 1`, and weakly associated to `S`'s class at `ι`.
  They also satisfy:
* for every prime `ℓ` different from the residue characteristic of `v`,
  every `ιΩ : PadicAlgCl ℓ ≃+* ℂ`, every finite place `lam` of `L` and every
  **continuous** field homomorphism `j : L_lam →+* PadicAlgCl ℓ` with
  `ιΩ (j x) = ι x` for `x ∈ L`: the representation
  `scalarExtensionAlong j (atFinitePlace v R_lam)` of `LocalGroup v` is
  equivalent (`FiniteRepresentation.Equiv`) to
  `Φ ℓ ιΩ (P.localComponent v).isoClass`.

`atFinitePlace v` is the Library's restriction along the completion
embedding `K → K_v`, using Mathlib's compatible choice of algebraic
closures. This is a decomposition group `Z_v` in Harris's sense.

### How the statement relates to Harris's

Harris's (ii) compares the `λ`-adic representation `σ_v` with `σ(Π_v)`, a
representation over `𝐐̄_ℓ` obtained from the `ℓ`-th correspondence of p. 313.
Making sense of this comparison requires a map from the coefficient
completion `C_λ` to `𝐐̄_ℓ` compatible with the identification of algebraic
closures and with the embedding `C → ℂ` used in (i). The statement makes
this explicit through `j`:

* Since `j` is continuous and `L` is dense in `L_lam`, `j` is determined by
  its restriction `ιΩ⁻¹ ∘ ι` to `L`. A continuous `j` exists only for the one
  place `lam` of `L` induced by the `ℓ`-adic absolute value through
  `ιΩ⁻¹ ∘ ι`, and that place lies over `ℓ`. So for each pair `(ℓ, ιΩ)` the
  conclusion concerns exactly one coefficient place, and every place `lam` of
  `L` over `ℓ` arises from some `ιΩ`.
* Continuity cannot be dropped. An element of `Gal(K̄_v/K_v)` outside the
  Weil group, such as a Frobenius lift raised to a non-integral `ℓ`-adic
  power, typically has a trace in `L_lam` that is not in `L`. Discontinuous
  field embeddings `L_lam → ℚ̄_ℓ` that agree with `ιΩ⁻¹ ∘ ι` on `L` exist
  (extend along a transcendence basis), and they can move such a trace. The
  resulting representations then have different traces, so no single
  `Φ ℓ ιΩ (Π_v)` could match them all.
* `Φ` is indexed by the full isomorphism `ιΩ`. Harris's correspondence
  depends only on the induced identification of algebraic closures of `𝐐`.
  The statement therefore allows `Φ` to depend on more data than Harris's
  `σ`, which makes it weaker.
* The statement uses the absolute Galois group of `K_v`, as Harris's
  `Z_v` does, not the Weil group `W_F` of the p. 313 correspondence. For
  continuous representations nothing is lost, because `W_F` is dense in
  `Gal(F̄/F)`.
* Harris's (ii) concerns the family constructed in his (i). Here the family
  is existential, and one family `R` serves every coefficient place and every
  compatible identification. The statement does not claim that every family
  as in (i) satisfies the conclusion. By the argument below, every family as
  in (i) has a weight `m ≡ n − 1 (mod 2)`, where `n = r + 1`, and the
  witness constructed there has weight `1 − n`. After a compatible scalar
  extension, a family of weight `m` is isomorphic to the witness twisted by
  `ε^{−k}`, where `ε` is the `ℓ`-adic cyclotomic character and
  `k = (m + n − 1)/2`. Its restriction at `v` is then
  `Φ ℓ ιΩ (Π_v) ⊗ ε^{−k}`. When `k ≠ 0` this is not equivalent to
  `Φ ℓ ιΩ (Π_v)`, because the determinants differ by the unramified
  character `ε^{−nk}` of infinite order.

### Why the statement holds

**From Harris.** The statement evaluates `Φ ℓ ιΩ` only at primes `ℓ`
different from the residue characteristic `p_v` of `v`, and only at the local
components `P.localComponent v`, which are supercuspidal. For such `ℓ` and a
supercuspidal class `π`, take `Φ ℓ ιΩ (π) := σ(π)`, defined by (5.4)–(5.5)
for the `ℓ`-th correspondence and the identification of algebraic closures of
`𝐐` induced by `ιΩ`. This is legitimate because (5.4)–(5.5) are purely local
(p. 314). The Lean map `Φ` is total, so it also needs values at every other
prime and every other class. Give it arbitrary values there; the statement
never evaluates them. Take as witness Harris's family of (i). Theorem
5.9(ii), read through the continuous embeddings `j` as above, then gives the
conclusion.

**Independently, from Harris–Taylor.** This argument fixes every
normalization explicitly.

*Conventions.* `n = r + 1`. For a finite place `w` of `K`, `q_w` is its
residue cardinality and `Fr_w` is a geometric Frobenius element. Both the
Library (`IsGeometricFrobeniusLift` in `Langlands.Galois.CompatibleFamily`)
and Harris–Taylor (printed p. 19, where the Artin map sends uniformizers to
geometric Frobenius elements) use geometric Frobenius. `ε` is the `ℓ`-adic
cyclotomic character, so `ε(Fr_w) = q_w^{-1}` for `w ∤ ℓ`. In the Library, a
spectral system has Euler polynomials `∏_i (1 − α_{w,i} X)`
(`Eigenvalues.eulerPolynomial`). The standard Hecke operator `T_d` acts on the
spherical vector of the local component at `w` by
`standardHeckeScalar = q_w^{d(n−d)/2} e_d(α_w)` (module
`Langlands.Representation.Unramified.HeckeOperators`, through
`HasSphericalHeckeSpectrum`). So the `α_{w,i}` are the Satake parameters for
normalized induction. Weak association (`UnitaryMatchesSpectrum` in
`Langlands.Galois.WeakAssociation`) says that at all but finitely many places
`w`, `unitaryEulerPolynomial (ι P_w) = ∏_i (1 − α_{w,i} X)`. Here
`P_w ∈ L[X]` is the common Euler polynomial `det(1 − Fr_w X)`, and
`unitaryEulerPolynomial` divides each eigenvalue (reciprocal root) by its own
absolute value. In particular `|α_{w,i}| = 1` at those places. Purity of
weight `m` (`IsPureCompatible`, `IsPurePolynomial`) says that every complex
conjugate of every eigenvalue has absolute value `q_w^{m/2}`.

*Step 1: eigenvalues of a family as in (i).* Let `(L, ι, R, m)` satisfy the
three conclusions of 5.9(i). At all but finitely many `w`, and for every
place `λ` of `L` not over the residue characteristic of `w`, the eigenvalues
of `R_λ(Fr_w)` are, after `ι`, exactly `q_w^{m/2} α_{w,1}, …, q_w^{m/2} α_{w,n}`.
So `ι(tr R_λ(Fr_w)) = q_w^{m/2} Σ_i α_{w,i}`.

*Step 2: `m ≡ n − 1 (mod 2)` for every family as in (i).* Clozel (1990),
Théorème 3.13, printed p. 112 (checked against the page image): "Soit
`π ∈ Alg(n)`, `p` son type à l'infini. Supposons `π` régulière. Alors `π_f`
est définie sur un corps de nombres `E ⊂ ℂ`". The Library's
`IsRegularAlgebraic` is Clozel's regularity in `Alg(n)`: see "Agreement with
Clozel and Harris" in the Library's `Langlands/Automorphic/RegularAlgebraic.md`,
which uses Clozel's Définitions 1.8 (pp. 89–90) and 3.12 (p. 111). At an
unramified place `w`, `T_1` is the characteristic function of a double coset,
a finite integral combination of translates. So `T_1` acts on the
spherical line of `^σπ_w` by `σ(t_w)` for every `σ ∈ Aut(ℂ)`, where
`t_w = q_w^{(n−1)/2} Σ_i α_{w,i}` is its eigenvalue on `π_w`. An
`E`-structure on `π_f` gives `^σπ_f ≅ π_f` for every `σ ∈ Aut(ℂ/E)`, so
`σ(t_w) = t_w` for all such `σ`, and `t_w ∈ E`. By Step 1,
`ι(tr R_λ(Fr_w)) = q_w^{(m − n + 1)/2} t_w`, and the left side lies in `ι(L)`
because `P_w ∈ L[X]`. The function `tr R_λ` is continuous and equals `n ≠ 0`
at `1`, so it is nonzero on an open normal subgroup `Gal(K̄/M)`, with `M/K`
finite Galois. By Chebotarev, infinitely many places `w` of `K` of degree one
over `𝐐` split completely in `M`. They have infinitely many distinct residue
characteristics `p_w = q_w`, and at all but finitely many of them Step 1
applies and `tr R_λ(Fr_w) ≠ 0`. If `m − n + 1 = 2b + 1` were odd, then
`√p_w = ι(tr R_λ(Fr_w)) / (p_w^b t_w)` would lie in the number field `ι(L)E`
for infinitely many primes `p_w`. This is impossible, since
`𝐐(√p_1, …, √p_s)` has degree `2^s` for distinct primes.

*Step 3: twist to weight `1 − n`.* Let `k = (m + n − 1)/2`, an integer by
Step 2, and let `R' = R ⊗ ε^k`: on the `λ`-component, `ε` is the cyclotomic
character of the residue characteristic of `λ`, with values in
`ℤ_ℓ^× ⊂ L_λ^×`. Then `R'` is a collection over the same `L`, of rank `n`,
compatible with the Euler polynomials `P_w(q_w^{-k} X) ∈ L[X]`, and pure of
weight `m − 2k = 1 − n`. It is weakly associated at `ι` to the same
spectrum, because multiplying all eigenvalues by the positive real number
`q_w^{-k}` does not change their unitary normalization. So `R'` again
satisfies the three conclusions of 5.9(i), and the eigenvalues of
`R'_λ(Fr_w)` are, after `ι`, `q_w^{(1−n)/2} α_{w,i}`.

*Step 4: the Harris–Taylor representation.* Harris and Taylor (2001),
Theorem VII.1.9, printed pp. 226–227 (checked against the page images),
applies to a cuspidal `Π` of `GL_n` over a CM field (Harris–Taylor's `L`,
here `K`) with `Π^∨ ≅ Π^c`, whose infinite component has the infinitesimal character of an
algebraic representation, and which is square integrable at some finite
place. Here `K` is CM, `Π` is conjugate self-dual and regular algebraic, and
`Π_v` is supercuspidal, hence square integrable. Fix `ℓ ≠ p_v` and
`ιΩ : ℚ̄_ℓ ≅ ℂ`, and choose Harris–Taylor's square root `|·|^{1/2}` so that
`ιΩ ∘ |·|^{1/2}` is positive (§I.7, printed p. 57). Set
`R₀ := R_{ℓ,ιΩ}(Π)^∨`, the contragredient of Harris–Taylor's
representation. This is the fixed choice of dual. Item 1 of the theorem
gives `[R_{ℓ,ιΩ}(Π)|_{W_{K_y}}] = [r_ℓ(ιΩ^{-1}Π_y)]` for every finite place
`y ∤ ℓ`. By printed p. 6, `r_ℓ(χ) = χ^{-1} ∘ Art^{-1}` for a character `χ`,
and `r_ℓ(π) = ⊕_i r_ℓ(π_i) ⊗ |Art^{-1}|^{(g_i − g)/2}` for a subquotient
`π` of `n-Ind(π_1 × ⋯ × π_t)` (normalized induction with `|·|^{1/2}`,
printed p. 23). For unramified `Π_w` with Satake parameters `α_{w,i}` and
`w ∤ ℓ` (all `g_i = 1`, `g = n`), the eigenvalues of
`r_ℓ(ιΩ^{-1}Π_w)(Fr_w)` are therefore `ιΩ^{-1}(q_w^{(n−1)/2} α_{w,i}^{-1})`.
So for every Frobenius lift `φ` at such a `w`, the characteristic polynomial
of `R₀(φ)` is `∏_i (X − ιΩ^{-1}(q_w^{(1−n)/2} α_{w,i}))`.

Remark on the dual and on item 2. Without the dual, the unitary
normalization would give `∏_i (1 − α_{w,i}^{-1} X)`, the spectrum of
`Π^∨ ≅ Π^c` rather than of `Π`. Since `Π_w` is tempered (Corollary VII.1.11,
printed p. 232), the Frobenius eigenvalues `β` of `R_{ℓ,ιΩ}(Π)` at such
`w` satisfy `|ιΩ(β)|² = q_w^{n−1}`. Item 2 of Theorem VII.1.9 prints the exponent
`(g − 1)/2`, which is half-integral for `g = 2` and inconsistent with item 1.
This argument does not use item 2.

At `v`: since `ℓ ≠ p_v`, item 1 applies at `y = v`. The representation
`r_ℓ(ιΩ^{-1}Π_v)` is irreducible because `Π_v` is supercuspidal
(Corollary VII.2.18(1), printed p. 250). An irreducible class in the
Grothendieck group is represented only by that irreducible representation,
so `R₀|_{W_{K_v}} ≅ r_ℓ(ιΩ^{-1}Π_v)^∨`, which is irreducible. The Weil group
is dense in `Gal(K̄_v/K_v)` and `R₀` is continuous, so an intertwiner on
`W_{K_v}` intertwines on the whole decomposition group. Hence `R₀|_{Z_v}` is
the unique continuous extension of `r_ℓ(ιΩ^{-1}Π_v)^∨`, and it is
irreducible. Changing the embedding `K̄ → K̄_v` conjugates `Z_v` and does
not change these isomorphism classes.

*Step 5: comparison.* Let `lam` be a finite place of `L` and
`j : L_lam → ℚ̄_ℓ` a continuous field homomorphism with `ιΩ ∘ j = ι` on `L`.
At all but finitely many `w ∤ ℓ`, the characteristic polynomial of
`R'_lam(Fr_w)`, after `j`, is `∏_i (X − ιΩ^{-1}(q_w^{(1−n)/2} α_{w,i}))`, by
Step 3 and `ιΩ ∘ j = ι` on `L`. So the traces of `R'_lam ⊗_j ℚ̄_ℓ` and of
`R₀` agree at every Frobenius lift at these places. By Chebotarev these lifts
are dense in `Gal(K̄/K)`. Both traces are continuous for the `ℓ`-adic
topology of `ℚ̄_ℓ`, because `j` is continuous, so they agree everywhere.
Applied to powers, this shows that the characteristic polynomials agree
everywhere (characteristic zero). By Brauer–Nesbitt the two representations
have the same semisimplification. `R₀` is irreducible, because its
restriction to `Z_v` is. A representation whose semisimplification is
irreducible is itself irreducible and isomorphic to it, so
`R'_lam ⊗_j ℚ̄_ℓ ≅ R₀`.

*Conclusion.* For `ℓ ≠ p_v` and a supercuspidal class `π` of
`GL_n(F)`, `F = K_v`, let `Φ ℓ ιΩ (π)` be the continuous extension to
`Gal(F̄/F)` of `r_ℓ(ιΩ^{-1}π)^∨` (with `|·|^{1/2}` as in Step 4), when such
an extension exists. Give `Φ` arbitrary values at all other inputs. Take any
family `R` as in (i): its existence is Theorem 5.9(i) (Clozel, Kottwitz;
published as the unproved statement `Harris1999Theorem59iStatement`). The
witness is its twist `R'` from Step 3, which does not depend on `ℓ`, `ιΩ`,
`lam` or `j`. For every compatible `(ℓ, ιΩ, lam, j)` with `ℓ ≠ p_v`, Steps 4
and 5 give `(R'_lam ⊗_j ℚ̄_ℓ)|_{Z_v} ≅ R₀|_{Z_v} ≅ Φ ℓ ιΩ (Π_v)`. Restriction
to `Z_v` commutes with extension of scalars, so this is the conclusion.

The local component used is that of the supplied presentation `P`, the same
convention as in `HasSupercuspidalComponent` and in the published
`HarrisSupercuspidalLocalComparisonStatement`. For a genuine tensor
presentation of an irreducible cuspidal representation, it is isomorphic to
Harris's `Π_v`.

## `HarrisSupercuspidalRestrictionIrreducibleStatement`

Binders: `K`, `K₀`, `r ≥ 1` as above; a cuspidal class `c` and a finite place
`v`, with `c` regular algebraic and conjugate self-dual,
`Harris.conjPlace K v ≠ v` and `HasSupercuspidalComponent c v` (exactly the
hypotheses of `Harris1999Theorem59iStatement`). Then **for every** number
field `L`, embedding `ι : L →+* ℂ`, collection `R` and weight `m` with the
three conclusions of 5.9(i), and every finite place `lam` of `L` whose
residue characteristic differs from that of `v`, the representation of
`LocalGroup v` obtained from `atFinitePlace v R_lam` by extending scalars to
`AlgebraicClosure L_lam` is irreducible (`Representation.IsIrreducible`).


Unlike the parameter statement, this one is universal over families. It
holds by the following argument, which uses the steps above. Let `R` be a
family as in (i), of weight `m`, let `lam` be a finite place of `L`, and let
`ℓ ≠ p_v` be its residue characteristic. Choose a continuous field
homomorphism `j : L_lam → ℚ̄_ℓ`. It exists because `L_lam` is a finite
extension of `ℚ_ℓ` and `ℚ̄_ℓ` is algebraically closed, and every
`ℚ_ℓ`-linear map from a finite-dimensional `ℚ_ℓ`-space is continuous. Then
choose `ιΩ : ℚ̄_ℓ ≅ ℂ` extending the embedding `ι ∘ (j|_L)^{-1}` of `j(L)`
into `ℂ`. It exists because both fields are algebraically closed of
characteristic zero and of the cardinality of the continuum. By Steps 2, 3
and 5, with `k = (m + n − 1)/2`, `R_lam ⊗_j ℚ̄_ℓ ≅ R₀ ⊗ ε^{−k}`. Its
restriction to `Z_v` is the twist of the irreducible `R₀|_{Z_v}` by the
character `ε^{−k}`, so it is irreducible. Finally, `ℚ̄_ℓ` is algebraic over
`j(L_lam)` and algebraically closed, so `j` extends to an isomorphism
`AlgebraicClosure L_lam ≅ ℚ̄_ℓ`. This isomorphism identifies the two scalar
extensions semilinearly and matches their invariant subspaces. So the
extension of scalars to `AlgebraicClosure L_lam` is irreducible too.

Alternatively, Steps 2–5 applied to `R` and to Harris's family show that,
after `j`, the two differ by a power of `ε`. By Harris's (ii), Harris's
family restricts at `v` to `σ(Π_v)`, which is irreducible by Henniart
(p. 313).

## Scope

* Harris's `σ(π_v)` of (5.4)–(5.5) is not defined here. It needs the
  Drinfeld tower `ℳ_N` (formal `O_D`-modules and the Drinfeld–Rapoport–Zink
  moduli problem, and nonarchimedean analytic spaces with their étale sites).
  At Library commit
  `24390f9f` the Library has the level-one space `ℳ_1 = Ω × Δ` (module
  `Langlands.Geometry.Analytic.DrinfeldLevelOneBase`), but not the levels
  `ℳ_N` for `N ≥ 2` or the cohomology `H_c^{n−1}(ℳ̆_N, 𝐐̄_ℓ)` of (5.5). The
  canonical statements of Theorem 5.9(ii), Theorem 5.7(iii), Lemma 5.8,
  Corollary 5.10 and (5.3) need the tower and are not made here.
* Nothing is said about `Φ` beyond existence: not that it is given by a
  local Langlands correspondence, not that it is injective, not that it
  is compatible with twists (Lemma 5.8).
* The equality of the weights of the witnesses for two representations with
  the same local component, which
  `harrisSupercuspidalLocalComparison_of_canonical`
  (`Langlands.Galois.HarrisSupercuspidalLocalComparisonReduction`) needs to
  deduce `HarrisSupercuspidalLocalComparisonStatement` from the two
  statements here, is not stated here; that proof derives it. The witness constructed
  in the truth argument has weight `1 − n`, but the statement does not fix
  the weight.
* Stated only for coefficient places of residue characteristic different from
  that of `v`, as in Harris's (ii).

## Sources

* Harris (1999), literature id
  `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`: printed
  p. 313 (correspondence for each `ℓ` via an identification; Henniart's
  irreducibility; (5.4)–(5.5)), p. 314 ("purely local"), pp. 314–315
  (Theorem 5.9 and its proof).
* Harris and Taylor (2001), literature id
  `harris-taylor-2001-geometry-cohomology-simple-shimura` (PDF page = printed
  page + 8): printed p. 6 (`r_ℓ` and `rec`), p. 19 (geometric Frobenius and
  the Artin map), p. 23 (normalized induction), p. 57 (choice of `|·|^{1/2}`
  and `ι`), Theorem VII.1.9 (pp. 226–227), Corollary VII.1.11 (p. 232) and
  Corollary VII.2.18(1) (p. 250). Used in the truth argument.
* Clozel (1990), *Motifs et formes automorphes : applications du principe de
  fonctorialité*, in *Automorphic Forms, Shimura Varieties, and
  L-functions*, Vol. I, literature id
  `clozel-milne-automorphic-forms-shimura-varieties-l-functions-i-1990` (PDF
  page = printed page + 11): Définition 1.8 (pp. 89–90), Définition 3.12
  (p. 111) and Théorème 3.13 (p. 112). Used for the parity of the weight.
* Library modules for the normalizations: `Langlands.Galois.CompatibleFamily`,
  `Langlands.Galois.WeakAssociation`, `Langlands.Galois.UnitaryNormalization`,
  `Langlands.Representation.Unramified.Eigenvalues`,
  `Langlands.Representation.Unramified.HeckeOperators`, and the Markdown of
  `Langlands.Automorphic.RegularAlgebraic`.
