# Conditional two-block normalized matrix functional equation

Authors: Worker 33 (Lean statement) and Worker 264 (source reading, Markdown
and independent compilation check).

This module defines one proposition,
`Langlands.GodementJacquet.TwoBlockMatrixFunctionalEquationInductionStatement.{uF,uV}`.
It is a statement target, not a proof. It states the functional-equation part
of Godement–Jacquet Theorem 3.4 for two blocks of split general linear groups
over a p-adic field. The induced representation is the Library's actual
normalized parabolic induction. The hypotheses are the published block
normalized matrix functional-equation packages. The conclusion is the same
published package for the induced representation, with product polynomials,
product unit and summed exponent. The blocks may be reducible, so the
statement is conditional, as in the source.

## The statement

For every prime `p` and every `F : PadicField.{uF} p`, the canonical
realization `F.canonicalTopologicalData` supplies the topology, valuative
relation and nonarchimedean local-field structure of `F.Carrier`. The field
gets its Borel measurable structure `borel F.Carrier` with `BorelSpace`. These
are the data instances that the `Padic` wrappers of `GodementJacquet.AnalyticData`
install, so the hypotheses and the conclusion use the same structures.

Two more local instances, `T2Space F.Carrier` and
`TotallyDisconnectedSpace F.Carrier`, are installed only because
`HarmonicAnalysis.IsSelfDual` (in `HarmonicAnalysis/Basic`) requires
`LocallyCompactSpace`, `T2Space` and `TotallyDisconnectedSpace`.
`T2Space` is the published field `F.canonicalTopologicalData.fieldT2`.
`TotallyDisconnectedSpace` is derived from a `NonarchimedeanRing` instance by
the same inline proof as in the published
`LocalFactor/Abelian/SelfDualTransport`. All three classes are propositions,
so the choice of instance proofs does not change the meaning of `IsSelfDual`.
The sibling statement `TwoBlockMatrixAnalyticInductionStatement` obtains the
same instances through the right uniform structure and
`HarmonicAnalysis.rowFourierCutoff_nonarchimedean`. By proof irrelevance this
gives the same proposition.

The remaining quantifiers come in the order of the task contract.

1. `t : ℕ`, `m : Fin 2 → ℕ` and `h : ∑ i, (m i + 1) = t + 1`. The ambient
   group is `GL(t+1, F)`. The two blocks have actual ranks `m 0 + 1` and
   `m 1 + 1`. Both ranks are positive and otherwise unrestricted. The block
   shape is the published `RankinSelberg.succBlockShape m h`, whose `i`-th size
   is `m i + 1`.
2. A dependent family `V : Fin 2 → Type uV` with explicit instances
   `[∀ i, AddCommGroup (V i)]` and `[∀ i, Module ℂ (V i)]`, and actual
   representations
   `σ i : Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (V i)`.
   The premises `∀ i, IsSmooth (σ i)` and `∀ i, IsAdmissible (σ i)` follow
   immediately, in the canonical topology. The published `IsAdmissible` is
   `IsSmooth` together with finite generation of the invariants of every open
   subgroup. So the smoothness premise adds no restriction; it is kept because
   the contract lists it. No irreducibility and no Whittaker type is assumed.
3. `ψ : UnitaryAdditiveCharacter F.Carrier` and
   `ν : AdditiveHaarMeasure F.Carrier` with the premise
   `HarmonicAnalysis.IsSelfDual ψ ν`. The structure `UnitaryAdditiveCharacter`
   contains continuity and the field `nontrivial`, so nontriviality of `ψ` is
   part of the binder. `IsSelfDual ψ ν` says that for every Schwartz–Bruhat
   function on `F` the second Fourier integral converges and the Fourier
   transform applied twice is reflection. The same `ψ` and `ν` are passed to
   both block packages and to the induced package.
4. `ω : Fin 2 → HarmonicAnalysis.Quasicharacter F.Carrier`, bundled continuous
   homomorphisms `F.Carrierˣ → ℂˣ`, with
   `Classification.HasGLCentralCharacter F.Carrier (m i + 1) (σ i)
   (ω i : F.Carrierˣ →* ℂˣ)` for each `i`. This says
   `σ i (scalar a) v = ω i a • v` for every unit `a` and every vector `v` of
   the whole carrier `V i`, not only on some coefficient image.
5. Proposed polynomials `P PDual : Fin 2 → Polynomial ℂ`, units
   `c : Fin 2 → ℂˣ` and integers `a : Fin 2 → ℤ`, with the published package
   `GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData F ψ ν (σ i)
   (P i) (PDual i) (c i) (a i)` for each `i`.

The Lean binders are named `σ`, `P`, `ψ`, `ν`, `ω`. The contract writes
`sigma`, `Pi`, `psi`, `nu`, `omega`. The conclusion is exactly

```text
GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData F ψ ν
  (F.canonicalNormalizedProductInduced (RankinSelberg.succBlockShape m h) σ)
  (∏ i, P i) (∏ i, PDual i) (∏ i, c i) (∑ i, a i).
```

Since the index type is `Fin 2`, the constants are `P 0 * P 1`,
`PDual 0 * PDual 1`, `c 0 * c 1` and `a 0 + a 1`.

## The published package

For a representation `ρ` of `GL(n+1, F)`, the predicate
`Padic.NormalizedMatrixFunctionalEquationData F ψ ν ρ P PDual c a` is defined
in `GodementJacquet.AnalyticData`. It uses the canonical residue cardinality
`q`, the canonical normalized absolute value, and the canonical group Haar
measure `generalLinearHaar F.Carrier n`. It is the conjunction of three parts.

- `MatrixAnalyticAssertions` for `ρ` and `P`. First, one real bound such that
  for every full-matrix Schwartz–Bruhat test `Φ`, every actual bi-smooth matrix
  coefficient `f` of `ρ`, and every `s` to the right of the bound, the matrix
  integral `Z(Φ, s + n/2, f)` converges. Second, for every `Φ` and `f`, a
  rational function `R` with `HasShiftedRationalValue`. This is actual
  agreement of the shifted integral with `R(q^(-s))` on a right half-plane,
  where the denominator of `R` is also nonzero. Third,
  `IsNormalizedGenerator` for `P`: `P.coeff 0 = 1`, and the Laurent span of
  all these continuations equals the module generated by `P⁻¹`.
- `IotaMatrixAnalyticAssertions` for `ρ` and `PDual`: the same three
  conditions for the functions `coefficientIota f`, `g ↦ f(transpose(g⁻¹))`,
  where `f` ranges over the actual bi-smooth coefficients of the same `ρ`.
- For every test `Φ`, a Schwartz–Bruhat witness `ΦHat` with
  `MatrixFourierPair ψ ν Φ ΦHat`. That is, for every matrix `x` the function
  `y ↦ Φ(y) ψ(∑ i j, y i j * x i j)` is integrable for the product measure
  `rectangularMeasure ν (n+1) (n+1)`, and `ΦHat x` equals the integral.
  Then, for every coefficient `f` and all `R`, `RDual` with
  `HasShiftedRationalValue` for `(Φ, f)` and for `(ΦHat, coefficientIota f)`,
  the equation
  `NormalizedFunctionalEquation q P PDual 1 c 0 a R RDual` holds. Unfolded,
  for every `s ∈ ℂ` with `R.denom(q^(-s)) ≠ 0` and
  `RDual.denom(q^(-(1-s))) ≠ 0`,

  ```text
  PDual(q^(-(1-s))) · RDual(q^(-(1-s))) = c · (q^(-s))^a · P(q^(-s)) · R(q^(-s)).
  ```

  The scalar is `1` and the sign exponent is `0`, so no extra sign appears.

The constants `P`, `PDual`, `c` and `a` come before every test and coefficient.
The witness `ΦHat` is chosen for each `Φ` before the coefficient `f`.

In the hypotheses `ρ = σ i` and `n = m i`. In the conclusion
`ρ = F.canonicalNormalizedProductInduced (succBlockShape m h) σ` and `n = t`.
The block packages are premises only. The statement does not assert that they
exist for any block, irreducible or not.

## The induced representation

`F.canonicalNormalizedProductInduced (RankinSelberg.succBlockShape m h) σ` is
the published normalized induction `i(σ 0, σ 1)` of `Induction/BlockFactors`.
`GL(t+1, F)` acts by right translation on smooth functions `f` with
`f(p x) = δ_P(l)^(1/2) • (σ 0 (l 0) ⊗ σ 1 (l 1)) (f x)`. Here `P` is the
standard upper block-triangular parabolic with top-left block of size
`m 0 + 1`, and `l = (l 0, l 1)` is the Levi part of `p`. Its carrier lies in
`Type (max uF uV)`. No equivalent model replaces it, and the statement contains
no premise about it other than the block data.

The conclusion therefore asks for all three parts of the package for the
actual induced representation: both analytic assertions with generators
`P 0 * P 1` and `PDual 0 * PDual 1`, a Fourier witness for every full-matrix
test of rank `t+1` with the same `ψ` and the product of copies of the same `ν`,
and the functional equation with unit `c 0 * c 1` and exponent `a 0 + a 1`,
for every actual bi-smooth coefficient of the induced representation and
every pair of continuations, under both denominator guards.

## Original source and exact correspondence

The principal source is Roger Godement and Hervé Jacquet, *Zeta Functions of
Simple Algebras*, Lecture Notes in Mathematics 260 (1972), registered as
`godement-jacquet-1972-zeta-simple-algebras`, SHA256
`86a8900900504adeb5757a04b5bb8a8754e6ef00b0fff49754096d371f59d568`, retained
at
`/home/taskhub/central-library/Godement-Jacquet--Zeta functions of simple algebras (book)--1972.pdf`.
The one-based PDF page is the printed page plus 10.

- Printed pages 30–31 (PDF 40–41; page 31 checked visually) state
  Theorem 3.3. Assertion (4), printed page 31, is the functional equation
  `Ξ(Φ̂, 1-s, f̌) = (-1)^(m(d-1)) ε(s, π, ψ) Ξ(Φ, s, f)` for all coefficients
  `f` of `π`, all `Φ` and all `s`. Here `Ξ(Φ, s, f) = Z(Φ, s+(n-1)/2, f)/L(s, π)`
  and `f̌(g) = f(g⁻¹)`. The function `ε(s, π, ψ)` is "a constant times a power
  of `q^(-s)`". An Euler factor is `P(q^(-s))⁻¹` with `P(0) = 1`.
- Printed pages 33–34 (PDF 43–44) explain that the assertions of Theorem 3.3
  make sense for an admissible representation with a scalar central
  quasicharacter even if it is reducible. For such a representation they are
  not necessarily true.
- Printed page 36 (PDF 46, checked visually) states Theorem 3.4. `σ'` and
  `σ''` are admissible representations of `G'` and `G''`. They are not assumed
  irreducible, but have scalar central quasicharacters `ω'` and `ω''`, and
  `π = Ind(G, P, σ' × σ'')`. If the assertions of Theorem 3.3 hold for `σ'`,
  `σ''` and their contragredients, then they hold for `π` and `π̃`, with
  `L(s, π) = L(s, σ')L(s, σ'')`, `L(s, π̃) = L(s, σ̃')L(s, σ̃'')` and
  `ε(s, π, ψ) = ε(s, σ', ψ)ε(s, σ'', ψ)`.
- Printed page 37 (PDF 47, checked visually) notes that `π` may be reducible
  even for irreducible `σ'`, `σ''`, and puts `P` in the upper block form
  `p = (g' u; 0 g'')`. So `g'` corresponds to `σ 0` and `g''` to `σ 1`.

The formalized statement is the split case `H = F` of Theorem 3.4 with
`G = GL(t+1, F)`, `G' = GL(m 0 + 1, F)` and `G'' = GL(m 1 + 1, F)`. The
correspondence is as follows.

- Hypotheses. Admissibility of each block is `IsAdmissible (σ i)`. The scalar
  central quasicharacters are `ω i` with `HasGLCentralCharacter`. The
  assertions of Theorem 3.3 for each block and its contragredient are the
  block package: its two analytic parts give `L(s, σ_i) = P i(q^(-s))⁻¹` and
  the dual factor `PDual i(q^(-s))⁻¹`, and its functional-equation part is
  assertion (4) with `ε(s, σ_i, ψ) = c i · (q^(-s))^(a i)`. The nontrivial
  `ψ` and the self-dual `ν` are the source's standing choices.
- Conclusion. The assertions for `π` and `π̃` together with the two
  L-factor products are the two analytic parts with generators `P 0 * P 1`
  and `PDual 0 * PDual 1`. Assertion (4) for `π` with
  `ε(s, π, ψ) = ε(s, σ', ψ)ε(s, σ'', ψ)` is the functional-equation part. The
  product of the two monomials is
  `(c 0 · (q^(-s))^(a 0)) · (c 1 · (q^(-s))^(a 1)) = (c 0 * c 1) · (q^(-s))^(a 0 + a 1)`,
  which is why the induced unit is the product and the exponent is the sum.
- The sign. The source's sign `(-1)^(m(d-1))` involves the degree `d` of the
  division algebra. In split `GL` the degree is `d = 1`, so the sign is `1`.
  It does not become a sign involving the `GL` rank. The package records this
  through its central scalar `1` and sign exponent `0`.
- Not part of this statement: the central character `ω'ω''` of `π`
  (a consequence in the source), Proposition 3.5 (any number of blocks,
  printed pages 45–46), Corollary 3.6, and any existence of block data.

The source proof, which a future proof must reproduce for the actual Lean
objects, runs as follows. Printed page 38 (PDF 48, checked visually) takes
`dm = dx dy du dv` with `dm`, `dx`, `dy` self-dual and `du`, `dv` dual, and
proves Lemma 3.4.0: the Fourier transform of the partial integral
`φ_Φ(x, y) = ∫ Φ((x u; 0 y)) du` is `φ_Φ̂`. Printed pages 39–41 (PDF 49–51;
page 41 checked visually) write
`Ξ(Φ, s, f) = ∑ c_ij Ξ(Φ'_j, s, f'_i) Ξ(Φ''_j, s, f''_i)` with block tests
`Φ'_j`, `Φ''_j` and block coefficients `f'_i`, `f''_i`. Printed page 42
(PDF 52, checked visually) gives the same expansion for `Φ̂` and `f̌`, with the
block tests replaced by their Fourier transforms by Lemma 3.4.0, and compares
the block functional equations. This yields assertion (4) for `π` with the
ε-product. Printed pages 43–45 prove the generation statements, using
Lemma 3.4.6; these belong to the analytic part.

## Convention adaptation

The published predicates follow the transpose-adapted conventions of
H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika, *Automorphic Forms on
GL(3) I* (1979), printed page 177, one-based PDF page 10 (checked visually),
equations (1.1.1)–(1.1.2). This source is registered as `jps-1979-gl3-i`,
SHA256 `6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`,
retained at
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Automorphic Forms on GL(3) I--1979.pdf`.

- (1.1.1) is `Z(Φ, s, f) = ∫_G Φ(x) f(x) |det x|^s d^×x`. For rank `r` the
  integral `Z(Φ, s+(r-1)/2, f)` converges on a half-plane and is a rational
  function of `q^(-s)`. With `r = n+1` the shift `(r-1)/2` is the published
  `jpssShift n = n/2`. It is `t/2` for the induced representation and `m i/2`
  for block `i`. The rational variable is `spectralPoint q s = q^(-s)`.
- (1.1.2) is
  `Z(Φ^, 1-s+(r-1)/2, f^ι)/L(1-s, π^ι) = ε(s, π, ψ) Z(Φ, s+(r-1)/2, f)/L(s, π)`.
  The transformed integral is shifted to `1-s+(r-1)/2`, as in the Lean
  equation, where `RDual` is evaluated at `q^(-(1-s))`. With
  `L(s, π) = P(q^(-s))⁻¹` and the dual factor `PDual(q^(-s))⁻¹`, dividing by
  an L-factor is multiplying by the polynomial, which gives the displayed Lean
  equation.
- The Fourier transform is `Φ^(x) = ∫ Φ(y) ψ(Tr(y ᵗx)) dy`, with a plus sign.
  The published `MatrixFourierPair` uses
  `rectangularPairing y x = ∑ i, ∑ j, y i j * x i j`, which equals
  `Tr(y * transpose x)`, and the product measure built from the supplied `ν`.
  The local notation on printed page 173 (PDF 6), just before (0.3), uses the
  same transform on rectangular matrices with a self-dual Haar measure.
- The transformed coefficient is `f^ι(g) = f(g^ι)` with `g^ι = (ᵗg)⁻¹`
  ((0.4.3), printed page 174, PDF 7), which is `coefficientIota f`.
  By (0.4.4), on the same page, `ι` carries a standard parabolic subgroup to a
  lower one. JPS 1979 obtain `Φ^` from the transform of
  Godement–Jacquet by changing `x` into `ᵗx`. Accordingly the substitution
  `g ↦ ᵗg`, which preserves Haar measure and `|det g|`, turns the pair
  `(Φ̂, f̌)` of Godement–Jacquet into the pair `(Φ^, f^ι)`.

In its irreducible setting the 1979 source identifies `π^ι` with the
contragredient `π̃`. Here no such identification is made. The dual generator
`PDual` is defined through `coefficientIota` of the coefficients of the same
representation. For a reducible induced representation, a bridge between
these functions and the source's coefficients of `π̃` is a future proof
obligation, not a definitional equality. In particular, inverse transpose
carries the upper block parabolic to the lower one. Section 7 of the 1979
paper treats `GL(3)`; it is used here only for these conventions.

The task contract also names H. Jacquet, I. I. Piatetski-Shapiro and
J. A. Shalika, *Rankin–Selberg Convolutions* (1983), registered as
`jpss-1983-rankin-selberg`. Its Section 5, printed pages 420–423, applies
Theorem 3.4 to Whittaker models and generic constituents. This statement makes
no such passage. It does not assume a matrix functional equation on an
arbitrary reducible carrier; it is conditional on supplied block data.

## Measures

All matrix integrals use the canonical group Haar measure `generalLinearHaar`
fixed by the published `Padic` wrappers. The source uses some Haar measure
`d^×g`. Rescaling it multiplies both sides of the functional equation by the
same positive constant.

The additive measure is the supplied `ν` in every Fourier relation: on
`(m i + 1) × (m i + 1)` matrices for the blocks and on `(t+1) × (t+1)`
matrices for the induced representation, always as the product of copies of
`ν` over the entries. No other Fourier transform or Haar measure is selected.
Printed page 38 of Godement–Jacquet factors the self-dual matrix measure as
`dm = dx dy du dv`. The premise `IsSelfDual ψ ν` keeps the self-duality
hypothesis of the source for the future proof. No choice or rescaling of `ν`
takes place.

## Relation to the sibling statement

The sibling task `c5c9e4f6-1b39-4daa-97dc-b61b8645a760` states
`Langlands.GodementJacquet.TwoBlockMatrixAnalyticInductionStatement`, whose
conclusion is the first two parts of the induced package. Its future proof
can supply the analytic part of this conclusion. This statement keeps those
parts in its conclusion because it uses the full published package, but adds
no premise derived from the sibling. The sibling places the smoothness and
admissibility premises after the central characters. Here they follow `σ`,
as item 2 of the contract lists them. For a future proof this is only an
argument permutation.

## Internal packaging

The statement is a derived formulation, not a verbatim transcription. It uses
the published `AnalyticData` package for both the hypotheses and the
conclusion, the product of proposed polynomials for the L-factors, and the
product unit and summed exponent for the ε-factor. These choices follow the
task contract. They keep every part of the predicate: the common convergence
bounds, the actual continuation witnesses, the normalized generators for both
families, every full-matrix test, a Fourier witness chosen before the
coefficients, Fourier-integrand integrability, and both denominator guards.

## Universes and scope

The universes `uF` of the field and `uV` of the block carriers are
independent. The induced carrier lies in `Type (max uF uV)`. The development
check inspecting this declaration reports a `Prop`-valued declaration, level
parameters `uF, uV`, and only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

No existing Library Lean or Markdown file is changed. The module proves
nothing. It does not add irreducibility, Whittaker type, existence of
L- or ε-factors, an equivalence of induced representations, or the induced
functional equation as a premise. It asserts no existence of block packages,
no bridge from `coefficientIota` to a contragredient, no generalization to
more blocks, and no JPSS gamma or L certificate.

## Sources read and errata

Godement–Jacquet printed pages 29–47 were read in extracted text. Printed
pages 31, 36, 37, 38, 41 and 42 were also checked in rendered page images.
JPS 1979 printed pages 173–177 were read in extracted text, and printed
page 177 also in a rendered page image. No registered errata note for these sources was found in the Library
notes, project notes or literature locations consulted.
