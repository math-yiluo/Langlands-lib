# Harris (1998), Theorem 1.2: compatible families weakly associated to `Reg(n, E)`

Author: Worker 34. This module states Harris's Theorem 1.2 over the Library's
actual cuspidal classes and genuine `λ`-adic Galois representations. The
statements are `Prop` definitions; nothing here proves them.

## Source

M. Harris, *The local Langlands conjecture for GL(n) over a p-adic field,
n < p*, Invent. Math. 134 (1998), 177-210, Section 1, printed pp.183-185.
Registered original `harris-1998-local-langlands`, SHA256
`7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`.

Theorem 1.2 (p.185, "mostly due to Clozel"): let `E` be a number field and
`π ∈ Reg(n, E)` with cuspidal spectrum `(nᵢ, πᵢ)`. Suppose

- (i) for each `i` there is a finite place `vᵢ` of `E` at which `π_{i,vᵢ}` is
  square-integrable; `pᵢ` is the rational prime below `vᵢ`;
- (ii) `E = E₀ K₀` with `E₀` totally real and `K₀` imaginary quadratic, and
  `πᵢ^∨ ≅ πᵢ ∘ c` for every `i`, where `c` is the nontrivial element of
  `Gal(E/E₀)`;
- each `pᵢ` splits in `K₀`.

Then `π ∈ C(n, E)`. Here (p.184) `Reg(n, E)` is the set of isobaric
representations all of whose cuspidal constituents `πᵢ` have archimedean
component of cohomological type ([C1, Def. 3.12] in Harris's references,
Clozel's *Motifs et formes automorphes*), "equivalently, `π_{i,∞}` has regular
infinitesimal character", and `C(n, E)` is the set of `π` to which some
compatible family `ρ` of dimension `n` is weakly associated (Definition 1.1).
On p.183 Harris assumes in practice that `ρ` is a sum of representations
`ρᵢ`, each pure of some weight.

## Library objects used

- The weak-association definitions of `Langlands/Galois/WeakAssociation`
  (this candidate) and the square-integrable components of
  `Langlands/Automorphic/SquareIntegrableComponent` (this candidate).
- `CuspidalOperatorRealization.IsoClass E r` (rank `r + 1`) and
  `PositiveRankCuspidalClass E` with its `rank` (published
  `CuspidalOperatorRealization`): actual irreducible cuspidal classes.
- `IsRegularAlgebraic` (published `Langlands/Automorphic/RegularAlgebraic`):
  the infinitesimal character is that of an irreducible algebraic
  representation (Clozel's regular algebraic type). The published Harris
  Proposition 4.8 statement uses the same predicate for `Reg(n, E)`.
- `IsConjugateSelfDual` (published `Langlands/Automorphic/ConjugateContragredient`):
  `π^∨ ≅ π ∘ c` for the CM conjugation `IsCMField.complexConj E`.
- `Harris.IsSplitImaginaryQuadratic p K₀` (published
  `Langlands/Global/Arithmetic/HarrisSetup`): `K₀` is imaginary quadratic and
  two distinct primes of `𝓞 K₀` contain `p`.
- `residueCharacteristic v`, `Collection`, `IsPureCompatible`, `HasRank`
  (published `Langlands/Galois/CompatibleFamily`).

## Statements

`Langlands.GaloisRepresentation.Harris1998Theorem12Statement` quantifies over

- a number field `E : Type uE` with instances `IsCMField E` and
  `CompactSpace (AdeleQuotient E)`. A field `E₀ K₀` as below is CM, so the
  first instance excludes no field allowed by Harris; it is needed to name the
  CM conjugation in `IsConjugateSelfDual`. The second is required by the
  published cuspidal classes and proved by the published
  `compactSpace_adeleQuotient`;
- intermediate fields `E₀ K₀` of `E/ℚ` with `E₀` totally real, `K₀` of degree
  2 and totally complex (imaginary quadratic), and `E₀ ⊔ K₀ = ⊤`, that is
  `E = E₀ K₀`;
- a finite index type `J : Type uJ` and cuspidal classes
  `c : J → PositiveRankCuspidalClass E`, the cuspidal spectrum `(nⱼ, πⱼ)`.

Its hypotheses are: every `c j` is regular algebraic (`π ∈ Reg(n, E)`); every
`c j` is conjugate self-dual (Theorem 1.2(ii)); and for every `j` there is a
finite place `v` of `E` at which `c j` has a square-integrable component and
whose residue characteristic splits in `K₀` (Theorem 1.2(i) with the splitting
assumption).

Its conclusion (`π ∈ C(n, E)`): there are a number field `L : Type uL`, an
embedding `ι : L → ℂ`, a finite set `excluded` of finite places of `L`, a
natural number `m`, collections `R k : Collection E L excluded` of genuine
`λ`-adic representations of `Gal(Ē/E)` with carriers in universe `uV`,
weights `w k : ℤ` and ranks `d k`, such that

- each `R k` is compatible and pure of weight `w k` (`IsPureCompatible`);
- each `R k` has rank `d k`, and `∑ₖ d k = ∑ⱼ nⱼ = n`;
- the direct sum `⊕ₖ R k` is weakly associated to the cuspidal spectrum
  (`PositiveRankCuspidalClass.IsSpectrumWeaklyAssociated`): every `c j` has an
  attached spectral system `sⱼ` (local factor carriers in universe `uW`), and
  for all but finitely many places `v` of `E` the unitary normalization at `ι`
  of the product of the common Euler polynomials of the `R k` is the product of
  the Euler polynomials of the `sⱼ`.

`Harris1998Theorem12CuspidalStatement` is the case of one cuspidal class
`c : CuspidalOperatorRealization.IsoClass E r` with one place `v`. Its
conclusion is the same with `∑ₖ d k = r + 1` and
`CuspidalOperatorRealization.IsoClass.IsSumWeaklyAssociated`. Harris remarks
(p.185) that it suffices to prove the theorem for cuspidal `π`; that reduction
is not proved here.

The helper theorem `complexConj_apply_of_mem_totallyReal` proves that the CM
conjugation of `E` fixes every element of a totally real intermediate field
`E₀`. When `E = E₀ K₀` with `K₀` imaginary quadratic, `[E : E₀] = 2` and the CM
conjugation is not the identity, so it is the nontrivial element `c` of
`Gal(E/E₀)` used in Theorem 1.2(ii). Only the fixing statement is proved in
Lean.

## Conventions and scope

- **Isobaric representations.** The Library has no isobaric sum construction.
  An isobaric `π` is determined by its cuspidal spectrum (Harris p.185), and
  Definition 1.1 compares only unramified Euler factors, whose product over the
  cuspidal spectrum is the factor of `π`. The statement is therefore made for
  the cuspidal spectrum itself. The isobaric representation is not
  constructed, and the uniqueness of `π` given its spectrum is not used.
- **Cohomological type.** `Reg(n, E)` asks for archimedean components of
  cohomological type. `IsRegularAlgebraic` encodes Clozel's regular algebraic
  condition: the infinitesimal character is that of an irreducible algebraic
  representation, which is the infinitesimal-character form of cohomological
  type that Harris paraphrases as "regular infinitesimal character". The
  equivalence with nonvanishing `(𝔤, K)`-cohomology for cuspidal
  representations is a theorem of Clozel that the Library does not prove; the
  published Proposition 4.8 statement makes the same choice.
- **Weights and normalization.** Harris (p.183) assumes "`ρ` to be the sum of
  representations `ρᵢ`, with each `ρᵢ` pure of some fixed weight `w`". The
  statement gives each summand its own existential weight `w k`. This is the
  weaker conclusion, and it is the one needed for an isobaric `π` whose
  cuspidal constituents have different weights. The unitary normalization
  treats each reciprocal root separately, so no single weight or
  half-integral twist is imposed. Frobenius is geometric.
- **Coefficients.** The coefficient field `L` and the finite set of excluded
  coefficient places are existential, as in Harris (pp.183-184). The
  embedding `ι : L → ℂ` is existential with them. Purity makes the
  normalization radii `|β|` independent of the embedding, but the normalized
  Euler polynomials can depend on `ι` (see `Langlands/Galois/WeakAssociation`),
  so the statement asserts association for the chosen `ι`.
- **Unramified matching only.** The conclusion is matching of Euler factors at
  almost all places. No ramified local compatibility is asserted, and no
  statement about the place `vⱼ` is made.
- **Reflex field.** The hypothesis `E = E₀ K₀` is retained. Harris notes
  (p.185) that for an arbitrary CM field one only obtains representations of
  the Galois group of a reflex field that in general properly contains `E`
  (Clozel 1991, Théorème 5.3); that variant is not stated here.
- **Provenance of the proof.** Harris attributes the theorem to Clozel (using
  Kottwitz's zeta functions and stable base change), to Taylor's removal of
  the multiplicity of `L^{S'}(s, π)^m`, and to Blasius and Clozel (1993,
  Theorem 2.6) for the bad-parity cases. These inputs are separate obligations
  of this task and are not asserted here.
