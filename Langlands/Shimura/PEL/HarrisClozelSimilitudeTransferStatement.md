# Clozel's transfer to the similitude group and the occurrence in the middle degree

This module states two inputs of the geometric endpoint
`Langlands.GaloisRepresentation.HarrisEvenGeometricMultiplicityStatement` of Harris's
Theorem 1.2 with multiplicity: Clozel's transfer of a conjugate self-dual cuspidal class
to the similitude group of a division algebra with involution, with the unramified
matching at the good places, and the occurrence of the transferred finite part in the
middle degree of the cohomology of the CM Shimura tower. It proves that the second
statement implies the first. Neither statement is proved here.

All declarations are in namespace `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel` and use
the variables of the module `HarrisTaylorCMKottwitzRegularStatement`, with the rank
written `n = r + 1`: the totally real field `E`, the CM field `F` (a quadratic extension
of `E`), the imaginary quadratic field `L` with an embedding `τ₀ : L → ℂ`, the central
simple algebra `A` with `Module.Finite ℚ A`, the datum
`D : CentralSimpleUnitaryData E F A (r + 1)` and Harris's charts
`C : HarrisSignatureCharts D.toSecondKindInvolution (r + 1) (harrisCMSection E (algebraMap L F) τ₀)`,
whose distinguished real place `τ₁ = C.distinguished` carries the signature `(n − 1, 1)`.
The second statement also uses the geometric prerequisites of the tower (`preservation`
through `htor`), the representability `q`, the relative dual statements `existence` and
`geometry`, and the rigidity `hRigid`, as there. Throughout, `Φ τ₁` is the distinguished
embedding of `F` and `v_θ = harrisPlace p₀ θ (Φ τ₁)` is the place of `F` above `p₀` cut out
by `θ : ℂ → ℚ̄_{p₀}` through it.

## Definitions

- `IsClozelSimilitudeTransfer D C c j πf ρ U`, for a cuspidal class `c` of `GL_{r+1}`
  over `F` (with `CompactSpace (AdeleQuotient F)`), a number field `K` with an embedding
  `j : K → ℂ`, a `K`-linear representation `πf` of the finite adelic points of the
  similitude group on `V`, an algebraic representation `ρ` of the similitude group over
  `K` on a finite-dimensional `W`, and a small level `U : SmallCMLevel D`. It is the
  conjunction of:
  - `πf` is admissible (`Langlands.IsAdmissible`) and irreducible after extension of
    scalars to `K̄`;
  - `ρ` is irreducible after extension of scalars to `K̄` and of regular highest weight
    (`AlgebraInvolution.IsRegularHighestWeight (r + 1) ρ`);
  - there are a finite set `S₁` of primes, a Hecke character `μ` of `F` that is algebraic
    (`Harris.IsAlgebraic`: its archimedean component is the character of an integral
    infinity type) and a spectrum `s` of `c` (`HasSpectralSystem.{0, 0} c s`) such that, at
    every prime `p₀ ∉ S₁` at which `F` is unramified, for every unramified chart at `p₀`
    whose level is the `p₀`-component of `U`, every local component `π_{p₀}` of `πf`
    (`πf ≅ π_{p₀} ⊗ π^{p₀}`), every `θ` and the place `w = v_θ` outside the exceptional set
    of `s`: `π_{p₀}` is spherical for the chart (`IsSphericalIrreducible` over `K̄`); a
    Kottwitz polynomial `P(π_{p₀}, F_w)` exists (`IsKottwitzPolynomial` for Kottwitz's
    function `C.hodgeFunction` of the charts, for some square root of `p₀` in `K̄`); and
    every Kottwitz polynomial `P ∈ K[X]` satisfies, for every uniformizer `ϖ_w` of `F_w`,

    ```
    roots of j(P) = { q_w^{(n−1)/2} · μ_w(ϖ_w) · tᵢ },
    ```

    as multisets, with `tᵢ` the eigenvalues of `s` at `w`, `q_w` the residue cardinality of
    `w` and `μ_w` the component of `μ` at `w`.

  Clozel's construction (Clozel 1991, §5.2–§5.3) attaches to `c` an automorphic
  representation `τ` of the similitude group (Lemma 5.6, printed p. 137): `ρ` is the
  coefficient system for which `τ` has nonzero `(𝔤, K_∞)`-cohomology ((5.18), printed
  p. 139, and printed p. 143), and `πf` is the finite part of `τ`, realized over a number
  field. Kottwitz (1992, printed p. 655) works in the same way with a number field, a
  coefficient system over it and an admissible representation of `G(𝔸_f)` over it; the
  finite part of `τ` occurs in the cohomology with coefficients in the local system of
  `ρ`, whose Hecke modules are finite-dimensional over the field of definition of `ρ`.
  Regular highest weight of `ρ` comes from that of `c`. The matching clause is
  Clozel's unramified matching: Proposition 4.11(i) (printed pp. 129–130) matches the
  descended representation with `c` at the unramified places; Lemma 5.6 (printed
  pp. 137–138) and the Hecke algebra homomorphism (5.17) (printed p. 138) carry it to the
  similitude group; and (5.27)–(5.31) (printed p. 141), with the changes of §5.3 for a
  CM base field (printed pp. 142–144), express Kottwitz's polynomial through the Satake
  parameters of `c`. The factor `q_w^{(n−1)/2}` is Kottwitz's twist by `Z` in
  `V(π_p, E_v)` (Kottwitz 1992, printed p. 656, with `dim S_K = n − 1`). The scalar
  `μ_w(ϖ_w)` collects the central character of `c`, the character `β` of Clozel's
  construction and the central character `χ` of the similitude representation, which is
  not of finite order when Clozel's parity `P` of (5.33) is odd (printed pp. 143–144);
  the clause asks only that it be the value at `w` of one algebraic Hecke character.
  Clozel's place `u` (printed p. 141) is the place of his CM field below the place of
  the reflex field given by `θ`, read through his embedding `ι₀`. For `n ≥ 3`, equality of
  his signature function with `C.hodgeFunction` forces `ι₀` to be the conjugate of `Φ τ₁`,
  so `u` is the conjugate of `v_θ`, and under conjugate self-duality of `c` the inverse
  Satake matrix of (5.27)–(5.28) at `u` is, up to permutation, the Satake matrix of `c` at
  `v_θ`. For `n = 2` the inverse of a pair of parameters is the pair divided by its
  product, so the two labellings differ by a scalar, which the clause absorbs into `μ`.
- `ClozelSimilitudeTransferStatement D C` (**Clozel's transfer to the similitude
  group**). Hypotheses, as binders: `CompactSpace (AdeleQuotient F)`; `D.IsDivision`;
  `3 ≤ r + 1` or a real place of `E` other than `τ₁` (the condition of the Kottwitz
  statements); a finite place `v₀` of `E` split in `F` (`IsSplitPlace E F v₀`) above
  which the algebra is divided (`IsDivisionAbove v₀`, at both places of `F` above `v₀`),
  with `D` quasi-split (`IsQuasiSplitAt`) at every other finite place of `E`, which is
  the form of the output of `Langlands.Shimura.FiniteUnitary.ClozelOnePlaceExistenceStatement`;
  a cuspidal class `c` of `GL_{r+1}` over `F` of regular highest weight
  (`HasRegularHighestWeight`), conjugate self-dual (`IsConjugateSelfDual`) and with a
  supercuspidal component at a place `w` of `F` above `v₀`
  (`HasSupercuspidalComponent.{0, 0}`). Conclusion: there are `K`, `j`, `V`, `πf`, `W`, `ρ`
  and a small level `U` with `IsClozelSimilitudeTransfer D C c j πf ρ U`.

  Source: Clozel 1991, Théorème 3.3(i) and Corollaire 3.4 (printed p. 108, the transfer
  to the division algebra and its stability under the involution, which the Library
  states as `Langlands.Shimura.HarrisClozel.HarrisClozelGlobalJLStatement` and
  `Langlands.Shimura.HarrisClozel.HarrisClozelInvolutionStabilityStatement`),
  Proposition 4.11 (printed pp. 129–130, the stable descent to the unitary group),
  Lemma 5.6 and (5.17)–(5.18) (printed pp. 137–139, the extension to the similitude group
  and the coefficient system) and §5.3 (printed pp. 142–144, a CM base field).
  Théorème 3.3(i) asks for components square-integrable at the places where the algebra
  is divided; the supercuspidal component at `w` gives square-integrable components at
  both places above `v₀` (the component at the conjugate place is supercuspidal by
  conjugate self-duality, the central character of `c` is unitary, and a unitarizable
  supercuspidal representation is square-integrable). For an odd parity `P` the central character `χ`
  of the similitude representation is not trivial on `A_G`; the transfer is then read
  with essentially unitary representations, as in Kottwitz's remark on printed p. 658.
- `CMHarrisMiddleDegreeOccurs … ρ πf U` (the occurrence in the middle degree): for every
  prime `ℓ`, every choice of the derived-category instances on the étale module sheaves
  of the tower with coefficients `HarrisCoefficientIntegers K ℓ` and on
  `ModuleCat.{0} (HarrisCoefficientIntegers K ℓ)`, and every place `λ` of `K` above `ℓ`, the
  fixed-vector comparison in degree `r = n − 1`
  (`CMHarrisLambdaTowerFixedVectorComparison`) implies that the Hecke multiplicity space
  `cmHarrisLambdaTowerHeckeMultiplicity` of `πf ⊗_K K_λ` in degree `r` at `U` is nonzero
  (`Nontrivial`). Under the fixed-vector comparison it is Kottwitz's multiplicity space
  `W^{n−1}(π_f)_λ = Hom_{𝓗_U}(π_f^U, H^{n−1}(S_U, ρ)) ⊗_K K_λ` (Kottwitz 1992, printed
  p. 655). This is the same multiplicity space whose nontriviality
  `CMHarrisKottwitzRegularMiddleDegreeStatement` relates to `a ≠ 0`.
- `ClozelMiddleDegreeOccurrenceStatement …` (**Clozel's transfer with the occurrence in
  the middle degree**). The hypotheses of `ClozelSimilitudeTransferStatement`; the
  conclusion adds to `IsClozelSimilitudeTransfer D C c j πf ρ U` the occurrence
  `CMHarrisMiddleDegreeOccurs … ρ πf U` for the same `πf`, `ρ` and `U`.

  Source: Clozel 1991, (5.18) (printed p. 139) and printed p. 143, the nonvanishing of
  `H^*(𝔤, K_∞; τ ⊗ ρ)` for the representation `τ` with finite part `π_f`; Kottwitz 1992,
  printed p. 655 (Matsushima's formula
  `W^i(π_f) ⊗ ℂ ≅ ⊕_{π_∞} m(π_f ⊗ π_∞) H^i(𝔤, K_∞; π_∞ ⊗ ρ)`) and printed p. 658 (for a
  regular highest weight the cohomology is concentrated in degree `dim S_K = n − 1`, by
  Vogan–Zuckerman 1984, Theorems 5.5 and 5.6, printed pp. 74–75). The occurrence of `τ`
  in the discrete spectrum with nonzero cohomology, concentrated in degree `n − 1`, makes
  `W^{n−1}(π_f)` nonzero at every level `U` with `π_f^U ≠ 0`, and the comparison of the
  `λ`-adic cohomology with the cohomology of the complex points together with the
  fixed-vector comparison carries this to the Library's multiplicity space. The statement
  asks for one transfer `(πf, ρ, U)` with both properties, because the occurrence is a
  property of the automorphic representation `τ` and not of the unramified matching
  alone.

## Proved result

- `clozelSimilitudeTransfer_of_middleDegreeOccurrence`:
  `ClozelMiddleDegreeOccurrenceStatement … → ClozelSimilitudeTransferStatement D C`. The
  proof forgets the occurrence clause.

## Sources

- L. Clozel, *Représentations galoisiennes associées aux représentations automorphes
  autoduales de `GL(n)`*, Publ. Math. IHÉS 73 (1991), Théorème 3.3(i) and Corollaire 3.4
  (printed p. 108), Proposition 4.11 (printed pp. 129–130), Lemma 5.6 and (5.17)–(5.18)
  (printed pp. 137–139), (5.27)–(5.31) (printed p. 141), §5.3 (printed pp. 142–144).
  Registered `clozel-1991-selfdual-galois`.
- R. E. Kottwitz, *On the λ-adic representations associated to some simple Shimura
  varieties*, Invent. Math. 108 (1992), printed pp. 655, 656 and 658. Registered
  `kottwitz-1992-lambda-adic-simple-shimura`.
- D. A. Vogan, Jr. and G. J. Zuckerman, *Unitary representations with non-zero
  cohomology*, Compositio Math. 53 (1984), Theorems 5.5 and 5.6, printed pp. 74–75.
  Registered `vogan-zuckerman-1984-unitary-nonzero-cohomology`.
