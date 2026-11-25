# Reducing the Harris Frobenius comparison to Frobenius power traces

The declarations are in
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`. This module does not prove
`CMHarrisKottwitzTraceComparisonStatement`. It proves that statement from
one named premise, `CMHarrisKottwitzPowerTraceInputs`, which has the form of
Kottwitz's (5.5): an identity of traces of Frobenius powers. The file repeats
the parameter telescope of `HarrisTaylorCMKottwitzTraceComparison` verbatim,
including both derived-category universes `wS` and `wR`.

## The at-place input

`CMHarrisKottwitzAtPlacePowerTrace … ℓ lam πf v w a P` fixes a coefficient
place `ℓ`, a place `lam` of `K` above it, `π_f`, a finite place `v` of `F`,
integers `w`, `a` and `P ∈ K[X]`. It asserts the existence of:

- a field embedding `j : K_λ →+* ℂ`;
- for every degree `i ≤ 2(n − 1)`, a finite-dimensional `K_λ`-space `M i`
  with a linear automorphism `T i`;
- purity: every root of `charpoly (T i)` mapped by `j` is a Weil number of
  weight `i + w` for the residue cardinality at `v`
  (`Cohomology.Weights.IsWeilNumber`, at the complex realization `j`);
- an eventual trace identity: for every `k` at least some `N`,
  `Σ_i (−1)^i j(tr(T_i^k)) = a · Σ_{roots z of P at j|_K} z^k`
  (`complexPowerTrace` and `rootPowerSum`);
- degreewise: the actual level cohomology `CMHarrisLambdaCohomologyUnramifiedAt`
  holds at `v` in degree `i`, and, given `CMHarrisLambdaTowerFixedVectorComparison`
  in degree `i`, a `K_λ`-linear isomorphism from `M i` to the actual Hecke
  multiplicity space `cmHarrisLambdaTowerHeckeMultiplicity` in degree `i`
  that intertwines `T i` with the chosen geometric Frobenius
  `DecompositionGroupAction.geometricFrobenius` along
  `chosenClosureEmbedding` at `v`.

The automorphisms are supplied before the fixed-vector comparison is
assumed, exactly as the target's polynomial family `H` is. Only finitely
many exponents may be excluded; that suffices because the roots are nonzero.

`cmHarrisKottwitz_atPlace_of_powerTrace` assumes `P` monic with
`P(0) ≠ 0` and turns this input into the two at-place clauses of the target:
`CMHarrisKottwitzFrobeniusComparison` with `H i = charpoly (T i)` and
`CMHarrisKottwitzVirtualIdentity` at `j ∘ (K → K_λ)`. For the first clause,
finite-dimensionality of the actual multiplicity space follows from the
isomorphism, and the characteristic polynomials agree by
`FrobeniusPolynomial.charpoly_eq_of_comp_eq`. For the second, the private
lemma `charpoly_virtualIdentity_of_powerTrace` gives monicity from
`LinearMap.charpoly_monic`, nonzero constant terms from invertibility
(`charpoly_eval_zero_ne_zero_of_isUnit`), converts the operator traces to root
power sums by `complexPowerTrace_eq_rootPowerSum`, and concludes with
`alternatingPolynomial_eq_zpow_of_eventual_powerSums`.

## The uniform input and the assembly

`CMHarrisKottwitzPowerTraceInputs` has the binders of the target
(division, reflex, irreducibility, central weight, admissibility) and the
same quantifier structure. It asks for one `a` and one finite set `S`:

- for every `ℓ`, both derived-category instance families at universes
  `wS`, `wR`, and every `lam`: an auxiliary place `v` of `F` above a rational
  prime different from `ℓ` and a monic `P` of positive degree with `P(0) ≠ 0`
  satisfying the at-place input; and the vanishing of the actual Hecke
  multiplicity above degree `2(n − 1)` under the fixed-vector comparison;
- at every prime `p₀ ∉ S` satisfying the target's unramifiedness, chart,
  level and local-component hypotheses, if `a ≠ 0`: spherical irreducibility
  of `π_p`, and for every `θ`, `√p` and `P` with `IsKottwitzPolynomial`, the
  at-place input at `vθ` for every coefficient place `ℓ ≠ p₀` with Mathlib's
  standard derived categories, and the same at universes `wS`, `wR` for every
  allowed instance family.

`cmHarrisKottwitzTraceComparison_of_powerTraces` proves the exact published
`CMHarrisKottwitzTraceComparisonStatement.{wS, wR}` from this premise. For a
chart polynomial `P`, `P(0) ≠ 0` is proved, not assumed: by the definition of
`IsKottwitzPolynomial`, the image of `P` in `K̄[X]` is `kottwitzPolynomialOf`, the
characteristic polynomial of the matrix of an automorphism in
`kottwitzBasis`. The private lemma `kottwitzCharpoly_eval_zero_ne_zero`
evaluates `det(X − M)` at `0` and uses that the matrix is a unit; nonvanishing
descends along the injective map `K → K̄`. The target's standard-instance
witness at `vθ` needs a coefficient place away from `p₀`. The private lemma
`choose_coefficient_place_away_from` takes the rational place at `2` or at `3`,
whichever differs from it, and a place of `K` above it (`placeAbove`). The
witness is then supplied from the standard-instance clause of the premise.

## What remains

The premise is the content of Kottwitz's §5 on the actual Harris tower. It is
not proved here and must not be cited as proved. Its proof needs:

- smooth projective good-reduction models of the actual tame Harris tower at
  the auxiliary and chart places, with the Hecke and generic-fibre
  comparisons (interface `CMHarrisTameIntegralTower`; prerequisite
  definitions: the prime-to-`p` PEL objects and the determinant datum of
  Kottwitz's integral Harris moduli problem);
- extension of the Harris coefficient sheaves, smooth proper
  specialization, and the identification of the Frobenius action on stalks
  (Kottwitz, *Points on some Shimura varieties over finite fields*, §16 and
  Lemma 18.1);
- Deligne's purity for the Weil-number condition;
- the Hecke-projected geometric trace (5.1), its comparison to the
  automorphic side (5.2)–(5.5) by the stable trace formula, the fundamental
  lemma for unramified base change, pseudo-coefficients at infinity and
  Lemma 4.2, together with the normalization identifying Kottwitz's
  `P(π_p, E_v)` with `IsKottwitzPolynomial`;
- the comparison between the whole Harris moduli space (a union of
  `|ker¹(ℚ, G)|` copies of the canonical model, Kottwitz JAMS §8 p. 400 and
  (19.5)–(19.6) p. 442) and the trace computation.

## Sources

R. E. Kottwitz, *On the λ-adic representations associated to some simple
Shimura varieties*, Invent. Math. 108 (1992), 653–665, registered
`kottwitz-1992-lambda-adic-simple-shimura`, SHA-256
`749af5541a59187e6f9d1089dec9a0e591a2059173da739c7384ff3a7d0dd799`: §5,
printed pp. 661–663 ((5.1)–(5.6)); §6, p. 664 ((6.1)). R. E. Kottwitz,
*Points on some Shimura varieties over finite fields*, J. Amer. Math. Soc. 5
(1992), 373–444, registered `kottwitz-1992-points-shimura-finite-fields`,
SHA-256 `c7cede3d0a5e201068e6100acbb3832adb67767d69248ec65458e7cc74ee46f1`:
§8, pp. 398–400; §19, pp. 440–442. The reduction is an internal derivation;
it adds no new mathematical claim from the sources.
