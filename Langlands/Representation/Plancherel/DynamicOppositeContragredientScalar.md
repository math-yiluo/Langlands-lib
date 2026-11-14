# Contragredient invariance of the scalar `j` (targets)

Worker 5. The module
`Langlands.Representation.Plancherel.DynamicOppositeContragredientScalar` states
two Prop-valued targets for the Library's actual opposite standard integrals
`J_{P̄|P}` and `J_{P|P̄}` (module `DynamicOppositeStandardIntertwining`):

- `ConditionalDynamicOppositeDualAdjunctionStatement`, the bilinear
  adjunction IV.1 (11) with the smooth contragredient, on the convergence
  domains;
- `ConditionalDynamicOppositeContragredientScalarStatement`, Waldspurger's
  IV.3 (2) `j(π̌) = j(π)` for the canonical scalar
  `conditionalCanonicalRationalScalar`.

Neither target is proved here. The module proves elementary facts about
inversion `z ↦ z⁻¹` of the unramified parameter. It defines the
compact-picture duality pairing. It proves that the second target implies
the same invariance for the density `plancherelDensity`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082, registered as `waldspurger-2003-plancherel`, PDF
SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

- IV.1 (11), printed p.283 / PDF p.49: for all `f ∈ I_P^G V` and
  `f̌' ∈ I_{P'}^G V̌`, `⟨J_{P'|P}(π) f, f̌'⟩ = ⟨f, J_{P|P'}(π̌) f̌'⟩`. Here
  the operators are rational functions of `π` on the orbit `O_ℂ`, and
  `⟨ , ⟩` is the `G`-invariant duality between `I_P^G V` and `I_P^G V̌`.
- IV.3 (2), printed p.286 / PDF p.52: `j(π) = j(π̌)`, "Cela résulte de
  IV.1 (11)". Here `j = j_P` is the rational function on `O_ℂ` such that
  `J_{P|P̄}(π') J_{P̄|P}(π')` is multiplication by `j_P(π')` when
  `I_P^G V'` is irreducible (start of IV.3, printed p.285 / PDF p.51).
- Lemma V.2.1, printed p.292 / PDF p.58, fourth item: `μ(ω̌) = μ(ω)` for
  `μ(ω) = j(ω)⁻¹ ∏_α γ(M_α|M)²`. The proof (printed p.293 / PDF p.59) cites
  IV.3 (2), (3), (5) and (6).
- Waldspurger's `K` (fixed in I.1) is a special maximal compact subgroup in
  good position relative to the minimal Levi subgroup, so
  `K ∩ P = (K ∩ M)(K ∩ U)` for every semistandard parabolic `P = MU`.

## Provenance

Both targets are derived statements adapted to the Library's data.

**Parameters.** The Library parametrizes the orbit of `A ⊗ z` by unramified
characters `z` of the dynamic centralizer `M = Z_G(χ)`. Since
`(π ⊗ χ)ˇ ≅ π̌ ⊗ χ⁻¹`, the point `π̌` of Waldspurger's contragredient orbit
corresponds to `Ǎ ⊗ z⁻¹` when `π` corresponds to `A ⊗ z`. So IV.1 (11)
pairs the parameter `z` of the integral for `A` with the parameter `z⁻¹` of
the integral for `Ǎ`. IV.3 (2) becomes `j_P(Ǎ ⊗ z⁻¹) = j_P(A ⊗ z)`: as
rational functions, the scalar for `Ǎ` equals the scalar for `A` composed
with inversion of the parameter.

**Convergence domains.** The Library has the integrals only on their
convergence domains (the families `conditionalForwardCompactFamily` and
`conditionalReverseCompactFamily` on `forwardFullDomainRegion` and
`reverseFullDomainRegion`), not their continuations as operators. The
adjunction target is therefore stated on the convergence domains, with an
explicit hypothesis `hz` that `z⁻¹` lies in the relevant domain for `Ǎ`.
The Library does not prove that inversion maps the domain for `A` into the
domain for `Ǎ`. For the same reason the scalar target has the hypotheses
`_hinvForward` and `_hinvReverse`.

**Pairing and normalization.** The pairing of compact pictures is
`⟨φ, φ̌⟩ = ∫_K φ̌(k)(φ(k)) dk` against the Haar probability measure
`CompactInduction.measure K hK`. This is the normalization of the Library's
duality of normalized inductions:
`CompactInduction.integralDualEquiv_pairing` (module
`CompactNormalizedInductionDuality`) writes the contragredient pairing of
`I_P^G A` in exactly this form. The integrals use the source measures
`forwardQuotientMeasure` and `reverseQuotientMeasure`, which give `K ∩ Ū`
and `K ∩ U` volume `1`.

**The constant.** The computation is the one in the Markdown of
`DynamicOppositeHermitianAdjunctionStatement`, with the Hermitian form
replaced by the duality. Let `f` be a section of the `P`-induction of
`A ⊗ z` and `f̌'` one of the `P̄`-induction of `Ǎ ⊗ z⁻¹`. Then
`Ψ(g) = f̌'(g)(f(g))` is left `M`-invariant: the characters `z` and `z⁻¹`
cancel, the contragredient pairing is `M`-invariant, and the half-moduli of
`P` and `P̄` are inverse on `M`. Since `f̌'` is left `Ū`-invariant, the left
side of the first identity is `∫_K ∫_Ū Ψ(ū k) dū dk`. Since `f` is left
`U`-invariant, the right side is `∫_K ∫_U Ψ(u k) du dk`. Fix Haar measures
with `vol(K) = 1` on `G` and `vol(K ∩ M) = 1` on `M`, and write `m` for the
Levi projection. Unfolding `∫_G = ∫_P ∫_K` with the left Haar measure
`dm du / [m(K ∩ P) : K ∩ M]` on `P` shows that the right side is
`[m(K ∩ P) : K ∩ M]` times the integral of `Ψ` over `M\G`. In the same way
the left side is `[m(K ∩ P̄) : K ∩ M]` times that integral. So the first
identity holds up to the factor `[m(K ∩ P̄) : K ∩ M] / [m(K ∩ P) : K ∩ M]`,
and the second up to its inverse. The factor is `1` under the hypotheses
`_hKsplit` and `_hOppKsplit`, which say that the Levi projections send
`P ∩ K` and `P̄ ∩ K` into `K`. They are the Lean form of Waldspurger's
property `K ∩ P = (K ∩ M)(K ∩ U)` and its analogue for `P̄`. Without them
the factor can differ from `1`, so they are hypotheses of the adjunction
target.

The scalar target also carries the split hypotheses, because its intended
proof goes through the adjunction target. The two factors are inverse to
each other and `j_P` uses both directions, so the scalar identity is
expected to hold without them. This is not claimed.

Absolute convergence of both sides follows from the definition of the full
domains: every section has absolutely convergent smooth-dual scalar
integrals (`standardIntertwiningFullDomainRegion`). The double integral
over `K × Ū` reduces to finitely many integrals over `Ū`, because the
sections are right invariant under an open subgroup of `K`.

## Inversion of the parameter

Generic part, for `ν : I → (G →* ℝ≥0ˣ)`:

- `unramifiedCharacters_inv_val_apply`: `χ⁻¹(g) = χ(g⁻¹)`.
- `inv_mem_unitaryUnramifiedCharacters`: inversion preserves unitarity.
- `unramifiedRegularInversion ν`, the `ℂ`-algebra automorphism
  `b ↦ (χ ↦ b(χ⁻¹))` of `unramifiedRegularFunctions ν`. It preserves the
  algebra because it sends the generator `unramifiedEvaluationRegular ν g`
  (evaluation `χ ↦ χ(g)`) to the generator for `g⁻¹`.
  Proved: `unramifiedRegularInversion_apply` (`(σ b)(χ) = b(χ⁻¹)`),
  `unramifiedRegularInversion_symm` (it is its own inverse),
  `unramifiedRegularInversion_evaluation`, and
  `unramifiedRegularInversion_unramifiedRegularInversion`.

On the actual field of rational functions `rationalUnramifiedFunctionField G
hp hG` of a connected reductive `G`:

- `rationalUnramifiedFunctionFieldInversion G hp hG`, the ring automorphism
  `f ↦ (χ ↦ f(χ⁻¹))`. It is the extension of `unramifiedRegularInversion` to
  the fraction field (`IsFractionRing.ringEquivOfRingEquiv`).
  Proved: `rationalUnramifiedFunctionFieldInversion_algebraMap`, `_constant`
  (complex constants are fixed) and `_involutive`.
- `unramifiedRegularInversion_val_inv`: `(σ b)(z⁻¹) = b(z)`.
- `rationalFunctionRegularAt_inversion_iff` and
  `rationalFunctionNonnegAt_inversion_iff`: `σ f` is regular at `z`, or
  regular with a nonnegative real value there, exactly when `f` has the
  same property at `z⁻¹`.

## The pairing

For `h : IsSemidirectDecomposition P M U`, a compact open subgroup `K` with
`hK : IsCompact K`, a smooth complex representation `A` of `M`, a section
`φ` in `CompactInductionPicture h K A` and a section `φ̌` in
`CompactInductionPicture h K A.contragredient`,
`compactPictureDualPairing h K hK A φ φ̌` is

```
∫ k : K, smoothDualPairing A.representation (eval φ̌ k) (eval φ k) ∂CompactInduction.measure K hK.
```

Here `A.contragredient` is the Library's smooth contragredient
(`SmoothRep.contragredient`), whose carrier is the space of smooth vectors
of the algebraic dual. The module defines the pairing and proves nothing
about it.

## The adjunction target

`ConditionalDynamicOppositeDualAdjunctionStatement` quantifies over:

- a nonarchimedean local field `F` and an affine group scheme `G` over `F`
  of locally finite type, a cocharacter `χ : 𝔾_m → G`, the structural
  premises `hRefl`, `hCST` and `hG : IsConnectedReductive G` used by the
  Library's integrals, with `P = parabolic χ`, `P̄ = oppositeParabolic χ`
  and `M = levi χ`;
- a compact open subgroup `K` of `G(F)` with `G(F) = P K` (`hPK`) and
  `G(F) = P̄ K` (`hOppK`);
- the split hypotheses `_hKsplit` and `_hOppKsplit`: for `p ∈ P ∩ K`,
  `(decomposition χ).projection p ∈ K`, and the same for `P̄`;
- a smooth complex representation `A` of `M(F)`.

Its conclusion is the conjunction of two statements:

1. For `z ∈ forwardFullDomainRegion χ K hK A` with
   `hz : z⁻¹ ∈ reverseFullDomainRegion χ K hK A.contragredient`, `φ` in the
   compact picture of `A` for `P` and `φ̌'` in the compact picture of `Ǎ` for
   `P̄`:
   `⟨J_{P̄|P}(A ⊗ z) φ, φ̌'⟩_{P̄} = ⟨φ, J_{P|P̄}(Ǎ ⊗ z⁻¹) φ̌'⟩_P`.
2. For `z ∈ reverseFullDomainRegion χ K hK A` with
   `hz : z⁻¹ ∈ forwardFullDomainRegion χ K hK A.contragredient`, `ψ` in the
   compact picture of `A` for `P̄` and `ψ̌'` in the compact picture of `Ǎ` for
   `P`:
   `⟨J_{P|P̄}(A ⊗ z) ψ, ψ̌'⟩_P = ⟨ψ, J_{P̄|P}(Ǎ ⊗ z⁻¹) ψ̌'⟩_{P̄}`.

Here `J_{P̄|P}(A ⊗ z) = conditionalForwardCompactFamily … A z`,
`J_{P|P̄}(Ǎ ⊗ z⁻¹) = conditionalReverseCompactFamily … A.contragredient
⟨z⁻¹, hz⟩`, similarly in the second statement, and `⟨ , ⟩_P`, `⟨ , ⟩_{P̄}`
are `compactPictureDualPairing` for `decomposition χ` and
`oppositeDecomposition χ`. Both directions are IV.1 (11), with
`(P, P') = (P, P̄)` and `(P̄, P)`.

## The scalar target

`ConditionalDynamicOppositeContragredientScalarStatement` has the same
data `F`, `G`, `χ`, `hRefl`, `hCST`, `hG`, `K`, `hK`, `hPK`, `hOppK`,
`_hKsplit`, `_hOppKsplit` and `A`, and in addition:

- conditional data of the canonical scalar for `A`, exactly as taken by
  `conditionalCanonicalRationalScalar`: continuations
  `p : ForwardContinuation … A` and `q : ReverseContinuation … A`, open
  nonempty sets `DForward ⊆ forwardFullDomainRegion χ K hK A` and
  `DReverse ⊆ reverseFullDomainRegion χ K hK A`, and an open nonempty set
  `D` on which the unramified induction of `A ⊗ z` is irreducible (`hi`);
- independent conditional data `p'`, `q'`, `DForward'`, `DReverse'`, `D'`,
  `hi'` of the same kind for `A.contragredient`;
- `_hinvForward : ∀ z ∈ DForward, z⁻¹ ∈ reverseFullDomainRegion χ K hK
  A.contragredient` and `_hinvReverse : ∀ z ∈ DReverse, z⁻¹ ∈
  forwardFullDomainRegion χ K hK A.contragredient`.

Its conclusion is the identity in the actual field of rational functions
on the parameter group:

```
conditionalCanonicalRationalScalar … A.contragredient p' q' … hi'
  = rationalUnramifiedFunctionFieldInversion (parameterScheme χ) …
      (conditionalCanonicalRationalScalar … A p q … hi).
```

The hypotheses `_hinvForward` and `_hinvReverse` make the convergence
domains of the two adjunction directions available on the open sets
`DForward` and `DReverse`, which is where the continuations `p` and `q` are
anchored.

The Borel `MeasurableSpace` and `BorelSpace` instances on `RationalPoint F
G.X` are local instances of this module. They are needed to form
`CompactInduction.measure`.

## The density corollary

`rationalUnramifiedFunctionFieldInversion_fieldConstant` says that the
inversion fixes the constants `fieldConstant i ζ hG c` of
`RationalPlancherelDensity`.

`plancherelDensity_contragredient_of_contragredientScalar` assumes the
scalar target `H`. For `χ = ζ ≫ i`, the hypotheses of the scalar target and
open sets `hDForward`, `hDReverse`, `hD`, `hDForward'`, `hDReverse'`,
`hD'`, it proves

```
plancherelDensity i ζ … A.contragredient p' q' … hi'
  = rationalUnramifiedFunctionFieldInversion (parameterScheme χ) …
      (plancherelDensity i ζ … A p q … hi).
```

The proof unfolds `plancherelDensity_def`
(`μ = fieldConstant (plancherelDensityConstant i ζ K hK) * j_P⁻¹`), rewrites
the scalar for `Ǎ` by `H`, and uses that the inversion is a ring
automorphism fixing the constant. The constant `plancherelDensityConstant`
(the square of the product of the `γ(M_α|M)`) does not depend on `A`. This is
the fourth item of Lemma V.2.1 in the Library's parametrization:
`μ(Ǎ ⊗ z⁻¹) = μ(A ⊗ z)`.

## Intended use

The scalar target is meant to be proved from the adjunction target. The
route has three steps.

1. Continue both directions of the adjunction from the open sets of the
   conditional data to the regular regions of the continuations, by
   rationality of the continued operators. This is the bilinear analogue of
   `continuedOperator_adjoint` in `DynamicOppositeUnitaryNonnegativity`.
2. Combine the two continued directions: for `z` regular for `A` with `z⁻¹`
   regular for `Ǎ`,
   `⟨J_{P|P̄}(A ⊗ z) J_{P̄|P}(A ⊗ z) φ, φ̌⟩_P =
   ⟨φ, J_{P|P̄}(Ǎ ⊗ z⁻¹) J_{P̄|P}(Ǎ ⊗ z⁻¹) φ̌⟩_P`.
3. On the irreducibility loci both composites are scalars. Pick `φ`, `φ̌`
   with `⟨φ, φ̌⟩_P ≠ 0`; then the two scalars agree on a nonempty open set,
   so the rational functions agree.

The density corollary is the fourth item of Lemma V.2.1. Waldspurger also
uses IV.3 (2) directly, together with IV.3 (4), in the proof of
Lemma V.2.2 (printed p.294 / PDF p.60) to compute the product `xy` of the
scalars for `sω` and `sω̌` as `∏ j_α(sω)`.

## Not proved here

The two targets. The continuation of the adjunction to the regular regions
of the continued operators. The nondegeneracy of the pairing. That
inversion maps the convergence domains for `A` into those for `Ǎ`.

## Axioms

The proved results use only `propext`, `Classical.choice` and `Quot.sound`.
The targets are `def … : Prop` and introduce no axioms.
