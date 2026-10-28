# Scaling a compatible quotient measure by a group automorphism

Author: Worker 787.

`Langlands.QuotientIntegration.CompatibleQuotientAutomorphismScaling` is a
proposition stating how a continuous automorphism of `G` that preserves a
closed subgroup `H` rescales every compatible measure on the existing left
quotient `LeftQuotient H`. This module states the proposition; it does not
prove it. The proof is a separate later task.

## Elementary packaging

The module adds two constructions and four representative formulas. They
need only a group with a topology, and use no measure theory.

- `subgroupAutomorphism H α hα : H ≃ₜ* H` is the restriction of
  `α : G ≃ₜ* G` to `H`. The hypothesis `hα : ∀ x, α x ∈ H ↔ x ∈ H` says
  that `α` maps `H` onto itself. Its forward map is `h ↦ α h` and its inverse
  is `h ↦ α.symm h`. Continuity in both directions comes from the subspace
  topology. The formulas `subgroupAutomorphism_apply` and
  `subgroupAutomorphism_symm_apply` (both `rfl`) say that the value in `G`
  of the image of `h` is `α h`, and of the inverse image is `α.symm h`.
- `quotientAutomorphism H α hα : LeftQuotient H ≃ₜ LeftQuotient H` is the
  homeomorphism induced on the actual published quotient
  `LeftQuotient H = Quotient (QuotientGroup.rightRel H)`, whose points are
  the cosets `H * g`. It is `Homeomorph.Quotient.congr` applied to the
  underlying homeomorphism of `α`. It respects the relation because
  `α y * (α x)⁻¹ = α (y * x⁻¹)`. The formulas `quotientAutomorphism_mk`
  and `quotientAutomorphism_symm_mk` (both `rfl`) say that `[g] ↦ [α g]`
  and, for the inverse, `[g] ↦ [α.symm g]`.

No new quotient type, model quotient or measure-law predicate is introduced.

## Hypotheses of the proposition

The proposition quantifies over all of the following:

- a group `G : Type uG` in an arbitrary universe that is a Hausdorff, locally
  compact topological group with a Borel measurable structure;
- a subgroup `H` with `IsClosed (H : Set G)`, with a Borel measurable
  structure on `H` for its subspace topology;
- a Borel measurable structure on `LeftQuotient H` for its existing quotient
  topology;
- arbitrary supplied measures `μG` on `G` and `μH` on `H`, each with
  `IsHaarMeasure`, `Regular` and `IsMulRightInvariant`. So both are regular
  two-sided Haar measures. Neither is normalized or chosen by the statement.
- every measure `ν : Measure (LeftQuotient H)` with the unchanged
  `IsCompatible H μG μH ν`. Compatibility is a hypothesis on `ν`, not a
  construction. It already provides that `ν` is nonzero and regular (hence
  finite on compacts), invariant under right translation, and satisfies the
  Weil integral formula
  `∫ q, quotientAverage H μH f q ∂ν = ∫ g, f g ∂μG` for continuous
  compactly supported `f : G → ℂ`.
- every `α : G ≃ₜ* G` and every `hα : ∀ x : G, α x ∈ H ↔ x ∈ H`.

Local compactness of `H` is not a hypothesis. Inside the proposition it is
obtained from closedness, as `hH.locallyCompactSpace`. This is needed for the
Haar modulus of the restriction to be defined. There is no second
countability, σ-compactness, compact-open basis or nonarchimedean hypothesis.
There is also no hypothesis about the quotient beyond its Borel structure.

## Conclusion

Inside the proposition the following local names are used:

- `αH = subgroupAutomorphism H α hα` and
  `αQ = quotientAutomorphism H α hα`;
- `δG = mulEquivHaarChar α` and `δH = mulEquivHaarChar αH`. These are
  Mathlib's actual Haar moduli of the given automorphisms, as values in
  `ℝ≥0`. Mathlib proves they are positive (`mulEquivHaarChar_pos`) and
  satisfy `mulEquivHaarChar φ • μ.map φ = μ` for every regular Haar measure
  `μ` (`mulEquivHaarChar_smul_map`). Equivalently,
  `∫ f(φ⁻¹ x) dμ(x) = δ · ∫ f dμ`.

The conclusion is the conjunction of two statements.

1. **Pushforward.** The literal equality of measures

   ```text
   Measure.map αQ ν = (((δH / δG : ℝ≥0) : ℝ≥0∞)) • ν.
   ```

2. **Inverse-integrand form.** For every function
   `f : LeftQuotient H → ℂ`,

   ```text
   (∫ q, f (αQ.symm q) ∂ν) = (((δG / δH : ℝ≥0) : ℝ) : ℂ) * ∫ q, f q ∂ν.
   ```

   This uses Mathlib's total Bochner integral. There is no measurability,
   integrability or continuity hypothesis on `f`. Given the first statement,
   the pushforward of `ν` by `αQ.symm` is a positive finite multiple of `ν`.
   So `f ∘ αQ.symm` is integrable exactly when `f` is. When `f` is not
   integrable both sides are zero, so no premise is needed.

The two factors are reciprocal. The second statement says that `ν` pushed
forward by `αQ.symm` is `(δG / δH) • ν`, and this follows from the first by
applying `Measure.map αQ.symm` to both sides.

## Why the factor is δH / δG

Let `f : G → ℂ` be continuous with compact support. Substituting
`h = αH h'` in the subgroup integral gives, for the coset `H * g`,

```text
∫_H f(h * α g) dμH(h) = δH · ∫_H f(α (h' * g)) dμH(h').
```

This uses `map αH μH = δH⁻¹ • μH`. Thus the quotient average of `f`, read
through `αQ`, equals `δH` times the average of `f ∘ α`. Integrating against
`ν` and using the Weil formula for `f ∘ α`, together with
`map α μG = δG⁻¹ • μG`, gives

```text
∫ (average of f) d(map αQ ν) = (δH / δG) · ∫_G f dμG.
```

So `map αQ ν` satisfies the Weil formula of the measure `(δH / δG) • ν`.
To conclude that the two measures are equal requires a uniqueness argument
for compatible measures. The proof successor must derive that internally,
for example from the existing positive lifting
(`Langlands.Analysis.Local.QuotientPositiveLifting`) and from the
compact-test measure extensionality in
`Langlands.Analysis.Local.QuotientFunctional`. This paragraph explains the
sign. The proposition does not assume this argument, quotient-measure
uniqueness, the map law or either integral identity.

## Provenance

This general law is an internal analytic prerequisite, formalized for the
project's quotient conventions. It is not a verbatim theorem of the
original source.

The original source is I. N. Bernstein and A. V. Zelevinsky, *Induced
representations of reductive p-adic groups. I*, Ann. Sci. École Norm. Sup.
(4) 10 (1977), 441–472. It is registered as `bernstein-zelevinsky-1977-induced-i`,
SHA256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Sections 1.7 and 5.17, including the continuation on printed page 467, were
read in full.

- **Section 1.7** (printed pp. 443–444). Here `U` is a unimodular l-group
  with Haar measure and `σ` is an automorphism. The modulus `mod_U σ` is
  defined by `∫ f(σ⁻¹ u) dμ(u) = mod_U(σ) ∫ f(u) dμ(u)`, which is the same
  convention as `mulEquivHaarChar`. The section then makes a short remark,
  not a numbered theorem. Let `U'` be a closed subgroup of `U` with
  `Δ_U = 1` and `Δ_{U'} = 1`, so both are unimodular. Then there is an
  invariant measure on `U'\U`. For an automorphism `σ` of `U` with
  `σ(U') = U'` one can define `mod_{U'\U} σ`, and "The Fubini theorem
  implies that `mod_{U'\U} = mod_U / mod_{U'}`." With `U = G`, `U' = H` and
  `σ = α`, this is the factor `δG / δH` in the inverse-integrand statement
  above. The source gives no further proof.
- **Section 5.17** (printed pp. 466–467) is Case IV of the proof of
  Theorem 5.2, where `X = V' \ V` with `V' = V ∩ M`. The authors choose a
  Haar measure on `V' \ V` "(see 1.7)" and define a map `A` by integrating
  over `V' \ V`. To prove that `A` is equivariant for `n ∈ N`, they make the
  conjugation change of variables `v = n⁻¹ ṽ n` in this integral. By 1.7
  this produces the factor `mod_{V'\V}(n)`. The continuation on p. 467
  proves that `A` is an isomorphism. It first treats the regular
  representation, using uniqueness of Haar measure on `V` and `V'`, and
  then uses free resolutions. It does not use the quotient modulus again.

The formalization differs from the source in the following ways.

- The source works with l-groups. Here `G` is any Hausdorff locally compact
  group and `H` any closed subgroup.
- The source's "invariant measure on `U'\U`" is replaced by every measure `ν`
  with the existing `IsCompatible` condition for the supplied Haar measures.
  So the quotient measure is not chosen by the statement.
- Unimodularity is expressed by requiring both supplied Haar measures to be
  right invariant as well. This is the same setting in which the published
  `compatibleMeasureExists` theorem
  (`Langlands.Analysis.Local.QuotientMeasureExistence`) shows that such `ν`
  exist, so the hypotheses are not vacuous.
- The source's single equation of moduli is expressed here as a literal
  equality of measures, together with its inverse-integrand form for
  arbitrary complex integrands.
- The source's cosets `U' u` match the project's `LeftQuotient H` of cosets
  `H * g`.

The planned use is the conjugation change of variables in the parabolic
orbit comparison (`Langlands.Geometric.PadicParabolicOrbitJacquetComparison`,
Worker 76). There, `α` is conjugation on the unipotent radical and `H` its
intersection with the orbit stabilizer. The formal determinant normalization
and the algebraic-integral equivariance belong to that later work, not to
this statement.
