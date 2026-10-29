# Automorphism covariance of the compact coinvariant integral

Author: Worker 787.

`Langlands.Induction.CompactAutomorphismIntegralCovariance.{uG,uV}` is a
proposition, written as a `Prop`-valued `def`. It says how the published
quotient integral on compact induction changes when the induced functions are
precomposed with a continuous automorphism `α` of `G` that preserves the
inducing subgroup `H`. This module states the proposition; it does not prove
it. The proof is a separate later task coordinated by Worker 76. The module
adds no other declarations.

## Published objects used

All objects in the statement are existing Library or Mathlib declarations.

- `CompactFunctions H σ`, the actual compactly induced functions: covariant
  functions `f(h * g) = σ h (f g)` with an open right stabilizer and compact
  projected nonzero support in `LeftQuotient H`.
- `compactCoinvariantIntegral H σ ν`, from
  `Langlands.Representation.Induction.CompactCoinvariantIntegral`. It is the
  complex linear map

  ```text
  f ↦ ∫_{LeftQuotient H} [f(g)] dν(H * g)  ∈  Representation.Coinvariants σ,
  ```

  defined as the finite-fiber `AlgebraicIntegral.integral` of the descended
  simple function `H * g ↦ Coinvariants.mk σ (f g)`. It is a finite sum of
  values weighted by the real measures of their fibers. It is not a Bochner
  integral, and the coefficient space has no topology.
- `automorphismInducing H α hα σ = σ.comp (subgroupAutomorphism H α hα)`,
  from `Langlands.Representation.Induction.CompactAutomorphism`. It is the
  representation `h ↦ σ(α h)` on the same module `V`.
- `automorphismInducingMap H α hα T`, the same linear map as an intertwiner
  `T : σ.IntertwiningMap τ`, viewed as an intertwiner between the pulled-back
  representations.
- `precomposeCompactInducedEquiv H α hα σ`, from the same module. It sends
  `f : CompactFunctions H σ` to the compact function `x ↦ f(α x)` in
  `CompactFunctions H (automorphismInducing H α hα σ)`.
- `QuotientIntegration.subgroupAutomorphism H α hα : H ≃ₜ* H`, the restriction
  of `α` to `H`, from `Langlands.Analysis.Local.QuotientAutomorphismStatement`.
- Mathlib's `Representation.Coinvariants`, `Coinvariants.mk`,
  `Coinvariants.map` and `MeasureTheory.mulEquivHaarChar`.

No other induced-function space, quotient, integral or coinvariant type is
used.

## Hypotheses of the proposition

The proposition quantifies over all of the following:

- a group `G : Type uG` that is a Hausdorff, locally compact topological group
  with a Borel measurable structure;
- a subgroup `H` with `hH : IsClosed (H : Set G)`, with a Borel measurable
  structure for its subspace topology;
- arbitrary supplied measures `μG` on `G` and `μH` on `H`, each with
  `IsHaarMeasure`, `Regular` and `IsMulRightInvariant`. So both are regular
  two-sided Haar measures, and neither is chosen by the statement;
- a Borel measurable structure on the actual quotient
  `QuotientIntegration.LeftQuotient H`, whose points are the cosets `H * g`;
- every measure `ν` on `LeftQuotient H` with the unchanged
  `hν : QuotientIntegration.IsCompatible H μG μH ν`;
- every `α : G ≃ₜ* G` and every `hα : ∀ x : G, α x ∈ H ↔ x ∈ H`.

These binders are the same as in the published
`QuotientIntegration.CompatibleQuotientAutomorphismScaling`. The only
difference is that the compatibility hypothesis is named `hν` here, because it
is used.

Two instances are installed inside the proposition and are not hypotheses:

- `LocallyCompactSpace H`, from `hH.locallyCompactSpace`. It is needed for the
  Haar modulus of the restriction of `α` to `H` to be defined.
- `IsFiniteMeasureOnCompacts ν`, from `hν.regular.toIsFiniteMeasureOnCompacts`.
  It is needed by `compactCoinvariantIntegral`.

There is no compact-open basis, second countability, σ-compactness,
nonarchimedean or normality hypothesis.

## Conclusion

Inside the proposition the following local names are used:

- `δG = mulEquivHaarChar α`, the Haar modulus of `α` on `G`;
- `δH = mulEquivHaarChar (subgroupAutomorphism H α hα)`, the Haar modulus of
  the restriction of `α` to `H`;
- `c = (((δH / δG : ℝ≥0) : ℝ) : ℂ)`, the quotient `δH / δG` in `ℝ≥0` sent to
  `ℂ` through `ℝ`.

Mathlib's convention is `mulEquivHaarChar φ • μ.map φ = μ` for a regular Haar
measure `μ`, so `∫ f(φ⁻¹ x) dμ(x) = mulEquivHaarChar φ · ∫ f dμ`.

The conclusion asserts that there exists a family

```text
A σ : Representation.Coinvariants (automorphismInducing H α hα σ)
        ≃ₗ[ℂ] Representation.Coinvariants σ,
```

one complex linear equivalence for every module `V : Type uV` with
`AddCommGroup V` and `Module ℂ V`, and every representation
`σ : Representation ℂ H V`. The module `V` carries no topology, and there is
no assumption on its dimension, no smoothness assumption on `σ`, and no
admissibility, finite length, completeness or separability. The family
satisfies three conditions.

1. **Representative formula.** For every `σ` and every `v : V`,

   ```text
   A σ (Coinvariants.mk (automorphismInducing H α hα σ) v) = Coinvariants.mk σ v.
   ```

2. **Naturality.** For all `V W : Type uV`, all representations `σ` on `V`
   and `τ` on `W`, every intertwiner `T : σ.IntertwiningMap τ` and every
   coinvariant `z` of `automorphismInducing H α hα σ`,

   ```text
   A τ (Coinvariants.map (automorphismInducing H α hα σ)
          (automorphismInducing H α hα τ) (automorphismInducingMap H α hα T) z)
     = Coinvariants.map σ τ T (A σ z).
   ```

3. **Integral identity.** For every `σ` and every
   `f : CompactFunctions H σ`,

   ```text
   A σ (compactCoinvariantIntegral H (automorphismInducing H α hα σ) ν
          (precomposeCompactInducedEquiv H α hα σ f))
     = c • compactCoinvariantIntegral H σ ν f.
   ```

The group universe `uG` and the coefficient universe `uV` are independent.
Naturality is stated for any two coefficient modules in the same universe
`uV`. The integral identity uses the actual finite-fiber integral for every
coefficient module, not only for complex-valued functions.

## The family `A` is determined by the representative formula

`Coinvariants.mk` is surjective (`Coinvariants.mk_surjective`). So the first
condition determines each `A σ` uniquely: it is the map that sends the class
of a vector to the class of the same vector. The existential therefore does not
allow any other choice of transport. The second and third conditions are
claims about this canonical map.

The second condition follows from the first. Both sides send the class of
`v` to `Coinvariants.mk τ (T v)`, because `Coinvariants.map` sends the class of
`v` to the class of `T v`, and `automorphismInducingMap H α hα T` has the same
underlying linear map as `T`. It is stated separately because the downstream
use needs it in this form.

The following is guidance for the proof, not a premise. A family with the
first property exists. `Coinvariants.ker ρ` is the span of the vectors
`ρ h v - v`. As `h` runs over `H`, the elements `subgroupAutomorphism H α hα h`
also run over all of `H`, since the restriction is bijective. So
`Coinvariants.ker (automorphismInducing H α hα σ) = Coinvariants.ker σ`, and
`Submodule.quotEquivOfEq` gives a linear equivalence of the quotients that is
the identity on representatives.

The Library has two existing coinvariant transports,
`Jacquet.coinvariantsMapEquiv` in
`Langlands.Representation.CuspidalSupport.GroupTransport` and
`Jacquet.coinvariantsGroupTransportEquiv` in
`Langlands.Representation.Jacquet.CanonicalLiftGroupTransportProof`. Both are
stated for `Jacquet.Coinvariants ρ N`. The module
`Langlands.Representation.Jacquet.Coinvariants` defines this as an
abbreviation for Mathlib's `Representation.Coinvariants (ρ.comp N.subtype)`,
and its `mk` is Mathlib's `Coinvariants.mk`. So both transports already use
Mathlib's quotient, which is also the quotient used by
`compactCoinvariantIntegral`, but for a representation restricted to a
subgroup `N`. For example, with `f : H →* H` the restriction of `α`,
`Jacquet.coinvariantsMapEquiv σ f ⊤` is a linear equivalence from
`Representation.Coinvariants ((σ.comp f).comp (⊤ : Subgroup H).subtype)` to
`Representation.Coinvariants (σ.comp (Subgroup.map f ⊤).subtype)`, equal to the
identity on representatives.

The carriers in this statement are the full-group coinvariants
`Representation.Coinvariants (automorphismInducing H α hα σ)` and
`Representation.Coinvariants σ`, with no restriction to `⊤`. To use the
existing transports here one also needs `Subgroup.map f ⊤ = ⊤` and an
identification of the coinvariants of each full representation with the
coinvariants of its restriction to `⊤`. These identifications hold, because
the two relation spans are equal, but they must be supplied. A search of the
Library found the kernel equality only as a private lemma
(`coinvariantKer_top` in
`Langlands.Representation.Whittaker.CompactLocalizationProof`). The statement
does not need any transport. It asserts that a family with the representative
formula exists, and that formula determines the family uniquely. So the module
adds no new transport definition. A proof may use the equal-kernel argument
above, or the existing transports together with these identifications.

## Why the factor is δH / δG

The statement precomposes forward: `E f` is `x ↦ f(α x)`. Write `F_f` for the
descended function `H * g ↦ Coinvariants.mk σ (f g)` on `LeftQuotient H`, and
`αQ = quotientAutomorphism H α hα` for the published homeomorphism
`H * g ↦ H * α g`. By the representative formula,

```text
A σ (F_{E f}(H * x)) = Coinvariants.mk σ (f(α x)) = F_f(αQ (H * x)).
```

So `A σ ∘ F_{E f} = F_f ∘ αQ`. The linear map `A σ` commutes with the
finite-fiber integral, and integrating `F_f ∘ αQ` against `ν` is the same as
integrating `F_f` against `Measure.map αQ ν`. The published theorem
`QuotientIntegration.compatibleQuotientAutomorphismScaling`
(`Langlands.Analysis.Local.QuotientAutomorphismProof`) gives

```text
Measure.map αQ ν = (δH / δG) • ν.
```

Scaling a measure by a finite constant scales every fiber measure, and so the
finite-fiber integral, by the same constant. This gives the factor `δH / δG`.

The published theorem also has an inverse-integrand form with the reciprocal
factor `δG / δH`, for integrands `q ↦ f(αQ.symm q)`. That form describes
precomposition with `α⁻¹`. It does not apply here, because the statement
precomposes with `α` itself.

This paragraph only explains the sign. The proposition does not assume the
quotient pushforward law, the scaling of the finite-fiber integral, or any
other part of this argument.

## Provenance

The proposition is an internal consequence of the quotient pushforward law and
the definition of the finite-fiber integral. It is not a verbatim theorem of
the original source.

The original source is I. N. Bernstein and A. V. Zelevinsky, *Induced
representations of reductive p-adic groups. I*, Ann. Sci. École Norm. Sup.
(4) 10 (1977), 441–472. It is registered as
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`. Sections
1.7 and 5.17 were read, including the continuation on printed page 467. A
search of the Library notes found no errata note for this source.

- **Section 1.7** (printed pp. 443–444) defines the modulus by
  `∫ f(σ⁻¹ u) dμ(u) = mod_U(σ) ∫ f(u) dμ(u)`. This is the same convention as
  `mulEquivHaarChar`. It remarks, without a numbered theorem, that for
  unimodular `U' ⊂ U` and an automorphism `σ` with `σ(U') = U'`, "the Fubini
  theorem implies that `mod_{U'\U} = mod_U / mod_{U'}`". The published
  quotient pushforward law formalizes this remark.
- **Section 5.17** (printed pp. 466–467) is Case IV₂ of the proof of
  Theorem 5.2 (`U = {e}`, `G = Q`, `N ⊂ M`). There `X = V' \ V` with
  `V' = V ∩ M`, and the map `A` is defined by
  `A f = ∫_{V'\V} ψ⁻¹(v) p(f(v)) dμ(v)`, where `p : L → L⁺` is the projection
  onto coinvariants. To prove that `A` commutes with `n ∈ N`, the source
  writes `A(π(n) f)` as `mod_V^{-1/2}(n)` times
  `∫_{V'\V} ψ⁻¹(v) p(f(v n)) dμ(v)`. It changes variables and, by 1.7,
  obtains `mod_{V'\V}(n) · ∫_{V'\V} ψ⁻¹(ṽ) p(f(n ṽ)) dμ(ṽ)`. It then
  rewrites `p(f(n ṽ))` using the covariance of `f`. The continuation on
  p. 467 proves that `A` is an isomorphism, using the regular representation
  and free resolutions. That part is not related to this statement.

The scan's sentence that introduces the change of variables reads "Use in this
integral the replacement v = n⁻¹ vn; according to 1.7 it equals". It does not
mark which `v` is the old variable and which is the new one. The display that
follows fixes the assignment, and the following is our interpretation of that
display, not a quotation. The display turns `f(v n)` into `f(n ṽ)`, so the
new variable is `ṽ = n⁻¹ v n`, equivalently `v = n ṽ n⁻¹`. Section 1.7
defines `mod_U(g)` as the modulus of the automorphism `u ↦ g u g⁻¹`. With
this convention, for a function `F` on `V' \ V`, writing the old variable as
`n ṽ n⁻¹` gives
`∫ F(v) dμ(v) = mod_{V'\V}(n) · ∫ F(n ṽ n⁻¹) dμ(ṽ)`. Since
`f(n ṽ n⁻¹ n) = f(n ṽ)`, this is the change of variables in the display, with
the factor `mod_{V'\V}(n)` shown there.

In the conjugation step of Case IV₂, the automorphism is conjugation
`ṽ ↦ n ṽ n⁻¹` on `V`, which preserves `V'`, and the integral takes values in
coinvariants of an arbitrary representation. This proposition supplies the
generic form of that substitution. For any automorphism `α` preserving `H`, it
relates the integral of the forward precomposition `x ↦ f(α x)` to the
original integral, with values in the coinvariants of an arbitrary coefficient
representation. It also records the naturality of the identification of
coinvariants in the coefficient. For `α` the conjugation by `n`, the factor
`δH / δG` is `mod_{V'}(n) / mod_V(n)`, which is the reciprocal of
`mod_{V'\V}(n)` by the remark in 1.7. This matches the source display, read
as an identity for the integral in the new variable `ṽ`. Both the
arbitrary-coefficient identity and the explicit naturality are internal
additions. The source performs the substitution in one line.

The formalization differs from the source as follows.

- The source works with l-groups. Here `G` is any Hausdorff locally compact
  group and `H` any closed subgroup.
- The source's Haar measure on `V' \ V` is replaced by every measure `ν`
  satisfying the existing `IsCompatible` condition for the supplied two-sided
  Haar measures. The published `compatibleMeasureExists`
  (`Langlands.Analysis.Local.QuotientMeasureExistence`) shows that such
  measures exist in this setting, so the hypotheses are not vacuous.
- The source has a character `ψ` and the action of `n` on the coefficients.
  This proposition has neither. The coefficient transport here is the
  identity on vectors. The action of `n` on the coefficients, the character
  twist, the determinant normalization, and the full relative
  normalizer-equivariant orbit comparison belong to later work, in particular
  `Langlands.Geometric.PadicParabolicOrbitJacquetComparison` (Worker 76).

## Scope

This module states one proposition and proves nothing. It does not assert
bijectivity of the integral, the existence or uniqueness of compatible
measures, or any equivariance under the ambient group. The proposition does
not assume the covariance, the measure scaling, a uniqueness or kernel
statement, surjectivity, a compact-open lift, or a comparison with a parent
construction. No smoothness hypothesis is needed: every element of
`CompactFunctions H σ` already has its own open right stabilizer.
