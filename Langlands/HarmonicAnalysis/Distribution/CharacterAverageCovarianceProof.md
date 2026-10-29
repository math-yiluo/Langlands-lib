# Translation covariance of character-weighted product averaging: proof

This module proves
`Langlands.HarmonicAnalysis.SchwartzBruhat.characterAverageCovariance.{uG, uY}`,
whose type is exactly the published proposition
`Langlands.HarmonicAnalysis.SchwartzBruhat.CharacterAverageCovarianceStatement.{uG, uY}`
of `Langlands.HarmonicAnalysis.Distribution.CharacterAverageCovarianceStatement`.
The statement module, the published averaging map
`SchwartzBruhat.characterAverage` and the pullback
`Hecke.TestFunction.pullback` are imported unchanged. Besides the statement
module, the proof imports only the Mathlib modules
`Mathlib.MeasureTheory.Group.Measure` and
`Mathlib.MeasureTheory.Group.MeasurableEquiv`.

## What is proved

The proof introduces exactly the binders of the proposition: arbitrary
`G : Type uG` and `Y : Type uY` in independent universes, the instances
`[Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
[BorelSpace G] [TopologicalSpace Y]`, a continuous character
`χ : ContinuousMonoidHom G ℂˣ` (not necessarily unitary), a measure `μ` on `G`
with `[SFinite μ] [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
[μ.IsMulRightInvariant]`, elements `a b : G` and a test function
`α : SchwartzBruhat (G × (Y × G))`. It proves

    characterAverage χ μ
        (Hecke.TestFunction.pullback
          ((Homeomorph.mulLeft a).prodCongr
            ((Homeomorph.refl Y).prodCongr (Homeomorph.mulRight b))) α) =
      ((χ a : ℂ) * (χ b : ℂ)) • characterAverage χ μ α.

No further hypothesis is added anywhere in the proof.

## The implemented argument

1. **The substitution is measure preserving.** Let
   `e = MeasurableEquiv.prodCongr (MeasurableEquiv.mulLeft a)
   (MeasurableEquiv.mulRight b)`, the measurable equivalence
   `(g₁, g₂) ↦ (a * g₁, g₂ * b)` of `G × G`. Mathlib's
   `measurePreserving_mul_left μ a` (from `μ.IsMulLeftInvariant`) and
   `measurePreserving_mul_right μ b` (from `μ.IsMulRightInvariant`) say that
   left translation by `a` and right translation by `b` preserve `μ`.
   `MeasurePreserving.prod`, which needs `SFinite μ` for both source
   factors, combines them: `e` preserves `μ.prod μ`. Left invariance is used
   only on the first factor and right invariance only on the second; neither
   is derived from the other.

2. **Reduction to scalars.** By extensionality of test functions
   (`Hecke.TestFunction.ext`) it suffices to compare values at each `y : Y`.
   The evaluation laws `characterAverage_apply` and `pullback_apply` hold by
   definition, and the scalar multiplication of `SchwartzBruhat Y` is
   pointwise, so the goal is restated by `change` as

       ∫ z, α (a * z.1, (y, z.2 * b)) * ((χ z.1 : ℂ) * (χ z.2 : ℂ))⁻¹ ∂(μ.prod μ)
         = (χ a : ℂ) * (χ b : ℂ) *
             ∫ w, α (w.1, (y, w.2)) * ((χ w.1 : ℂ) * (χ w.2 : ℂ))⁻¹ ∂(μ.prod μ).

   Here `pullback e' α x = α (e' x)`, so the first argument of `α` on the
   left is `(a * z.1, (y, z.2 * b))`: forward composition with the displayed
   homeomorphism.

3. **Change of variables on the right.** Write
   `F w = α (w.1, (y, w.2)) * ((χ w.1 : ℂ) * (χ w.2 : ℂ))⁻¹`. Rewriting
   backwards with `MeasurePreserving.integral_comp'` for `e` replaces
   `∫ w, F w ∂(μ.prod μ)` by `∫ z, F (e z) ∂(μ.prod μ)`, and rewriting
   backwards with `integral_const_mul` moves the constant
   `(χ a : ℂ) * (χ b : ℂ)` inside the integral.

4. **Pointwise identity.** `integral_congr_ae` with an everywhere-true
   equality reduces the goal to, for every `z = (z.1, z.2)`,

       α (a * z.1, (y, z.2 * b)) * ((χ z.1 : ℂ) * (χ z.2 : ℂ))⁻¹
         = (χ a : ℂ) * (χ b : ℂ) *
             (α (a * z.1, (y, z.2 * b)) *
               ((χ (a * z.1) : ℂ) * (χ (z.2 * b) : ℂ))⁻¹).

   Multiplicativity of `χ` (`map_mul`) and of the coercion `ℂˣ → ℂ`
   (`Units.val_mul`) rewrite `χ (a * z.1)` as `χ a * χ z.1` and
   `χ (z.2 * b)` as `χ z.2 * χ b`. The four values `χ a`, `χ b`, `χ z.1`,
   `χ z.2` are nonzero because they are units (`Units.ne_zero`), and
   `field_simp` closes the resulting identity in the field `ℂ`.

## Signs

The weight is the inverse of the character values. At the translated point
`e z = (a * z.1, z.2 * b)` it is

    ((χ (a * z.1)) * (χ (z.2 * b)))⁻¹
      = (χ a)⁻¹ * (χ b)⁻¹ * ((χ z.1) * (χ z.2))⁻¹.

Hence the original weight satisfies
`((χ z.1) * (χ z.2))⁻¹ = χ a * χ b * ((χ (a * z.1)) * (χ (z.2 * b)))⁻¹`:
multiplying by `χ a * χ b` exactly cancels the two inverted factors produced by
translating. The factor that comes out of the integral is therefore the plain
product `χ a * χ b`, with neither factor inverted, and it multiplies on the
left, matching the scalar `((χ a : ℂ) * (χ b : ℂ)) •` of the statement. Only
commutativity of `ℂ` is used to rearrange the scalars; `G` itself is not
assumed commutative, and the translations stay on their original sides
(`a` on the left of `z.1`, `b` on the right of `z.2`).

## Why the substitution needs no extra topology or countability

- **Measurability of translations.** `measurePreserving_mul_left`,
  `measurePreserving_mul_right`, `MeasurableEquiv.mulLeft` and
  `MeasurableEquiv.mulRight` need only `MeasurableMul G`, i.e. that each
  single translation `g ↦ c * g` and `g ↦ g * c` is measurable. Mathlib's
  instance `ContinuousMul.measurableMul` supplies it from the separate
  continuity of multiplication (a consequence of `IsTopologicalGroup G`) and
  `OpensMeasurableSpace G` (a consequence of `BorelSpace G`). Joint
  measurability of multiplication `G × G → G` (`MeasurableMul₂`), which would
  require second countability, is never used.
- **Product σ-algebra.** The integral defining `characterAverage` is taken
  over `μ.prod μ` on the product σ-algebra of `G × G`, and `e` is a
  measurable equivalence for that product σ-algebra because it is a product
  of measurable equivalences (`MeasurableEquiv.prodCongr`). The proof never
  compares the product σ-algebra with the Borel σ-algebra of `G × G`, which
  is where countability would be needed.
- **Product of measure-preserving maps.** `MeasurePreserving.prod` needs only
  `SFinite μ`, which is a hypothesis of the statement (and is also needed for
  `characterAverage` itself to be defined).
- **No integrability side conditions.** `MeasurePreserving.integral_comp'`
  transports the Bochner integral of an arbitrary function along a
  measure-preserving measurable equivalence, and `integral_const_mul` holds
  for every complex-valued function. Neither requires integrability, so the
  proof needs no integrability argument (the published lemma
  `integrable_characterAverage_slice` is not used).

No Haar measure, local compactness, Hausdorff property, nonarchimedean or
totally disconnected structure, commutativity of `G`, unitarity or local
constancy of `χ`, open character kernel, countability, σ-compactness or
nonemptiness is assumed or used. `IsFiniteMeasureOnCompacts μ` is used only
through the definition of `characterAverage`. No distribution theorem,
surjectivity or factorization of the averaging map, or multiplicity-one result
is used. The only axioms are `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

The covariance identity is internal derived content, as explained in the
statement's Markdown: the elementary change of variables underlying Shalika's
average `β_α` in Proposition 1.12 (printed p. 177) of J. A. Shalika, *The
multiplicity one theorem for GL_n*, Ann. of Math. (2) **100** (1974), 171–193,
registered as `shalika-1974-multiplicity-one`. Shalika does not state or
prove this transformation law; the proof above is an internal argument and
follows the substitution outlined in the statement's Markdown, carried out by
transporting the right-hand integral along `(g₁, g₂) ↦ (a * g₁, g₂ * b)`.
