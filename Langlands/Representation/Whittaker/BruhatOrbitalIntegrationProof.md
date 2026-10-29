# Orbital integration onto test functions on an upper Bruhat cell: proof

Author: Worker 1011.

This module proves `Langlands.Whittaker.bruhatOrbitalIntegration.{uF}`, whose type is
exactly the published proposition
`Langlands.Whittaker.BruhatOrbitalIntegrationStatement.{uF}` of
`Langlands.Representation.Whittaker.BruhatOrbitalIntegrationStatement`. The statement
module and everything it imports are used unchanged. Besides the statement module, the
proof imports the published modules `Langlands.Group.GL.UpperBruhatCoordinatesProof`
(for `upperBruhatCoordinates`), `Langlands.Group.GL.UpperUnipotentFactorizationProof`
(for `upperUnipotentFactorization`) and `Langlands.Group.GL.CompactOpen` (for
`PadicField.canonicalGeneralLinearCompactOpen`). It adds no hypothesis, axiom or proof
hole. The only axioms are `propext`, `Classical.choice` and `Quot.sound`.

## What is proved

For every prime `p`, every p-adic field `F : PadicField.{uF} p` with
`F.canonicalNormedField`, every `n : ℕ` (including `n = 0`) and every permutation `w` of
`Fin (n + 1)`, write `U = upperUnipotent (n + 1) F.Carrier`,
`P = permutationUnipotentPlus (n + 1) F.Carrier w`, `H = Fin (n + 1) → F.Carrierˣ`,
`M = U × (H × U)`, `C = UpperBruhatCell (n + 1) F.Carrier w`, `π = upperBruhatTorusMap
(n + 1) w : M → C`, and `u • m = bruhatFiberAct (n + 1) F.Carrier w u m`. For every
measure `μ` on `P` (Borel σ-algebra) with `[Measure.IsHaarMeasure μ]` and
`[μ.IsMulRightInvariant]`, there is exactly one complex-linear map
`I : SchwartzBruhat M →ₗ[ℂ] SchwartzBruhat C` with

1. `I α (π m) = bruhatFiberAverage (n + 1) F.Carrier w μ α m` for all `α` and `m`;
2. `Function.Surjective I`;
3. `tsupport (I α) ⊆ π '' tsupport α` for every `α` (the image itself, no closure).

The p-adic theorem is a specialization of a generic theorem,
`existsUnique_bruhatOrbitalIntegration`, stated for every field `K` with a topology
making it a Hausdorff topological ring. It takes four inputs, all supplied by published
results in the p-adic case: the cell coordinates `eT` with their multiplication law, the
factorization `e` with its multiplication law, and a nonempty compact open subset `K₀`
of `P`.

## Coordinates (section `Coordinates`)

The published `upperBruhatCoordinates` gives a homeomorphism

    eT : U × H × U_w⁻ ≃ₜ C,   (eT (u₁, d, v)).val = u₁ * p_w * h(d) * v,

with `p_w = permutation (n + 1) F.Carrier w`, `h(d) = Iwasawa.diagonalUnits d` and
`U_w⁻ = permutationUnipotentMinus`. The published `upperUnipotentFactorization` gives a
homeomorphism

    e : P × U_w⁻ ≃ₜ U,   (e (u, v)).val = u * v.

The proof uses two maps built from them:

- `cellSection eT : C → M`, `c ↦ (u₁, d, v)` where `eT⁻¹ c = (u₁, d, v)` and `v` is
  viewed in `U` through `permutationUnipotentMinus_le_upperUnipotent`. It is continuous
  (`continuous_cellSection`).
- `plusCoordinate e : M → P`, `(u₁, d, u₂) ↦ (e⁻¹ u₂).1`, the `U_w⁺` factor of the last
  component. It is continuous (`continuous_plusCoordinate`).

Writing `s = cellSection eT` and `q = plusCoordinate e`, the following identities are
proved:

- `upperBruhatTorusMap_cellSection`: `π (s c) = c`, from the law of `eT` and
  `upperBruhatTorusMap_val`.
- `cellSection_upperBruhatTorusMap`: if the last component of `m` lies in `U_w⁻`, then
  `s (π m) = m`. Here `π m = eT x` for the obvious `x`, so `s (π m)` is `x` again.
- `plusCoordinate_bruhatFiberAct_cellSection`: `q (u • s c) = u`. The last component of
  `u • s c` is `u * v` (`bruhatFiberAct_snd_snd_val`), which is `e (u, v)`.
- `bruhatFiberAct_plusCoordinate_cellSection`: `q m • s (π m) = m` for every `m`. Write
  `e⁻¹ u₂ = (x₁, x₂)`, so `u₂ = x₁ * x₂`. Then `x₁⁻¹ • m` has last component `x₂ ∈ U_w⁻`
  and the same image under `π` (`upperBruhatTorusMap_bruhatFiberAct`), so
  `s (π m) = x₁⁻¹ • m` by the previous item, and `x₁ • (x₁⁻¹ • m) = m` by
  `bruhatFiberAct_bruhatFiberAct` and `bruhatFiberAct_one`.
- `continuous_bruhatFiberAct_cellSection`: `(c, u) ↦ u • s c` is continuous on `C × P`,
  from the published `continuous_bruhatFiberAct`.

No homeomorphism `C × P ≃ₜ M` is constructed; the section and the plus coordinate are
enough.

## The descended average (section `Average`)

For a measure `μ` on `P` with `IsFiniteMeasureOnCompacts μ`, define
`cellAverage μ eT α : C → ℂ` by `c ↦ bruhatFiberAverage … μ α (s c)`, the published raw
average read along the section.

- **Formula** (`cellAverage_upperBruhatTorusMap`, uses right invariance). For every `m`,
  `cellAverage μ eT α (π m) = bruhatFiberAverage … μ α m`. Rewrite `m` as
  `q m • s (π m)`; the published `bruhatFiberAverage_bruhatFiberAct` (invariance of the
  raw average under the action, from `μ.IsMulRightInvariant`) removes `q m`.
- **Support** (`support_cellAverage_subset`, `tsupport_cellAverage_subset`). If
  `cellAverage μ eT α c ≠ 0`, the published
  `exists_bruhatFiberAct_mem_tsupport_of_mem_support` gives `u` with
  `u • s c ∈ tsupport α`, and `π (u • s c) = π (s c) = c`. So the support lies in
  `π '' tsupport α`. This set is compact (continuous image of the compact `tsupport α`)
  and hence closed, since `C` is Hausdorff; so the topological support lies in it too.
- **Compact support** (`hasCompactSupport_cellAverage`): `tsupport` is a closed subset
  of the compact set `π '' tsupport α`.
- **Local constancy** (`isLocallyConstant_cellAverage`). Apply the auxiliary lemma
  `isLocallyConstant_integral_of_isCompact` (below) to `g (c, u) = α (u • s c)` on
  `C × P` with `T = q '' tsupport α`, which is compact. `g` is locally constant because
  `α` is and `(c, u) ↦ u • s c` is continuous. If `u ∉ T` then `g (c, u) = 0`, since
  otherwise `u = q (u • s c) ∈ q '' tsupport α`.
- **Linear map** (`cellOrbitalIntegral`). These facts bundle `cellAverage μ eT` into a
  complex-linear map `SchwartzBruhat M →ₗ[ℂ] SchwartzBruhat C`. Additivity and
  homogeneity follow pointwise from linearity of `bruhatFiberAverage`.

### Auxiliary lemmas (section `Tube`)

- `isLocallyConstant_integral_of_isCompact`: let `g : X × Y → ℂ` be locally constant and
  `g (x, y) = 0` whenever `y ∉ T`, with `T` compact. Then `x ↦ ∫ g (x, y) dν(y)` is
  locally constant, for any measure `ν`. Fix `x₀`. The set
  `{(x, y) | g (x, y) = g (x₀, y)}` is open and contains `{x₀} × T`. Mathlib's
  `generalized_tube_lemma` gives an open `V ∋ x₀` with `V × T` inside it. For `x ∈ V` the
  integrands at `x` and `x₀` agree at every `y`: on `T` by the tube, and off `T` both
  vanish.
- `isLocallyConstant_indicator_const`: the indicator of a clopen set with constant value
  is locally constant.

## The generic theorem (section `Main`)

`existsUnique_bruhatOrbitalIntegration eT heT e he hK₀c hK₀o hK₀` proves, for every
Borel measure `μ` on `P` with `[Measure.IsHaarMeasure μ] [μ.IsMulRightInvariant]`, the
exact `∃!` of the statement with `I = cellOrbitalIntegral μ heT he`. The Haar instance
supplies `IsFiniteMeasureOnCompacts μ` and `IsOpenPosMeasure μ`. Formula and support
are the results above.

**Surjectivity.** Let `f : SchwartzBruhat C`. The value `μ.real K₀` is nonzero, because
`K₀` is compact (finite measure) and open and nonempty (positive measure). Let `φ` be the
indicator of `K₀` with constant value `(μ.real K₀)⁻¹`, and set

    g m = f (π m) * φ (q m).

- `g` is locally constant: `f ∘ π` and `φ ∘ q` are, because `π` and `q` are continuous
  and `K₀` is clopen (compact in a Hausdorff space, hence closed, and open).
- `g` has compact support: its support lies in the image of the compact set
  `tsupport f × K₀` under the continuous map `(c, u) ↦ u • s c`. Indeed, if `g m ≠ 0` then
  `π m ∈ tsupport f`, `q m ∈ K₀`, and `m = q m • s (π m)`.
- For every `c`, `g (u • s c) = f c * φ u` (because `π (u • s c) = c` and
  `q (u • s c) = u`). Hence
  `cellAverage μ eT g c = f c * ∫ φ dμ = f c * (μ.real K₀ * (μ.real K₀)⁻¹) = f c`, by
  `integral_const_mul` and `integral_indicator_const`.

**Uniqueness.** If `J` satisfies the formula clause, then for every `α` and `c`,
`J α c = J α (π (s c)) = bruhatFiberAverage … μ α (s c) = cellAverage μ eT α c`. So
`J = cellOrbitalIntegral μ heT he` by `LinearMap.ext`. Only the formula clause is used
here.

## The p-adic theorem

`bruhatOrbitalIntegration` introduces `p`, `Fact p.Prime` and `F`, installs
`F.canonicalNormedField`, and introduces `n` and `w`. It then takes:

- `eT` and its law from `upperBruhatCoordinates F.Carrier (n + 1) w` (second
  component);
- `e` and its law from `upperUnipotentFactorization F.Carrier (n + 1) w`;
- a compact open subgroup `L` of `GeneralLinear (n + 1) F.Carrier` from
  `F.canonicalGeneralLinearCompactOpen (n + 1) Set.univ Filter.univ_mem`.

It sets `K₀ = Subtype.val ⁻¹' L ⊆ P`. `K₀` is compact because `P` is closed in the
general linear group (published `isClosed_permutationUnipotentPlus`), so the inclusion
is a closed embedding and preimages of compact sets are compact. It is open as a
continuous preimage of an open set, and it contains `1`. The generic theorem then
gives the statement for every `μ`.

## Hypotheses that are not needed

- No `SFinite`, normalization, countability or regularity assumption on `μ` is made.
  Left invariance is not used. Right invariance is used only through the published
  `bruhatFiberAverage_bruhatFiberAct`.
- The generic theorem needs no local compactness or nonarchimedean hypothesis on `K`.
  The only p-adic input is the existence of the compact open `K₀`.
- No Shalika distribution invariance, Whittaker multiplicity one, quotient
  construction or fiber transitivity is used.

## Provenance

The proposition is Shalika's Lemma 1.10 together with formula (1.11), J. A. Shalika,
*The multiplicity one theorem for GL_n*, Ann. of Math. (2) **100** (1974), 171–193,
printed p.176, registered as `shalika-1974-multiplicity-one`. The statement's Markdown
records the source comparison. The proof route follows the outline in the task context
(integration along `P` in the published coordinates, then a compact-open normalized
tensor for surjectivity). The section and plus-coordinate argument, the tube-lemma proof
of local constancy and the generic formulation are internal to this module. They are
not quotations of the source. This module was written by Worker 1011 alone and reuses
no draft by another author.
