# Twisted orbital integrals of product functions

`Langlands.TraceFormula.ProductTwistedOrbitalStatement` defines two propositions in
namespace `Langlands.TraceFormula`.

## Common setting

Each group is a Hausdorff, locally compact, second-countable topological group with its
Borel σ-algebra. Each quotient has the Borel σ-algebra of its quotient topology.
The factor group measures are left Haar measures. Each measure on a centralizer is
right invariant, finite on compact sets, and positive on nonempty open sets.

The statements use `twistedCentralizer`, `twistedOrbitFunction`, and
`twistedOrbitalIntegral` from `Langlands.TraceFormula.TwistedOrbital`. For a twist `θ`
and an element `δ` of `G`, the subgroup `C = twistedCentralizer θ δ` consists of
the elements `x` with `x⁻¹ δ θ(x) = δ`. The Library's `LeftQuotient C` is `C \ G`,
with classes `C x` under multiplication by `C` on the left. The orbit function
of `f` sends `C x` to `f (x⁻¹ δ θ(x))`, and `twistedOrbitalIntegral θ δ ν f` is
its Bochner integral against `ν`.

`QuotientIntegration.IsCompatible C μG μC ν` requires `ν` to be nonzero,
regular, and invariant under right translations by `G`. For every continuous
compactly supported `g : G → ℂ`, the function `C x ↦ ∫_C g(c x) dμC(c)` must be
`ν`-integrable, with integral equal to `∫_G g dμG`.

## Two factors

`ProdTwistedOrbitalIntegralStatement.{u}` takes groups `G₁, G₂ : Type u` with
left Haar measures `μ₁, μ₂`. The monoid endomorphisms `θ₁` and `θ₂` are
continuous, and the monoid endomorphism `θ` on the product satisfies
`θ x = (θ₁ x.1, θ₂ x.2)` for every `x`.

For elements `δ₁ : G₁` and `δ₂ : G₂`, write `C₁ = twistedCentralizer θ₁ δ₁`,
`C₂ = twistedCentralizer θ₂ δ₂`, and `C = twistedCentralizer θ (δ₁, δ₂)`.
Take measures `μC₁`, `μC₂`, and `μC` on the respective centralizers and
measures `ν₁`, `ν₂`, and `ν` on their Borel left quotients. The measure
hypotheses are

- `IsCompatible C₁ μ₁ μC₁ ν₁` and `IsCompatible C₂ μ₂ μC₂ ν₂`
- `IsCompatible C (μ₁.prod μ₂) μC ν`
- `μC.map Subtype.val = (μC₁.map Subtype.val).prod (μC₂.map Subtype.val)` on `G₁ × G₂`

Take continuous `f₁ : G₁ → ℂ` and `f₂ : G₂ → ℂ` whose orbit functions
`twistedOrbitFunction θ₁ δ₁ f₁` and `twistedOrbitFunction θ₂ δ₂ f₂` are
integrable against `ν₁` and `ν₂`, respectively. Set `f x = f₁ x.1 * f₂ x.2`.
The statement asserts that `twistedOrbitFunction θ (δ₁, δ₂) f` is
`ν`-integrable and that

```text
twistedOrbitalIntegral θ (δ₁, δ₂) ν f =
  twistedOrbitalIntegral θ₁ δ₁ ν₁ f₁ * twistedOrbitalIntegral θ₂ δ₂ ν₂ f₂
```

## Finite family

`PiTwistedOrbitalIntegralStatement.{u, w}` takes a type `ι : Type w` with
`Fintype ι` and a family of groups `G i : Type u` with left Haar measures
`μ i`. The monoid endomorphisms `θ' i` are continuous, and the monoid
endomorphism `θ` on `Π i, G i` satisfies `θ x i = θ' i (x i)` for all `x` and `i`.

For `δ : Π i, G i`, write `C i = twistedCentralizer (θ' i) (δ i)` and
`C = twistedCentralizer θ δ`. Take measures `μC' i` and `μC` on these
centralizers and measures `ν' i` and `ν` on the respective Borel left
quotients. The measure hypotheses are

- `IsCompatible (C i) (μ i) (μC' i) (ν' i)` for every `i`
- `IsCompatible C (Measure.pi μ) μC ν`
- `μC.map Subtype.val = Measure.pi (fun i => (μC' i).map Subtype.val)` on `Π i, G i`

Take continuous `f i : G i → ℂ` such that each
`twistedOrbitFunction (θ' i) (δ i) (f i)` is `ν' i`-integrable.
Set `φ x = ∏ i, f i (x i)`. The statement asserts that
`twistedOrbitFunction θ δ φ` is `ν`-integrable and that

```text
twistedOrbitalIntegral θ δ ν φ =
  ∏ i, twistedOrbitalIntegral (θ' i) (δ i) (ν' i) (f i)
```

The finite statement includes empty `ι`, where the right-hand side is the
empty product `1`.

## Source and scope

These propositions are derived from Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), §17.8, Lemma 17.8.3 and step (17.55) of its proof
(printed pp. 463–464). That step splits off finitely many places from a
relative orbital integral using product Haar measures on the acting group
and stabilizer and the Fubini–Tonelli theorem. Equation (18.32) in §18.5
(printed p. 487) gives the twisted-conjugation integrand and its stabilizer
quotient. [Getz–Hahn (2024)](https://doi.org/10.1007/978-3-031-41153-3)

The Lean statements isolate the finite product identity at a single element
in arbitrary groups in the common setting. The left quotients `C \ G` use
the same subgroup-on-the-left convention as the relative orbital integral.
Equation (18.32) uses adelic groups modulo split central subgroups. The Lean
statements use the centralizers of elements in the supplied ambient groups.

The source chooses product Haar measures and proves absolute convergence for
its compactly supported tests using properness in Proposition 17.8.2. In Lean,
the ambient measures are left Haar products, centralizer normalization is
an explicit pushforward equality, and the quotient measures are supplied with
compatibility hypotheses. The tests are continuous, factor integrability is a
hypothesis, and product integrability is part of the conclusion.
