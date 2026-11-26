# Cyclically twisted Weyl integration for GLₙ

`Langlands.BaseChange.TwistedWeylIntegrationFormulaStatement` states the
cyclically twisted Weyl decomposition of Haar integrals on `GL_n(E)`. Here `F`
is a nonarchimedean local field of any characteristic. `E` is an
`F`-algebra in an independent universe with the module topology, and
`IsCyclicAlgebra σ l` holds: `E` is reduced and finite of rank `l` over `F`,
and `σ` has order `l` with fixed algebra `F`. The rank `n` may be zero.

## Data and normalizations

The statement quantifies over the following data:

- a Haar measure `μE` on `GL_n(E)`;
- a set `S` with `WeylTorus.IsRepresentativeSet S`, one rational maximal torus
  from each `GL_n(F)`-conjugacy class;
- a Haar measure `μT T` on the rational points `T(F)` of each `T` in `S`;
- a right Haar measure `μC T γ` on the centralizer `glCentralizer γ` at each
  point `γ` of `T.regularPoints`, with the same pushforward to `GL_n(F)` as
  `μT T`.

At a regular point of `T` the centralizer is `T(F)` itself, so the last
condition identifies `μC T γ` with `μT T`. This is the normalization of the
centralizer measures `dg_γ` by the torus measures `dγ_T` on p. 72 of the
source.

The statement then asserts the existence of the following data, chosen once
for all input functions. For every `T` in `S` and every `γ` in
`T.regularPoints ∩ T.normImage σ l`:

- a lift `lift T γ` in `T.points E` with
  `cyclicNorm σ l (lift T γ) = baseChange F E n γ`;
- a right Haar measure `μD T γ` on the σ-centralizer
  `sigmaCentralizer σ n (lift T γ)` that satisfies `IsAssociatedMeasure` with
  `μC T γ`;
- a measure `ν T γ` on the left coset space of that σ-centralizer that
  satisfies `QuotientIntegration.IsCompatible` with `μE` and `μD T γ`.

These are the measures on the σ-centralizers and on the quotients
`G^σ_δ(F) \ G(E)` that the σ-orbital integral `Λ^{G(E)}_σ(φ, δ)` uses in the
source. They follow the associated-measure convention of Henniart–Lemaire,
I.2.5.

## The norm quotient as a subset of the rational torus

Formula (1) integrates over `T(E)^{σ-1} \ T(E)` against a measure `dδ_{T,σ}`.
On p. 71 the source shows that `1 → T(E)^{σ-1} → T(E) → T(F)` is exact, by
Hilbert's Theorem 90, and that the norm `N : T(E) → T(F)` is open. The norm
therefore identifies the quotient with the open subgroup `N(T(E))` of `T(F)`,
and `dδ_{T,σ}` is the transport of the restriction of `dγ_T` to this
subgroup.

The statement integrates over this image instead of the quotient. The
domain is `T.normImage σ l`, the rational torus points that are norms of
points of `T.points E`. The measure is the rational torus Haar measure
`μT T`, and the torus integrand is zero off `T.regularPoints ∩ T.normImage σ l`.
The non-regular points of `T(F)` form a Haar-null set, on which the source's
integrand need not be evaluated.

At a regular point `γ` of the image, the σ-orbital integral at the class of
`δ` with `N(δ) = γ` is evaluated at the chosen exact lift `lift T γ`. Two
exact lifts `δ` and `δ'` of `γ` differ by an element of the kernel
`T(E)^{σ-1}` of the norm, so `δ' = t⁻¹ δ σ(t)` for some `t` in `T(E)`. Their
σ-centralizers are the same subgroup, the image of `T(F)`, which `t`
centralizes. So left translation by `t` descends to the quotient. It
preserves the compatible quotient measure, since `μE` is invariant and the
compatible measure is unique. Hence the σ-orbital integral `Λ_σ(φ, δ)` takes
the same value at every exact lift of `γ`. The other factor `Θ(δ)` of the
source's integrand need only descend almost everywhere. This is treated in
the section on the L¹ formulation.

The source's weight `|D_G(N(δ))|_F` is the ordinary discriminant at the norm
`γ`. With the factor `|W_T(F)|⁻¹` it is `WeylTorus.integrationWeight T γ`,
the same weight as in the ordinary formula.

## The integration identity

The conclusion concerns every complex function `φ` integrable against `μE`:

- for each `T` in `S` and `μT T`-almost every `γ` in the regular norm image,
  the σ-orbit function `x ↦ φ(x⁻¹ · lift T γ · σ(x))` is integrable on the
  quotient against `ν T γ`;
- the torus integrand
  `γ ↦ integrationWeight T γ · sigmaOrbitalIntegral σ n (lift T γ) (ν T γ) φ`,
  extended by zero, is integrable against `μT T`;
- the integrals of the norms of these integrands are summable over `S`;
- the integral of `φ` against `μE` is the sum over `S` of their integrals.

The left side is an integral over all of `GL_n(E)`. The σ-orbits of the
chosen lifts make up the set of elements whose norm class is regular
semisimple, which is the locus of the predicate `IsSigmaRegular`. Indeed, an
element `δ` associated with a regular semisimple `γ'` is σ-conjugate to an
element of norm `γ`, where `γ` is a conjugate of `γ'` in `T(F)` for some `T`
in `S`. That element commutes with its norm `γ`, so it lies in `T(E)`, and it
is σ-conjugate under `T(E)` to `lift T γ`. By the remark on p. 71 of the
source, this locus is the set of σ-semisimple σ-regular elements, where the
twisted discriminant `D_{G,σ}` does not vanish. Its complement is the zero
set of this polynomial function, which is not identically zero, so the
complement is Haar-null.

The source's σ-regular set `G(E)_{σ-r}` of II.2.2 is larger in positive
characteristic. It asks only that the characteristic polynomial of the norm
class be a product of distinct irreducible factors, which need not be
separable. For example, for `E = F = 𝔽_p((t))` with `σ` the identity, the
companion matrix of the Eisenstein polynomial `X^p − t` lies in it. Such
classes lie in the zero set of `D_{G,σ}`, so they do not contribute to the
integral.

## The L¹ formulation

The source states formula (1) for `φ` in `C_c^∞(G(E))` and a locally
integrable function `Θ` on `G(E)` such that `Θ(g⁻¹ δ σ(g)) = Θ(δ)` for almost
every `δ` in `G(E)_{σ-r}` and every `g` in `G(E)`. The left side has
`φ(g)Θ(g)` and the right side has `Λ^{G(E)}_σ(φ, δ)Θ(δ)`. The Lean statement
expresses the underlying measure decomposition for every `L¹` input. The
product `φΘ` is `μE`-integrable, and the statement applied to it gives the
torus integrands `integrationWeight T γ · Λ_σ(φΘ, lift T γ)`. These agree
with the integrand of formula (1) for almost every regular norm parameter:

- Let `A` be the set of `δ` with `Θ(g⁻¹ δ σ(g)) = Θ(δ)` for every `g`. It is
  a union of σ-orbits, and `Θ` is constant on each σ-orbit in `A`. By the
  hypothesis, the points of the `IsSigmaRegular` locus outside `A` lie in a
  Haar-null Borel set `N`.
- Apply the statement to the indicator of `N`, which is integrable with
  integral zero. Its torus integrands are nonnegative and their integrals
  sum to zero, so they vanish almost everywhere. The weight is positive at
  regular points. So for `μT T`-almost every `γ`, the σ-orbit function of the
  indicator of `N` at `lift T γ` is integrable with integral zero, hence
  vanishes almost everywhere on the quotient. The quotient
  measure is nonzero, so the σ-orbit of `lift T γ` meets `A` and therefore
  lies in `A`.
- For such `γ`, `Θ` is constant on the σ-orbit of `lift T γ`, so
  `Λ_σ(φΘ, lift T γ) = Θ(lift T γ) · Λ_σ(φ, lift T γ)`. This σ-orbit contains
  every `δ` in `T(E)` with `N(δ) = γ`. So the source's integrand
  `Λ_σ(φ, δ)Θ(δ)` is well defined at the class over `γ` in
  `T(E)^{σ-1} \ T(E)`, and it takes this value.

With the transport of `dδ_{T,σ}` described above, the decomposition of `φΘ`
is therefore formula (1). When `Θ(g⁻¹ δ σ(g)) = Θ(δ)` holds at every point,
only the last step is needed.

Mathlib's Bochner integral is zero on non-integrable functions, so the
statement asserts integrability of the orbit functions and of the torus
integrands explicitly. It also asserts summability of their `L¹` norms over
`S`, so that the sum over the representative tori converges absolutely.

## Source

Henniart–Lemaire, *Changement de base et induction automorphe pour GLₙ en
caractéristique non nulle*, Mém. SMF 124 (2011), II.2.10, printed pp. 70–72
(PDF pp. 78–80), formula (1). The registered source ID is
`provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`.
The torus data, the norm image and the weight are those of
`Langlands.BaseChange.WeylIntegrationData`. The σ-centralizers, σ-orbital
integrals and associated measures are those of
`Langlands.BaseChange.OrbitalIntegral`.
