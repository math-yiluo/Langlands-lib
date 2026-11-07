# Completeness of Whittaker functions (statement)

`Langlands.Whittaker.WhittakerCompletenessStatement.{uF,uV}` states Jacquet and
Shalika, *A lemma on highly ramified ε-factors*, Math. Ann. 271 (1985),
Lemma (3.2), printed page 325 (one-based PDF page 7). This module only defines the
proposition; it does not prove it.

## Original sources and conventions

Jacquet–Shalika write `G_r = GL_r(F)`, let `N_r` be its upper unitriangular
subgroup, and set `θ(u) = ψ(u_12 + u_23 + ... + u_(r-1,r))` in §3.1, printed
page 324. Lemma (3.2) concerns a smooth complex function `H` satisfying
`H(ug) = θ̄(u) H(g)` and having compact support modulo `N_r`. Its hypothesis
tests `H` against every function in every irreducible admissible generic
Whittaker model, and its conclusion is pointwise vanishing of `H`.
Because `ψ` is unitary, `θ̄ = θ⁻¹`, as used by the Lean formulation.

The registered source is `jacquet-shalika-1985-ramified-factors`, SHA-256
`0864a6633c3cf430f576f91eadd05a7f11d88eea1b47095943d3ea76f7c9946b`:
H. Jacquet and J. Shalika, *A lemma on highly ramified ε-factors*,
Math. Ann. 271 (1985), 319–332, §3.1 and Lemma (3.2), printed pages 324–325
(one-based PDF pages 6–7).

The printed proof of Lemma (3.2) refers to the argument of JPSS 1981,
Lemme (3.5), printed page 207 (one-based PDF page 9). That earlier lemma
has spherical tests and a right maximal-compact invariance hypothesis.
Its proof decomposes a unitary induced representation into irreducible
representations; JS85 cites that argument with modifications for the
all-model, arbitrary-open-subgroup version stated here. The extra spherical
restriction of JPSS Lemme (3.5) is not a hypothesis of JS85 Lemma (3.2).
The registered source is `jpss-1981-conductor`, SHA-256
`986b06d6c16221fd55f04480604a1b17bf11004a704ab16b78acdd131ae6d49d`:
H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika,
*Conducteur des représentations du groupe linéaire*,
Math. Ann. 256 (1981), 199–214.

JS85 §1.1 fixes an additive character of conductor the ring of integers for
convenience in its conductor formulas. The completeness formulation here
allows every nontrivial unitary additive character: separation by all
Whittaker models does not require that conductor normalization. This is
the conductor-independent reading of Lemma (3.2), rather than a statement
of one of the subsequent conductor identities.

## Quantifiers and hypotheses

The proposition quantifies over every natural prime `p` with `[Fact p.Prime]`
and every `F : PadicField.{uF} p`. It installs the topology, valuative relation
and nonarchimedean local-field certificate from `F.canonicalTopologicalData`.
The general linear group, its upper unipotent subgroup, and their left quotient
carry the Borel measurable structures of these topologies. Every `n : ℕ`
is allowed, so the rank `r = n + 1` includes rank one.

`ψ : UnitaryAdditiveCharacter F.Carrier` already includes continuity,
nontriviality and values in the unit circle. Its standard character on
`N_(n+1)` is `Whittaker.standardCharacter ψ n`.
`H : RankinSelberg.InverseWhittakerFunctions ψ n` is an actual function on
`GL_(n+1)(F)` with the law `H(ug) = θ(u)⁻¹ H(g)`.
The two following hypotheses say:

- Some `K : OpenSubgroup GL_(n+1)(F)` fixes `H` under right translation:
  `H(g k) = H(g)` for every `g` and every `k ∈ K`. This encodes smoothness.
  The subgroup may depend on `H`.
- Some compact set `C` in the group contains representatives of all cosets
  on which `H` is nonzero: `H(g) ≠ 0` implies `g = u c` with `u ∈ N_(n+1)`
  and `c ∈ C`. This is support in `N_(n+1) C`, namely compact support
  modulo `N`, rather than compact support in the group.

The vanishing hypothesis quantifies over every carrier `V : Type uV`,
every additive group and complex module structure on it, and every actual
representation `π` of this same general linear group with
`Whittaker.IsGeneric ψ n π`. This predicate includes irreducibility,
admissibility (and hence smoothness), and existence of a nonzero standard
Whittaker functional. It then quantifies over every
`ℓ : Whittaker.glFunctionals ψ n π` and every vector
`w : (Whittaker.coefficientModel π ℓ).toSubmodule`. Such a vector gives the
actual function `W(g) = ℓ(π(g)v)` for some `v`. Allowing the zero functional
adds only the zero model. No preferred nonzero functional is chosen.
The universes `uF` and `uV` are independent; no topology on `V` is required.

The conclusion is `∀ g, H.val g = 0`, so it concerns the original function
at every group element. No unramified or supercuspidal restriction is
placed on the representations.

## Quotient integrand and measure

The existing `RankinSelberg.whittakerProductIntegrand ψ W H` descends `g ↦ W(g) H(g)` to the actual space
`RankinSelberg.LeftUnipotentQuotient n F.Carrier`, namely
`N_(n+1) \ GL_(n+1)(F)`. The standard and inverse characters cancel by the
published theorem `RankinSelberg.whittaker_product_invariant`.
Complex multiplication makes this the source's product `H(g) W(g)`.
This descent is reused from `SupercuspidalProductCompletenessStatement`; it
introduces no representation-theoretic assumption.

The statement uses the Bochner integral against the published measure
`RankinSelberg.unipotentQuotientHaar F.Carrier n`.
`RankinSelberg.unipotentQuotientHaar_isCompatible` certifies compatibility
with `generalLinearHaar F.Carrier n` and `unipotentHaar F.Carrier n`.
These Haar measures give mass one to `GL_(n+1)(O_F)` and `N_(n+1)(O_F)`,
respectively. Compatibility includes nonzeroness, regularity, right
translation invariance and the Weil identity

`∫_{N\G} (∫_N f(u g) du) dμ = ∫_G f(g) dg`

for compactly supported continuous complex functions, including
integrability of the averaged function.

For these fixed ambient and subgroup Haar measures,
`RankinSelberg.unipotentQuotientHaar_unique` proves that every compatible
quotient measure equals this one. If instead the Haar normalizations
are changed by positive finite factors `a` and `b`, respectively, the
Weil identity gives the quotient normalization `(a / b) μ`.
The integral of `W H` is multiplied by the same nonzero scalar, so its
vanishing is independent of that choice of Haar normalizations.
This rescaling explanation is mathematical context; this module does
not formalize a new measure-rescaling theorem.

There is no separate integrability premise. Under the stated hypotheses,
`H` is locally constant by its open right stabilizer, and `W` is locally
constant because admissibility includes smoothness. Their invariant
product descends to a continuous function supported in the compact image
of `C` in the Hausdorff quotient. It is therefore integrable for the regular
quotient measure. This explains the use of the total Bochner integral
without weakening the source's vanishing hypothesis. The module defines
the completeness proposition; it supplies no proof of completeness or
of this integrability consequence.
