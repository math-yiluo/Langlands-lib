# Henniart's numerical correspondence: conductors, unramified twists and orbit counts

Author: Worker 14 (task `62ea68fa-e1f4-4187-811b-7436743bba6a`, revision 1).
This module defines proposition targets and three small helper relations. It
proves none of the propositions.

Main declaration: `Langlands.Henniart.NumericalCorrespondenceStatement`, the
conjunction of `NumericalInjectionExistenceStatement`,
`NumericalSurjectivityStatement`, `NumericalOrbitCountStatement` and
`NumericalOrbitReductionStatement`. The helpers are in
`Langlands.Henniart.Numerical`.

## Sources

- G. Henniart, *La conjecture de Langlands locale numérique pour GL(n)*,
  Ann. Sci. ÉNS (4) 21 (1988), 497–544. Registered source
  `henniart-1988-numerical`, SHA-256
  `3de93884b6c4b26106d614e648cfb7f293f9f40a66ef352c0751e222a602f25c`.
  The retained Numdam scan has one cover page, so printed page `p` is PDF
  page `p − 495`. Passages read for this module: §§1.1–1.3, pp. 497–498
  (PDF 2–3), including the definitions of the class sets, of the twist
  action, of the conductor exponents and Théorème 1.2; §§1.9–1.10,
  pp. 501–502 (PDF 6–7), including the remark that the bijectivity of every
  admissible choice of injections follows by the counting arguments; §2,
  pp. 503–507 (PDF 8–12), including Proposition 2.2 (twists and stabilizers),
  Proposition 2.3 (finiteness of `C_K(n,j)`) and the counting argument of §2.8.
- G. Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur
  un corps p-adique*, Invent. Math. 139 (2000), 439–455. Registered source
  `henniart-2000-simple-proof`, SHA-256
  `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
  §1.3, pp. 440–441: an injection with `a(σ) = a(π(σ))`, equivalently with
  equal exponents of `q^(-s)` in the two epsilon factors, is bijective, "le
  résultat principal de [He 3]" (= Henniart 1988). §4.3, p. 453: "la
  surjectivité dans b) découle du résultat principal de [He 3]".
- H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika, *Conducteur des
  représentations du groupe linéaire*, Math. Ann. 256 (1981), 199–214,
  registered `jpss-1981-conductor`, SHA-256
  `986b06d6c16221fd55f04480604a1b17bf11004a704ab16b78acdd131ae6d49d`:
  Théorème 5.1, p. 211, for the last-row level groups and the newvector
  conductor of a generic representation. Its proof uses the corrected
  essential-vector theorem of Jacquet (2012), Theorem 1, p. 517
  (`jacquet-2012-conductor-correction`).

## Henniart's statement

Henniart 1988, §1.1, works with a local field `F`, a finite extension `K` of
`F` in `F̄`, the set `G⁰_K(n)` of classes of continuous irreducible complex
`n`-dimensional representations of `W_K`, and the set `A⁰_K(n)` of classes of
irreducible admissible supercuspidal representations of `GL(n, K)`. By §1.2
every element of either set has an Artin conductor exponent `a`, and the group
`X_K` of unramified characters of `K^×` acts on both sets by twisting:
`χσ = (χ ∘ τ_K) ⊗ σ` and `χπ = (χ ∘ det) ⊗ π`, where `τ_K` sends geometric
Frobenius elements to uniformizers. The footnote on p. 498 says that a
"caractère" is any continuous homomorphism to `ℂ^×`; unitarity is not
imposed. Théorème 1.2 reads: there is an injective map from `G⁰_K(n)` to
`A⁰_K(n)` which preserves conductors and is compatible with twisting by
unramified characters, and every such map is bijective.

## Objects and normalizations

The field is an actual `K : PadicField p` with its canonical topology. The
rank is written `k + 1`, so all positive ranks are covered and the
supercuspidal side has the form required by the published first-level
invariant. The Weil side is `Correspondence.IrreducibleWeilClass K
k.succPNat`, the genuine classes of continuous irreducible representations of
the constructed local Weil group; the supercuspidal side is
`Correspondence.SupercuspidalAutomorphicClass K k.succPNat`, the genuine
supercuspidal classes of `GL_(k+1)(K)` defined by vanishing Jacquet modules.
Weil carrier universe `uW` and supercuspidal carrier universe `uV` are
independent. These are the domains of `Correspondence.SupercuspidalMap`.

- `Numerical.HasArtinConductor K σ a`: some representative `A` of `σ` has an
  actual `Ramification.Padic.FiniteInertiaPresentation`, with surjective
  inertia restriction, whose Artin expression equals `a`. That expression is
  Serre's sum `Σ_i |G_i|/|G_0| · codim V^(G_i)` over the lower ramification
  filtration of the presenting finite Galois extension. The relation chooses
  no presentation. Integrality (Hasse–Arf), existence of presentations and
  independence of the presentation are separate published targets
  (`FiniteGaloisConductorIntegralityStatement` and
  `InertiaSurjectivityPresentationAndConductorIndependenceStatement`), not
  assumptions of this module.
- `Numerical.conductor K π`: the published
  `GeneralLinear.SupercuspidalClass.firstFixedLevel`, the least `a` for which
  the last-row congruence subgroup `K_(k+1)(a)` of JPSS 1981 fixes a nonzero
  vector, with value `⊤` if there is none. Henniart 1988 defines `a(π)`
  through the Godement–Jacquet epsilon factor (§2.5, p. 504). For generic
  representations JPSS 1981, Théorème 5.1, identifies that exponent with the
  newvector level; supercuspidal representations are generic. This module
  therefore uses the intrinsic newvector level as the conductor. That is a
  derived reformulation. The epsilon identification is the separate
  published statement `Langlands.Conductor.ConductorExponentStatement`; it is
  needed when the numerical theorem is applied to a map that preserves
  epsilon factors, as in Henniart 2000, §4.3.
- `Numerical.weilUnramifiedTwist K k z` twists by
  `Weil.Local.unramifiedCharacter (Weil.Local.localDegree K) z`, which sends
  an element of degree `d` to `z^d`. The published local degree sends
  geometric Frobenius to `+1` (`Weil/Local/Assembly.md`).
  `Numerical.supercuspidalUnramifiedTwist K k z` twists by
  `g ↦ z^(ord det g)` (`determinantUnramifiedCharacter`), the unramified
  character sending a uniformizer to `z`, composed with the determinant.
  With Henniart's geometric normalization of `τ_K`, the field character `χ`
  with `χ(ϖ) = z` pulls back to the Weil character with value `z` at
  geometric Frobenius. Hence the same `z` appears on both sides. Every
  `z ∈ ℂ^×` is allowed, as in Henniart's `X_K`.
- `Numerical.IsNumericalInjection K φ` is the conjunction of injectivity,
  conductor preservation (`HasArtinConductor K σ a → conductor K (φ σ) = a`)
  and compatibility with every unramified twist.
- `Numerical.weilOrbitStratum K k a` is the set of unramified-twist orbits,
  in the published quotient `Weil.UnramifiedOrbitClasses (localDegree K)`,
  that contain a class of dimension `k + 1` with Artin conductor `a`.
  `Numerical.supercuspidalOrbitStratum K k a` is the set of orbits, in the
  published quotient `PadicSupercuspidal.UnramifiedOrbitClasses K`, that
  contain a supercuspidal class of `GL_(k+1)` with conductor `a`. Both orbit
  quotients use every complex unit, so they identify classes differing by
  any unramified twist.

## The four propositions

`NumericalInjectionExistenceStatement`: for every prime `p`, p-adic field `K`
and `k`, some `φ` satisfies `IsNumericalInjection K φ`. This is the first
assertion of Théorème 1.2.

`NumericalSurjectivityStatement`: for every such `p`, `K`, `k` and every `φ`
with `IsNumericalInjection K φ`, `φ` is surjective. This is the second
assertion of Théorème 1.2 ("toute telle application est bijective"); with
injectivity it gives bijectivity. It is the input used for surjectivity in
Henniart 2000, §§1.3 and 4.3.

`NumericalOrbitCountStatement`: for every `p`, `K`, `k` and `a`, the two orbit
strata are finite and have the same cardinality (`Set.ncard`). This is the
sufficient finite counting result. It concerns finite sets of orbits of fixed
rank and conductor; no equality of infinite cardinalities is asserted or
used. Its provenance is derived: Henniart's Proposition 2.3 gives finiteness
of the Weil-side orbit counts `C_K(n, j)`, Bernstein–Zelevinsky finiteness
gives finiteness on the supercuspidal side, and the equality of counts is
equivalent to Théorème 1.2 by the argument of §2.8 (any bijection as in
Théorème 1.2 induces a bijection of the strata, and conversely).

`NumericalOrbitReductionStatement`: the counts, together with finiteness of
the conductor of every supercuspidal class, imply the surjectivity
proposition. The intended proof is elementary. An injective twist-compatible
`φ` induces a map of orbits that is injective and sends the Weil stratum
`(k, a)` into the supercuspidal stratum `(k, a)`. Equal finite cardinalities
make it onto that stratum, every supercuspidal orbit lies in some stratum
because its conductor is finite, and twist compatibility lifts orbit
surjectivity to surjectivity. The published elementary targets
`Langlands.Henniart.FiniteCountingStatement` and
`FiniteOrbitCountingStatement` describe the finite step. The finiteness of
every supercuspidal conductor follows from genericity and JPSS 1981,
Théorème 5.1; it is a premise here, not an assumption of the other
components.

## Retained source gaps and scope

- Henniart 1988, Théorème 1.3, the explicit count
  `C_K(n, j) = (q_K − 1) q_K^j`, is not stated. Its source chain uses Koch's
  1984 Satz 1, which the operator declined to supply (request
  `e6ae248a5a155ec3906cd2ff39478631`), and the previously recorded
  discrepancy in the summation range of §1.3 for Swan conductor zero is
  unresolved. The orbit-count proposition above is a weaker, sufficient
  formulation and does not depend on those formulas.
- Henniart's theorem covers local fields of any characteristic; this module
  states it for p-adic fields only, which is the case used by Henniart 2000.
- No local Langlands correspondence, epsilon-factor identity or global input
  is a hypothesis of any component. The map `φ` is arbitrary.
- The equal-characteristic comparison of Henniart 1988, §§1.5–1.6 and 8, the
  base-change arguments of §§1.7–1.9 and 6–7 and the reduction to
  `n = p^r` are proof inputs for `NumericalSurjectivityStatement`; none is
  stated here.

## Dependencies

All imports are accepted and published modules of Library commit
`18a1f10aef8ea135d90e8474439a5e6d9c130008`; the table gives the first twelve
hexadecimal digits of the SHA-256 of each `.lean` file there.

| Module (under `Langlands/`) | Declarations used | `.lean` SHA-256 |
| --- | --- | --- |
| `Correspondence/SupercuspidalSpecification` | through its imports of `Correspondence/Domains` (`34903bc08863`) and `Correspondence/SupercuspidalRelations` (`701f46d9e700`): `IrreducibleWeilClass`, `SupercuspidalAutomorphicClass`, `weilClassForget` | `b40cc87cb82b` |
| `LocalFactor/Ramification/InertiaPresentation` | `FiniteInertiaPresentation`, `.artinConductor`, `weilInertiaRestriction` | `84c62107d6a3` |
| `Representation/Classification/SupercuspidalStrata` | `GeneralLinear.SupercuspidalClass.firstFixedLevel` | `fe7fddcd7c5c` |
| `VirtualRepresentation/Weil/Local` | local Weil basis | `841da167450a` |
| `VirtualRepresentation/Weil/Twist` | `Weil.UnramifiedOrbitClasses`, `Weil.unramifiedOrbitClass` | `10cace6b1825` |
| `VirtualRepresentation/Supercuspidal/Unramified` | `PadicSupercuspidal.UnramifiedOrbitClasses`, `PadicSupercuspidal.unramifiedOrbitClass` | `d90f3ddcac6b` |

Declarations reached through these imports: `Weil.Local.unramifiedCharacter`
(`Weil/Local/DegreeCharacters`, `f93ff5bdd74c`), `Weil.Local.localDegree`
(`Weil/Local/Assembly`, `576d8ad3c157`),
`FiniteRepresentation.continuousIrreducibleTwistEquiv`
(`Weil/Representation/TwistClasses`, `210fff747f1e`),
`Supercuspidal.twistClassEquiv` (`VirtualRepresentation/Supercuspidal/Twist`,
`2e54337a39ca`) and `determinantUnramifiedCharacter` with its two kernel
lemmas (`Group/GL/UnramifiedCharacter`, `69df6a7fd220`).

## Proof obligations

Each of the four components is a separate proof obligation. The reduction is
elementary. Existence and surjectivity are Henniart's 1988 theorem, whose
proof uses Laumon's local Fourier transform, the comparison of close local
fields, Arthur–Clozel base change and the counting of §2. The orbit counts
follow from Théorème 1.2 with the finiteness results named above.
