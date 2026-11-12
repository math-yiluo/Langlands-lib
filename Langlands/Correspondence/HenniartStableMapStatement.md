# Removing the auxiliary choices in Henniart's construction

Author: Worker 14 (task `62ea68fa-e1f4-4187-811b-7436743bba6a`, revision 1).
This module defines proposition targets and a few helper predicates for
Henniart's local argument in §4 of his 2000 paper. It proves none of the
propositions.

Main declaration: `Langlands.Henniart.HenniartStableMapStatement`, the
conjunction of the ten propositions described below. The helpers are in
`Langlands.Henniart.StableMap`.

## Sources

- G. Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur
  un corps p-adique*, Invent. Math. 139 (2000), 439–455. Registered source
  `henniart-2000-simple-proof`, SHA-256
  `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
  Printed page `p` is PDF page `p − 438`. Passages read for this module:
  §§1.2–1.4 and 1.9–1.10, pp. 440–443; §§2.5–2.8, pp. 445–448; §§3.1, 3.7–3.8,
  pp. 448 and 451; §4, pp. 452–453 (PDF 14–15).
- G. Henniart, *Caractérisation de la correspondance de Langlands locale par
  les facteurs ε de paires*, Invent. Math. 113 (1993), 339–350. Registered
  source `henniart-1993-epsilon-pairs`, SHA-256
  `057967169237036da64c0e5a72c69e8ddfd69176bebade0ef13588de24809763`.
  Printed page `p` is PDF page `p − 338`. Passages read: Théorème 1.1 and its
  Corollaire, pp. 339–340; §4, pp. 348–349 (Théorème 4.1 and the extension by
  unramified twists in §§4.2–4.4).
- G. Henniart (1988), Théorème 1.2, p. 498, through the companion module
  `HenniartNumericalStatement`.

## Henniart's argument

§3.7 (p. 451) composes `R_E(F) ↪ R_G(F, 0) ≅ R_A(F, 0) → R_A(F)` for a finite
Galois extension `E/F`; §3.8 lists its properties: degree, contragredient,
determinant/central character and twists (a), pair L and ε factors (b),
irreducible classes go to supercuspidal classes and rank-one classes are given
by class field theory (c). The composite depends a priori on the global choices
of §3 (§3.7, last sentence; §4.1).

Théorème 4.2 (p. 452): (a) for every `σ ∈ G⁰_F(n)` factoring through a finite
Galois extension there is `E(σ)` such that the constructions of §3 always give
the same `ρ(σ)` once `E ⊇ E(σ)`; (b) the resulting map is a bijection from the
classes with finite-order determinant onto the supercuspidal classes with
finite-order central character, compatible with contragredients, central
characters and finite-order twists; (c) it preserves pair L and ε factors.

§4.3 (pp. 452–453) proves this by induction on `n`. For `n ≥ 2`, the central
character of `ρ(σ)` and its conductor are imposed, so `ρ(σ)` lies in a finite
set `P`. Two distinct members of `P` are separated by a lower-rank epsilon test
(Théorème 1.4, i.e. Henniart 1993); after an unramified twist the test has
finite-order central character, and by induction it is `ρ(σ')` for some
lower-rank `σ'`. Enlarging `E` to contain `E(σ')` for the finitely many tests
fixes `ρ(σ)`. Injectivity and the compatibilities come from 3.8; surjectivity
comes from Henniart 1988. §4.4 (p. 453) extends `ρ` to every irreducible `σ` by
`ρ(σ) = χ ρ((χ ∘ τ_F)⁻¹ σ)` for an unramified `χ` making the determinant of
finite order, independently of `χ`, and refers to Henniart 1993, §4, for the
remaining (easy) arguments.

## Objects

Throughout, `K : PadicField p` is an actual p-adic field with its canonical
topology. Field universe `uK`, Weil carrier universe `uW`, supercuspidal
carrier universe `uV`, local-constant-system universe `uE` and the universe
`uQ` of finite quotients in `CandidateExistenceStatement` are independent.
Finite quotients inside the helper predicates live in `Type uK`; every finite
quotient of the absolute Galois group has a model there.

- The lattices are the published `LocalWeil.UnitaryLattice K` (free on actual
  unitary irreducible Weil classes of all dimensions) and
  `PadicSupercuspidal.UnitaryLattice K` (free on actual unitary supercuspidal
  classes of all ranks). The target is the group on supercuspidal classes, not
  on all irreducible representations of `GL_n(K)`.
- A finite Galois extension `E/K` is represented by a homomorphism `q` from
  the absolute Galois group of `K` to a finite group. `R_E(K)` is the published
  `LocalWeil.unitaryFiniteFactoringSupported K q`: unitary classes factoring
  algebraically through `q` composed with the projection of the Weil group.
  Continuity or surjectivity of `q` is not required; a finer quotient gives a
  larger lattice.
- `StableMap.IsCandidate K q Φ`: `Φ : W ≃ₗ[ℤ] A` is a linear equivalence of
  sublattices, `R_E(K) ≤ W`, and `Φ` satisfies the published
  `Correspondence.LatticeMap.HenniartProperties K Φ`. That predicate is the
  conjunction of the properties of 3.8 at `K` (as transported from Henniart's
  Proposition 2.6 by the H3 program): preservation of pairings and degrees,
  irreducible classes correspond exactly to supercuspidal classes, contragredient,
  twists by every modulus-one character along every geometric reciprocity
  candidate, rank-one characters, determinant/central character, and pair L and
  ε factors for every nontrivial additive character, self-dual measure and
  local-constant system. These are the separate clauses of a definition; no
  structure or construction field assumes any theorem.
- `StableMap.IsFiniteFactoring K σ`: the generator of `σ` lies in
  `R_E(K)` for some finite quotient. For irreducible classes this is
  equivalent to finite image and to finite-order determinant (Henniart 1988,
  §2.2), which is not asserted here.
- `StableMap.IsStableImage K σ y`: for one finite quotient `q` through which `σ`
  factors, some candidate at `q` exists, and every candidate at `q` sends the
  generator of `σ` to `y`. Since a candidate at a finer quotient is a candidate
  at `q`, this is Henniart's condition "pour tout `E` contenant `E(σ)`". The
  existence clause prevents a vacuous stable image.
- `StableMap.HasFiniteOrderCentralCharacter K π`: some `ω : K^× →* ℂ^×` is the
  central character of `π` (published `IsUnitaryBasisCentralCharacter`) and has
  finite order.
- `StableMap.StableExistsAt K n`, `StableMap.StableSurjectiveAt K n` and their
  conjunction `StableMap.RankStage K n`: in dimension/rank `n`, every
  finite-image unitary irreducible class has a stable image; every unitary
  supercuspidal class with finite-order central character is the stable image of
  a finite-image unitary irreducible class of the same dimension.
- `StableMap.weilUnramifiedTwist K z`: twist of an irreducible Weil class by the
  character sending geometric Frobenius to `z` (the published local degree sends
  geometric Frobenius to `+1`). On the supercuspidal lattice the published
  `PadicSupercuspidal.unramifiedTwistLatticeEquiv K z` twists by
  `g ↦ z^(ord det g)`. With Henniart's normalization of `τ_F` the same `z`
  appears on both sides.

## Derived reformulation: candidates instead of the global constructions

Henniart's 4.2 (a) speaks of the maps produced by the global constructions of
§3. Here a stable image is defined using every local map with the properties of
3.8. This is stronger than the printed assertion and is the form in which
§4.3 uses the constructions: its proof invokes only 3.8. It applies to
Henniart's maps through the published H3 statements. For the relative
witnessed pairs, `Langlands.Global.PoleComparison.HenniartCompositeMapStatement`
gives `HenniartProperties` for `henniartCompositeMap` at `K`, and
`Langlands.Global.HenniartGlobalizationStatement` with
`continuousRestrict_completionWeilTransport_eq_iff` gives `R_E(K) ≤ W` for the
transported Weil image. Under their hypotheses the composite is a candidate.
`HenniartProperties` uses twists by every modulus-one character, as in
Proposition 2.6 (a), rather than only characters trivial on `N_(E/F)(E^×)` as
printed in 3.8 (a); the transported image satisfies the former.

## The propositions

1. `CandidateExistenceStatement`: for every `p`, `K` and finite quotient `q` (in
   any universe `uQ`), there is a candidate at `q`. This is the local output of
   Théorème 3.1 with §§3.7–3.8.
2. `ChoiceIndependenceStatement`: every finite-image unitary irreducible class
   has a stable image. This is Théorème 4.2 (a).
3. `SupercuspidalEpsilonConductorFinitenessStatement`: for a fixed nontrivial
   additive character `ψ` and self-dual measure `ν`, a fixed central character
   `ω` and a fixed integer `m`, the supercuspidal classes of `GL_(k+1)(K)` with
   central character `ω` whose epsilon factor against the trivial character of
   `GL_1(K)` is `c q^(-ms)` for some `c` form a finite set. This is the finite
   set `P` of §4.3 ("caractère central imposé", "conducteur imposé par
   `ε(σ, s, ψ) = ε(π, s, ψ)`"). The epsilon relation is the published
   `Correspondence.IsSupercuspidalPairEpsilonFactor`, the relation used by
   `HenniartProperties` on basis classes, with the published
   `rankOneSupercuspidalClass K 1`. For fixed `ψ`, `m` differs from the
   conductor of `π` by a shift depending only on `ψ` and `k + 1` (Henniart
   1988, §2.5, p. 504). The finiteness is derived from the published
   bounded-level finiteness (Bernstein–Zelevinsky 1976, Corollary 4.15), the
   genericity of supercuspidal representations and JPSS 1981, Théorème 5.1
   (`Langlands.Conductor.ConductorExponentStatement`).
4. `RankOneStageStatement`: `RankStage K 1`, the base case given by local class
   field theory (§4.1, last sentence; §4.3, "clair pour `n = 1`").
5. `ChoiceIndependenceStepStatement`: for `n > 1`, if `RankStage K r` holds for
   every `r < n`, then `StableExistsAt K n`. The lower-rank stable images and the
   lower-rank surjectivity are the explicit hypotheses used to lift the
   separating tests.
6. `SurjectivityStepStatement`: `StableExistsAt K n` implies
   `StableSurjectiveAt K n`, the last sentence of §4.3, by Henniart 1988.
7. `RankInductionStepStatement`: for `n > 1`, `RankStage K r` for all `r < n`
   implies `RankStage K n`.
8. `StableCorrespondenceStatement`: `RankStage K n` for every `n`, i.e.
   Théorème 4.2 (a) and the bijectivity in (b). The other clauses of (b) and (c)
   are inherited from `HenniartProperties` at a common candidate.
9. `UnramifiedTwistIndependenceStatement`: if `σ₁ = z₁⁻¹ σ` and `σ₂ = z₂⁻¹ σ`
   (unramified twists of one irreducible class `σ`) have stable images `y₁`,
   `y₂`, then `z₁ y₁ = z₂ y₂` in the supercuspidal lattice. This is the
   independence of the choice of `χ` in §4.4 and Henniart 1993, §4.3.
10. `HenniartConstructionStatement`: for every `p` and `K` some
    `c : SupercuspidalMap K` satisfies the published
    `IsSupercuspidalCorrespondence K c` and sends every finite-image unitary
    irreducible class to its stable image. This is Henniart's Théorème 1.2
    obtained by his construction (§4.4 with Henniart 1993, §§4.3–4.4).

In 5–7 the quantifier order is: `p`, `K`, `n`, `1 < n`, the lower-rank stages,
then the conclusion. All objects are actual; the inductive hypotheses are
propositions about the same stable-image relation.

## Scope and retained obligations

- No component assumes a local Langlands correspondence. Proposition 10
  concludes one; the existing `SupercuspidalCorrespondenceStatement` and the
  uniqueness statements remain separate.
- The relative H3 statements are not the absolute-global `R_G(F, 0)` of
  Henniart 2.5; the absolute global construction remains with its owners.
  Proposition 1 is stated locally and does not depend on that choice.
- The finite separating tests are the published Worker 78 statement
  `Langlands.Henniart.SupercuspidalFiniteEpsilonStatement`. It uses the
  class relation `RankinSelberg.IsClassEpsilonFactor`, whereas
  `HenniartProperties` and Proposition 3 use
  `Correspondence.IsSupercuspidalPairEpsilonFactor`; a comparison of the two
  JPSS relations is a retained proof obligation for Proposition 5.
- The surjectivity step needs the extension of the stable map to all classes of
  dimension `n` by unramified twists, the conductor identifications on both
  sides (`Langlands.LocalFactor.ConductorExponentStatement` and
  `Langlands.Conductor.ConductorExponentStatement`) and Henniart 1988
  (`Langlands.Henniart.NumericalSurjectivityStatement`).
- The existence of an unramified twist with finite-order determinant is the
  parameter-branch statement owned by task
  `ce2095a8-9814-480e-ac62-bd2f27fa88ae`; it is reused, not restated.
- Proposition 10 also needs the behaviour of pair L and ε factors under
  unramified twists on both sides (Henniart 1993, §4.4) and the local converse
  theorem for uniqueness in each rank.
- Every unitary supercuspidal class with finite-order central character is
  covered by Proposition 8; that every supercuspidal class with finite-order
  central character is unitarizable is not asserted here.

## Dependencies

All imports are accepted and published modules of Library commit
`18a1f10aef8ea135d90e8474439a5e6d9c130008`; the table gives the first twelve
hexadecimal digits of the SHA-256 of each `.lean` file there.

| Module (under `Langlands/`) | Declarations used | `.lean` SHA-256 |
| --- | --- | --- |
| `Global/Factors/HenniartCompositeMapStatement` | `Correspondence.LatticeMap.HenniartProperties` | `486f1396356c` |
| `Correspondence/SupercuspidalSpecification` | `IsSupercuspidalCorrespondence`, `SupercuspidalMap` | `b40cc87cb82b` |
| `Correspondence/RankOneExistence` | `rankOneSupercuspidalClass` | `1a7cd13b9588` |
| `VirtualRepresentation/Weil/Twist` | `Weil.twistBasisEquiv` | `10cace6b1825` |
| `VirtualRepresentation/Supercuspidal/Unramified` | `PadicSupercuspidal.unramifiedTwistLatticeEquiv` | `d90f3ddcac6b` |

Declarations reached through these imports:
`LocalWeil.unitaryFiniteFactoringSupported`, `LocalWeil.UnitaryBasis`,
`LocalWeil.UnitaryLattice`, `LocalWeil.Basis`
(`VirtualRepresentation/Weil/Local`, `841da167450a`);
`PadicSupercuspidal.UnitaryBasis`, `PadicSupercuspidal.UnitaryLattice`,
`PadicSupercuspidal.Basis`, `PadicSupercuspidal.includeUnitary`
(`VirtualRepresentation/Supercuspidal/Basic`, `27a08f4c78ca`);
`PadicSupercuspidal.IsUnitaryBasisCentralCharacter`
(`Global/Factors/RelativeIsometryFactorStatement`, `5b769806a3cc`);
`SupercuspidalCentralActsBy` (`Correspondence/SupercuspidalRelations`,
`701f46d9e700`); `IsSupercuspidalPairEpsilonFactor`
(`Correspondence/SupercuspidalFactorCompatibility`, `28f432e159f2`);
`NontrivialAdditiveCharacter`, `LocalAdditiveHaarMeasure`, `IsSelfDualMeasure`
(`Correspondence/LocalConventions`, `da20981c4fca`); `generator`
(`VirtualRepresentation/Integral`, `785418baa91b`);
`Weil.Local.unramifiedCharacter` (`Weil/Local/DegreeCharacters`,
`f93ff5bdd74c`) and `Weil.Local.localDegree` (`Weil/Local/Assembly`,
`576d8ad3c157`).

## Proof obligations

Each of the ten propositions is a separate proof obligation. Proposition 1
follows the H3 route named above under its deep hypotheses (Harris 1998,
Proposition 4.8, certified pole comparisons and arithmetic class families).
Propositions 2 and 4–8 follow §4.3 with the inputs listed under Scope.
Proposition 9 needs Proposition 1 for a common candidate and the twist clause of
`HenniartProperties`. Proposition 10 needs Propositions 8–9, the parameter-side
unramified reduction and the factor laws of Henniart 1993, §4.4.
