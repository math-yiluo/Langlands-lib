# Exact actual-point targets for Waldspurger VIII.3

These are **unproved proposition definitions** for Proposition VIII.3.1
(printed p.323, proof pp.323–326; PDF pp.89–92) and Corollary VIII.3.2
(printed pp.326–327; PDF pp.92–93) of J.-L. Waldspurger,
*La formule de Plancherel pour les groupes p-adiques*, 2003,
DOI 10.1017/S1474748003000082, registered as
`waldspurger-2003-plancherel`. The elementary quotient equivalence
is an internal transport lemma, not an analytic proof.

## Complete structural premises

Each closed statement quantifies over the following data:

- An arbitrary universe `u`, a field `F : Type u` with its valuation,
  topology and `IsNonarchimedeanLocalField` instance, and an affine,
  locally finite type group scheme `G` over `F` with
  `IsConnectedReductive G`.
- A commutative group scheme `S`, an actual maximal split torus
  `i : S.toGrp → G`, and a generic cocharacter `ν` selecting the actual
  minimal parabolic `standardParabolicPoints i ν ∅`.
- A subgroup `K0` satisfying the precisely named external
  `SimultaneousStandardBasisAt i ν K0`. This is the Renard V.5.2
  structural input used in the published rational Xi statement, not a
  package of analytic estimates. It is separate from the next choice.
- An open subgroup `K` of the actual rational points, its compactness
  proof `hKc`, and the Iwasawa pair `hPK` for this `K` and the minimal
  parabolic.
- A nonempty finite matrix index `Fin N` and a matrix representation
  `ρ` satisfying `IsClosedSubgroup ρ`. The Schwartz space is the existing
  `RationalSchwartzSpace hKc hPK ρ`, with the canonical rational-point
  topology and Borel structure, actual Xi and actual matrix height.
- An actual group measure `muG` satisfying `muG.IsHaarMeasure`.

The integrability statement additionally quantifies over a commutative
group scheme `T`, an actual split component `s : T.toGrp → G` and
`hs : IsSplitComponent s`. Its central subgroup is exactly
`A = (rationalPoints.map s).range`. It displays the Borel measurable
structures of `A` and `LeftQuotient A`, a Haar measure `muA` on `A`
with explicit `muA.IsMulRightInvariant`,
a measure `muQ` on `LeftQuotient A`, and
`QuotientIntegration.IsCompatible A muG muA muQ`.
That compatibility includes nonzero regularity, right invariance and
the complex Weil formula. It is not compatibility along `G¹`.
Existence of such a measure is not asserted in this unit.

There is no characteristic-zero, split-group, quasi-split or
positive-rank hypothesis. The finite residue-field and nonarchimedean
conditions are those of `IsNonarchimedeanLocalField`. All structural
choices remain quantified. No estimate, convergence, summability,
kernel reproduction or spectral finiteness is a premise.

## Exact analytic conclusions

`RationalCuspidalConjugationConverges` states that for every
`f₁ ∈ rationalCuspidalSubmodule hKc hPK ρ`, every actual Schwartz
function `f₂`, and every `h ∈ G(F)`, the function
`g ↦ f₁(h g h⁻¹) f₂(g)` is Bochner integrable against `muG`.
It includes absolute convergence and a.e. strong measurability.
This proposition is a conclusion in both targets, never their premise.
It strengthens the chamber-only convergence needed for VIII.3.1 to
the shared all-`h` assertion needed for VIII.3.2.

`RationalCuspidalConjugationBoundStatement` concludes
`RationalCuspidalConjugationBound`, consisting of this convergence
and the following inequality: for every such `f₁`, `f₂` and every
**real** `r`, there is a **real** `c > 0` such that

`‖B(f₁,f₂)(a)‖ ≤ c δ₀(a) (1 + σ(a))^(-r)`

for all `a : rationalMinimalChamberInNormKernel i ν`.
The pairing is the actual `rationalConjugationPairing`, with no
complex conjugation on `f₂`. The chamber is the full image of
`RenardLeviCones.componentPlus F i ν ∅ (identity S)` intersected
with `Plancherel.rationalCommonNormKernel G`. It is not restricted
to a common-uniformizer section.
The factor is exactly `rationalMinimalModulus i ν`, evaluated
through the proved `rationalMinimalChamberToParabolic`, with no
square root. The height is exactly `rationalHeight ρ`.
In relative rank zero the chamber inequalities are empty and
the imported cuspidal submodule is the whole Schwartz space;
the targets retain that case.

`RationalCuspidalConjugationIntegrabilityStatement` concludes
`RationalCuspidalConjugationIntegrability`: the same all-`h`
convergence, and `Integrable` of the actual complex
`rationalLeftConjugationPairing` on the genuine `A_G(F)\G(F)`
against `muQ`. This includes a.e. strong measurability and finite
integral of the norm. A finite lower integral alone is not used.
The totalized definition of `B` does not discharge either target.

`RationalCuspidalRightConjugationIntegrability` uses the same
convergence and the actual right quotient `G(F)/A`, with
`rightConjugationPairing` and measure
`muQ.map (normalLeftQuotientHomeomorph A)`.
`rationalCuspidalConjugationIntegrability_iff_right` proves equivalence
of the entire conclusions for explicitly displayed Borel structures on
both quotients. The proof supplies normality from split centrality
and applies `integrable_rightConjugationPairing_iff` to every pair.
Thus it transports true Bochner integrability, not merely a norm
bound. The same structural premises of the closed left target
therefore give the equivalent right formulation under this transport.

## Source comparison and remaining proof obligations

The actual kernel is imported from `RationalCuspidalSpace`.
Its membership requires integrability and zero constant term for
every proper standard root subset, every Haar measure on its actual
unipotent radical, and every two-sided translate. Its published
`mem_rationalCuspidalSubmodule_iff_constantTermInd` retains convergence.
This task does not duplicate that construction.

In VIII.2 Waldspurger recursively constructs `°f = f − κ(ψ)`.
VIII.2.1 identifies its image with vanishing of proper semistandard
induced constant terms. Comparison of the imported all-standard,
convergence-strengthened kernel with all semistandard parabolics
and with that recursive image remains unproved. The published
`RationalCuspidalVanishingComparisonStatement` is the exact
vanishing-only comparison target; its proof and the recursive
image comparison remain with Task 7252. Task 7229 owns the full
semistandard index. No assertion here applies these targets to a
recursive `°f` without first proving its membership.

The VIII.3.1 proof still needs the actual open-cell split,
proper constant-term vanishing in that split, conjugation height
and tail estimates, and the relevant constant-term and Xi bounds.
For VIII.3.2 it still needs actual I.1 (4) Cartan and (5) volume
bounds (printed p.241, PDF p.7), the central-quotient cover,
compact conjugation-orbit finiteness from smoothness, lattice-height
summability, and analytic measurability of the descended pairing.
The generic `CuspidalDecay`, `CuspidalSplit` and
`CuspidalIntegrability` reductions retain these inputs; they do
not establish the closed actual-point targets.

Existing constant-term Task 5460, rapid-decay Task 5461,
Xi upper-bound Task 5326 and split-centre height Task 5480 keep their
proof ownership. No recursive VIII.2 projection, VIII.4 finiteness,
inversion or Plancherel conclusion is proved here. The source-map
correction on printed p.325 reads VIII.2.1 where the source prints
VII.2.1; it does not supply that missing comparison.
