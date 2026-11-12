# Proof of the local normalized orbit comparison for represented parabolics

This module proves the published proposition
`Langlands.Aubert.General.RepresentedParabolic.RepresentedGeometricLemmaOrbitComparisonStatement.{u,v}`
(module `Langlands.Representation.Geometric.RepresentedGeometricLemmaOrbitComparisonStatement`).
The theorem is `representedGeometricLemmaOrbitComparison`. Its type is exactly that closed proposition, with independent universes `u` (field and group schemes) and `v` (carriers of the source representations). It adds no hypotheses.

## Source

This is the local step of the geometric lemma of Renard, *Représentations des groupes réductifs p-adiques* (French version dated 9 July 2026, literature ID `renard-2026-representations-groupes-reductifs-padiques`). That step consists of the coinvariant–compact-induction isomorphism VI.5.1.3 (printed p.167 / PDF p.173) and the stabilizer comparison and cancellation of the residual modular characters (printed pp.171–172 / PDF pp.177–178). The Lean proof does not follow Renard's text line by line. It assembles natural isomorphisms already published in the Library, which formalize those steps with the Library's half-Haar normalizations. This module discharges the structural inputs those isomorphisms carry.

## What is proved

Fix a nonarchimedean local field `k`, a connected reductive `G` over `k` with the canonical topology on `G(k)`, and two arbitrary represented parabolic triples `(P, M, N)` and `(Q, L, U)`. Fix a rational point `z` and a full `GeometricLemmaIntersectionDatum D` at `z`. Then there is a natural isomorphism, on the category of all smooth complex representations of `M(k)`, between:

```text
smoothLeviInducingFunctor ⋙ Geometric.orbitPiece P(k) Q(k) z⁻¹ ⋙ leviParabolicCoinvariantsFunctor
```

and `D.pieceFunctor`.

## The implemented proof

The proof chains three published natural isomorphisms:

```text
orbitParabolicProjectionKernelIso p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z
  ≪≫ R.orbitProjectionKernelCompactIso
  ≪≫ DynamicRealization.targetNormalizedCompactIso D R hcompact hroot hinj
```

1. `orbitParabolicProjectionKernelIso` (module `RepresentedParabolicKernelCoinvariants`) identifies the left functor of the statement with `orbitProjectionKernelCoinvariantsFunctor`. That functor takes the twisted stabilizer coefficient, applies compact induction from the orbit stabilizer `Q(k) ∩ z⁻¹ P(k) z`, and then takes coinvariants by the kernel of the projection to the target Levi.
2. `R.orbitProjectionKernelCompactIso` (module `RepresentedGeometricLemmaCompactNaturality`) identifies that functor with `D.targetNormalizedCompactFunctor`. This is compact induction of the normalized target-intersection coefficient, followed by restriction to `L(k)`. The step uses the compact quotient-integral comparison and the cancellation of the distinct radical Haar moduli recorded in the Library.
3. `targetNormalizedCompactIso` (module `RepresentedGeometricLemmaTargetInduction`) identifies `D.targetNormalizedCompactFunctor` with the datum's original Jacquet–conjugation–induction piece `D.pieceFunctor`.

Each of these isomorphisms is natural on the full smooth source category, so their composite is too. The composite is packaged with `Nonempty`, as the statement requires.

## Discharging the structural inputs

Steps 2 and 3 take four structural inputs. The proof constructs each of them from the given data and published unconditional theorems:

- **Simultaneous dynamic realization** `R : D.DynamicRealization`. This is a common cocharacter description of the target triple and of the source triple conjugated by `z⁻¹`, inside the datum's common torus. It is `D.dynamicRealizationOfParabolicDynamic parabolicDynamic hG`, with `parabolicDynamic` the published proof of `ParabolicDynamicStatement`.
- **Compactness** of the quotient `pointImage D.q' \ L(k)`. The target intersection parabolic `D.q'` is a parabolic subgroup of the connected reductive target Levi `L`. So this is `arbitraryParabolicQuotientCompact` (published proof of `ArbitraryParabolicQuotientCompactStatement`) applied to `L`. The topology on `L(k)` is the canonical Levi point topology `leviPointTopology lQ hlQ`. Its local compactness and nonarchimedean instances come from `leviPoints_locallyCompactSpace` and `leviPoints_nonarchimedeanGroup`.
- **Relative root system** for the common torus transported into `G`. This is `relativeRootSystem` (published proof of `RelativeRootSystemStatement`), applied to the datum's ambient maximal split torus law `D.targetCommonTorus_isMaximalSplitTorus_ambient`.
- **Injectivity of character restriction** from the target common Levi `D.L'` to its common torus `D.targetCommonTorusHom`. This is the new lemma `GeometricLemmaIntersectionDatum.characterRestrict_targetCommonTorusHom_injective`, proved in this module.

### The new lemma

`characterRestrict_targetCommonTorusHom_injective D` states that `characterRestrict D.targetCommonTorusHom` is injective on rational characters of `D.L'`. The proof:

- `D.L'` is connected reductive because it is a rational Levi subgroup (`D.hlQ'.isConnectedReductive`).
- The composite embedding `D.lQ' ≫ D.q' ≫ lQ ≫ q` of `D.L'` into `G` is a closed subgroup, as a composite of closed subgroups.
- The common torus followed by this embedding is a maximal split torus of `G`. This is the datum field `targetCommonTorus_isMaximalSplitTorus_ambient`.

Take a character `χ ≠ 0` of `D.L'` whose restriction to the common torus vanishes. The published `centralSplitTorusCharacter` gives a central split torus `a : A ⟶ D.L'` on which `χ` restricts nontrivially. By `IsCentralSplitTorus.exists_factor_of_isMaximalSplitTorus`, the torus `a` factors as `g ≫ D.targetCommonTorusHom`. Then `characterRestrict a χ = characterRestrict g (characterRestrict D.targetCommonTorusHom χ) = 0`, a contradiction. Hence the kernel is zero.

## Scope

The theorem assumes no admissibility, finite length, irreducibility, standardness of the parabolics, supplied filtration, chosen root presentation, modulus equality or supplied orbit-comparison isomorphism. The point `z` and the full datum `D` are premises of the published local proposition itself, and all their fields are kept. The full represented geometric lemma and the support-graded comparison are not used. The proof needs no lemma beyond the published Library and the character-restriction lemma above.

Axioms: `propext`, `Classical.choice`, `Quot.sound`.
