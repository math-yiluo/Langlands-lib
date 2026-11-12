# Finite parabolic double cosets with torus-adapted representatives: proof

Author: Worker 4901.

`Langlands.GroupScheme.representedParabolicDoubleCoset` proves exactly
`Langlands.GroupScheme.RepresentedParabolicDoubleCosetStatement.{u}`, defined
in `Langlands.GroupScheme.Rational.ParabolicDoubleCosetStatement`, at the
arbitrary universe `u`. The theorem adds no hypotheses.

For every field `k`, connected reductive `G`, actual parabolics `p : P ⟶ G`
and `q : Q ⟶ G`, and rational Levis `l : M ⟶ P` and `lQ : L ⟶ Q`, it proves
both conjuncts of the statement:

1. the literal quotient `DoubleCoset.Quotient` of `rationalPoints G` by
   `(rationalPoints.map p).range` and `(rationalPoints.map q).range` is
   `Finite`;
2. every `g : rationalPoints G` has a representative `z` with the same
   `DoubleCoset.mk` class and a maximal split torus `i : T.toGrp ⟶ G` with
   factors `a ≫ l ≫ p = i` and `b ≫ lQ ≫ q ≫ (G.innerIso z).hom = i`.

## Proof

The proof is one application of the published conditional assembly
`Langlands.GroupScheme.representedParabolicDoubleCosetStatement_of_dynamic_structural_inputs`
from `Langlands.GroupScheme.Rational.ParabolicDoubleCosetAssembly`. Its six
structural premises are discharged by these published unconditional proofs,
all at universe `u`:

| Premise | Input theorem | Module |
| --- | --- | --- |
| `RationalBruhatStatement` | `Langlands.GroupScheme.rationalBruhat` | `Langlands.GroupScheme.Rational.RationalBruhatProof` |
| `GenericMinimalParabolicStatement` | `Langlands.GroupScheme.genericMinimalParabolic` | `Langlands.GroupScheme.Rational.GenericMinimalParabolicProof` |
| `MinimalParabolicConjugacyStatement` | `Langlands.GroupScheme.minimalParabolicConjugacy` | `Langlands.GroupScheme.Rational.MinimalParabolicConjugacyProof` |
| `ParabolicIntersectionCentralizerStatement` | `Langlands.GroupScheme.parabolicIntersectionCentralizer` | `Langlands.GroupScheme.Rational.ParabolicIntersectionCentralizerProof` |
| `ParabolicDynamicStatement` | `Langlands.GroupScheme.parabolicDynamic` | `Langlands.GroupScheme.Absolute.ParabolicDynamicProof` |
| `SmoothMaximalSplitTorusConjugacyStatement` | `Langlands.GroupScheme.smoothMaximalSplitTorusConjugacy` | `Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof` |

No structural proposition remains a premise of the final theorem. Its
inspection reports only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

Inside the assembly, the two conjuncts are proved as follows.

- Finiteness uses the first three inputs, through
  `finite_parabolicDoubleCosets_of_bruhat_minimal_conjugacy` in
  `ParabolicDoubleCosetFiniteness`. A generic cocharacter of a maximal split
  torus gives a minimal parabolic `P₀`. A rational conjugate of `P₀` lies in
  each of `P` and `Q` (the published `parabolicContainsMinimalStatement` and
  minimal-parabolic conjugacy). The rational Bruhat covering indexes
  `P₀(k) \ G(k) / P₀(k)` by the finite relative Weyl group. The
  conjugate-containment map is surjective onto `P(k) \ G(k) / Q(k)`, so this
  quotient is finite.
- The representative uses the last three inputs, through
  `representedParabolicDoubleCosetStatement_of_structural_inputs` in
  `ParabolicDoubleCosetRepresentatives`. The centralizer statement (Borel–Tits
  4.18) applied to `P` and `g Q g⁻¹` gives a common maximal split torus `S`.
  The dynamic and smooth-conjugacy inputs give `u ∈ P(k)` moving `S` into `M`,
  and `v ∈ Q(k)` moving `g⁻¹ S g` into `L`. With `U = p(u)` and `V = q(v)`,
  the representative is `z = U g V⁻¹`, in the double coset of `g`; the torus
  `U S U⁻¹` factors through `M` and through `z L z⁻¹`.

## Source correspondence

The finiteness clause is Borel–Tits, *Groupes réductifs* (1965), 5.20
Corollaire (printed p.102 / PDF p.49), with 4.13 b) (printed p.90 / PDF p.37)
for conjugacy of minimal parabolics; it is Renard, *Représentations des
groupes réductifs p-adiques* (2026), V.4.5 (PDF pp.125–126) over a local
field. The torus clause is derived, as explained in the statement's
Markdown. The implemented route takes the common torus from Borel–Tits 4.18
(printed p.92 / PDF p.39) and moves it into the Levi subgroups by rational
conjugacy, as in the proof of 5.15 (printed p.100 / PDF p.47). It does not
follow Renard's standard representatives `z = g⁻¹ w h` of V.4.7
(PDF pp.127–128). Both routes give the same conclusion. The proof keeps every
field and characteristic and needs no splitting, perfectness or infinitude
condition.
