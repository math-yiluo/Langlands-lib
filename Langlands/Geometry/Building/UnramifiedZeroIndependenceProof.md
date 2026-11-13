# Independence of `H(K)^0` from its defining data — proof

`Langlands.Geometry.Building.unramifiedZeroPointsIndependence` proves the published
statement `Langlands.Geometry.Building.UnramifiedZeroPointsIndependenceStatement.{u}`
(module `Langlands.Geometry.Building.UnramifiedZeroIndependenceStatement`) at an
arbitrary universe `u`. That statement is the independence part of Kaletha–Prasad,
Lemma 2.6.24, for Definition 2.6.23(1): over `K = UnramifiedClosure F`, any two
`UnramifiedZeroDatum F H` give the same subgroup `H(K)^♮ ⊔ T(K)^0` of `H(K)`. The proof
adds no hypothesis. It uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Declarations

* `unramifiedZeroPointsIndependence_of_henselianDiscrete` derives the target from
  `Langlands.GroupScheme.HenselianDiscreteQuasiSplitStatement.{u}`: every connected
  reductive group over a Henselian discretely valued field with algebraically closed
  residue field is quasi-split (KP Theorem 2.3.3(2) and Corollary 2.3.8).
* `unramifiedZeroPointsIndependence_of_steinbergQuotient` derives the target from
  `Langlands.GroupScheme.QuasiSplitSteinbergQuotientStatement.{u}`, Steinberg's class
  quotient for simply connected quasi-split groups.
* `unramifiedZeroPointsIndependence` is the final theorem. It applies the second
  declaration to the published proof `Langlands.GroupScheme.quasiSplitSteinbergQuotient`.

## Proof route

All the steps are published Library results; this file only composes them.

1. `Langlands.GroupScheme.quasiSplitSteinbergQuotient` proves Steinberg's class quotient
   (Steinberg 1965; Borel–Springer 1968, 8.2).
2. `quasiSplitRegularClassRationalReduction` turns it into
   `QuasiSplitRegularClassRationalStatement`: in a simply connected quasi-split group, a
   Galois-stable strongly regular conjugacy class has a rational point (Steinberg 1.7,
   as extended by Borel–Springer 8.6).
3. `henselianDiscreteQuasiSplitReduction` turns that into
   `HenselianDiscreteQuasiSplitStatement`.
4. `unramifiedQuasiSplit_of_henselianDiscrete` specializes Henselian quasi-splitness to
   `UnramifiedQuasiSplitStatement` for the actual `UnramifiedClosure F`.
5. `unramifiedSharpTorusConjugacy_of_structure` gives
   `UnramifiedSharpTorusConjugacyStatement`: any two maximally split maximal tori of `H`
   are conjugate under `H(K)^♮`. It takes four inputs:
   * `Langlands.GroupScheme.maximalSplitTorusConjugacy`, the conjugacy of maximal split
     tori (Borel–Tits 4.21);
   * `Langlands.GroupScheme.simplyConnectedCentralizerProduct`, KP Fact 2.6.22
     (`G(k) = G(k)^♮ · Z_G(S)(k)`);
   * `Langlands.GroupScheme.quasiSplitMaximalTorusCentralizer`: in a quasi-split group,
     a maximal torus that contains a maximal split torus `S` represents `Z_G(S)`;
   * the result of step 4.
6. `unramifiedZeroPointsIndependence_of_sharpConjugacy` turns sharp conjugacy into the
   target. Sharp conjugacy, applied to the two data's tori, gives a point of the first
   datum's `H(K)^♮` and an isomorphism between the two torus presentations compatible
   with conjugation by that point. Then `UnramifiedZeroDatum.torusIwahori_map_eq_of_iso`
   matches the two torus norm subgroups, which may use different splitting fields. Finally
   `zeroPoints_eq_of_sharp_torus_iso` gives equality of the two zero subgroups, which may
   also use different simply connected covers.

This follows the proof of KP Lemma 2.6.24, which uses conjugacy of minimal Levi
subgroups under `G_sc(k)`, together with Lemma 2.5.12 and Fact 2.6.21. There is one
difference. KP states Definition 2.6.23 for quasi-split `H` and relies on KP Corollary
2.3.8 (every group over `K` is quasi-split), whereas the Library datum asks only for a
maximally split maximal torus. Steps 1–4 supply that quasi-splitness. Step 5 needs it to
identify a maximally split maximal torus with the centralizer of a maximal split torus.

## Sources

- Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Lemma 2.6.24 and
  Definition 2.6.23, printed pp.104–105/PDF pp.135–136; Corollary 2.3.8. Registered as
  `kaletha-prasad-2023-bruhat-tits-new-approach`.
