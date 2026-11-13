# Proof: rational lifting of values of the canonical class quotient

Task `dae9b3ff-3319-4226-a421-ef1462af985a` (Task 5324). Design by Worker 175 (previous instance);
maintained by Worker 5324.

This module proves `Langlands.GroupScheme.ClassFunctions.StronglyRegularRationalLiftingStatement.{u}`
(module `Rational/ClassFunctionsRationalLiftingStatement`) as the closing theorem
`Langlands.GroupScheme.ClassFunctions.stronglyRegularRationalLifting`. The proof shows more than the
statement asks: for a simply connected quasi-split group `G` over an arbitrary field `k`, every
rational point `v` of the canonical quotient `ClassFunctions.quotient G` is `x ≫ ClassFunctions.rho G`
for a rational point `x` of `G`. The strongly regular data `F`, `w`, `S`, `j` and the hypothesis
relating `w` to `v` are not used.

No global rational section of `ClassFunctions.rho G` is constructed or asserted. When `G` has a simple
component of type `A_n` with `n` even, the lift is chosen point by point. For each point it comes from
one of several pattern products, and the choice depends on `v`.

## Declarations

- `RationalLifting.pullbackPoint X y`: the base change to `L` of a rational point `y` of an object
  `X` over `Spec k`, as a rational point of `(Over.pullback (algebraBaseMap k L)).obj X`.
  `point_ext` says that such a rational point is determined by its projection to `X`.
  `pullbackPoint_fst` and `map_left_fst` are the corresponding projection identities.
- `RationalLifting.quotientPoint k L G v`: the `L`-rational point of `quotient G_L` obtained from `v`.
  It is `pullbackPoint v` followed by the published comparison isomorphism
  `ClassFunctions.BaseChange.quotientComparison k L G`
  (`Rational/ClassFunctionsBaseChange`).
- `rho_eq_quotientPoint_iff`: a rational point `g` of `G_L` satisfies
  `g ≫ rho G_L = quotientPoint v` exactly when the `L`-point `baseChangeBasePointsEquiv g` of `G`
  satisfies `… ≫ rho G = toUnit _ ≫ v`. The proof rewrites with the published compatibility
  `BaseChange.quotientComparison_rho`, cancels the isomorphism, and compares projections.
- `rationalConjugate_rho_eq`: for `L/k` finite Galois, Galois conjugation
  `GaloisPointComparison.rationalConjugate k L G σ` (`GaloisPointRational`) preserves the
  condition `g ≫ rho G_L = quotientPoint v`. The published `baseChangeCoeffEquiv_rationalConjugate`
  shows that conjugation precomposes the `L`-point of `G` with `Spec σ`, and `v` is defined over `k`.
- `rho_eq_of_baseChangeBasePoint`: if the base change of a rational point `x` of `G` maps to
  `quotientPoint v`, then `x ≫ rho G = v`. Here `Spec L → Spec k` is an epimorphism: it is flat and
  surjective (`fieldExtension_fpqc`, Mathlib's `Flat.epi_of_flat_of_surjective`).
- `stronglyRegularRationalLifting_of_evenChain (hCS : SplitEvenChainCrossSectionStatement.{u})
  (hGal : EvenChainGaloisDataStatement.{u}) : StronglyRegularRationalLiftingStatement.{u}`: the
  descent argument below, with both statements as explicit hypotheses.
- `stronglyRegularRationalLifting : StronglyRegularRationalLiftingStatement.{u}`: the closing
  theorem. It is `stronglyRegularRationalLifting_of_evenChain` applied to two published proofs:
  `Langlands.GroupScheme.splitEvenChainCrossSection : SplitEvenChainCrossSectionStatement.{u}`
  (module `Rational/EvenChainCrossSection`, Task 5373, `95361554-92ac-4439-beef-d85479cec26e`) and
  `Langlands.GroupScheme.evenChainGaloisData : EvenChainGaloisDataStatement.{u}`
  (module `Rational/EvenChainGaloisData`, Task 5375, `d652a852-c752-406a-8eff-a02a2a321395`).
  So the closing theorem takes no unproved statement as a premise. It does not use
  `QuasiSplitRegularClassRationalStatement`, `QuasiSplitSteinbergQuotientStatement` or any form
  of Borel–Springer 8.6.

## Proof of `stronglyRegularRationalLifting`

Let `G` over `k` be simply connected and quasi-split, and let `v` be a rational point of the quotient.
Steps 2 and 3 use the two published proofs `evenChainGaloisData` (`hGal`) and
`splitEvenChainCrossSection` (`hCS`); the rest is `stronglyRegularRationalLifting_of_evenChain`.

1. The published `IsQuasiSplit.exists_pairingCompatiblePinningData` (`Rational/QuasiSplitPinningOrbitPairs`)
   is applied to the published proofs `parabolicDynamic` and `rootDatumExistence`. It gives a finite
   Galois extension `L/k` and `D : PairingCompatiblePinningData k L G`. This includes a split pinning
   `D.pinning` of `G_L`, normalized simple-root maps `D.rootMaps`, and their Galois compatibility.
   Borel–Springer 8.2–8.3 supply such a finite Galois splitting field over an arbitrary field, with
   no perfectness assumption.
2. `hGal k L G D` gives even-path data `C`, orderings `o`, `e` with `e` middle-out, and the pattern set
   `P = C.patternSet D.rootMaps (canonicalSimpleReflectionRepresentatives D.rootMaps) o e` of rational
   points of `G_L`. Every `rationalConjugate σ` maps `P` into itself.
3. `G_L` is simply connected by the published `isSimplyConnectedFieldExtension`. `hCS` therefore gives
   exactly one `g ∈ P` with `g ≫ rho G_L = quotientPoint v`.
4. For each `σ`, the conjugate `rationalConjugate σ g` lies in `P` (step 2) and has the same image
   (`rationalConjugate_rho_eq`). By uniqueness it equals `g`.
5. The published `rationalPointOfGaloisFixed` (`SubgroupConjugacyDescent`) descends the Galois-fixed `g` to
   a rational point `x` of `G` whose base change is `g`
   (`baseChangeBasePoint_rationalPointOfGaloisFixed`). This needs `G.X.left` affine, which follows
   from the affine structure morphism. `rho_eq_of_baseChangeBasePoint` then gives `x ≫ rho G = v`.

## Sources

- R. Steinberg, *Regular elements of semi-simple algebraic groups*, Publ. Math. IHÉS 25 (1965),
  source `steinberg-1965-regular-elements-semisimple-groups`, SHA-256
  `bda20c4a4b3cf4a7e9e5b17a4eacd0147d0c9370063ab3a3778114a53c8349b9` (PDF page = printed page − 47).
  Theorem 1.7 = 9.8 (printed pp.51, 73): for `G` simply connected with a Borel subgroup over `k`,
  every semisimple class over `k` contains an element over `k`. Points of the quotient correspond
  to semisimple classes (6.10). The theorem follows from 9.4 (the product `N` is over `k` when no
  component has type `A_n`, `n` even) and from 9.7 e) with 9.11–9.19 (the substitutes `N''` and
  `N'''` for components of type `A_n`, `n` even, each over `k`). Steinberg assumes `k` perfect
  (p.51). Here every rational point is instead descended from a finite Galois splitting field.
- A. Borel and T. A. Springer, *Rationality properties of linear algebraic groups II*, Tôhoku Math. J.
  20 (1968), source `borel-springer-1968-rationality-properties-ii`, SHA-256
  `e465d0622ca9540ff21e0d53d7b2fdb00a14cf70a7caceee352c040a3cb1abef`, 8.2–8.3 (finite Galois
  splitting fields) and 8.6 (rational regular classes over arbitrary fields). Their 8.6 is the
  arbitrary-field form of the result proved here. It is not used as a premise.

The point-level Galois descent through a Galois-stable set with unique preimages is a derived
formalization route. Steinberg instead shows that the cross-section variety is defined over the field.
