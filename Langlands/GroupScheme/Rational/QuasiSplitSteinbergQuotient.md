# Steinberg's class quotient of a simply connected quasi-split group

This module proves the published proposition
`Langlands.GroupScheme.QuasiSplitSteinbergQuotientStatement.{u}`
(module `Rational/QuasiSplitSteinbergQuotientStatement`) as the closing theorem

```lean
theorem quasiSplitSteinbergQuotient : QuasiSplitSteinbergQuotientStatement.{u}
```

The statement pair and every pair it imports are unchanged. The universe `u` and the fields `K`
and `F` stay arbitrary. Finite fields and imperfect fields of positive characteristic are allowed,
and no hypothesis on `K`, `F`, `G`, `v`, `y`, `w`, `S` or `j` is added.

## Declarations

- `quasiSplitSteinbergQuotient_of_rationalLifting
  (hlift : ClassFunctions.StronglyRegularRationalLiftingStatement.{u}) :
  QuasiSplitSteinbergQuotientStatement.{u}`: the assembly of the three properties for the
  canonical class-function quotient, with property 3 supplied as the hypothesis `hlift`.
- `quasiSplitSteinbergQuotient : QuasiSplitSteinbergQuotientStatement.{u}`: the closing theorem.
  It applies the assembly to the published proof
  `Langlands.GroupScheme.ClassFunctions.stronglyRegularRationalLifting :
  ClassFunctions.StronglyRegularRationalLiftingStatement.{u}`
  (module `Rational/ClassFunctionsRationalLifting`). So the closing theorem has no hypotheses and takes no
  unproved Library statement as a premise. In particular it does not use
  `QuasiSplitRegularClassRationalStatement` or any other form of Borel–Springer 8.6 as a premise.

## Proof

Let `K` be a field and `G` a simply connected quasi-split group over `Spec K`. Quasi-splitness
gives `IsAffineHom G.X.hom` (`hqs.isConnectedReductive.isAffineHom`), and this instance makes the
canonical class-function quotient available. The witnesses are `V := ClassFunctions.quotient G`,
the relative spectrum of the subalgebra of conjugation-invariant regular functions, and
`ρ := ClassFunctions.rho G` (module `Rational/ClassFunctions`). Each of the three properties is a
direct application of a published result to the same data:

1. Invariance under conjugation is the published `ClassFunctions.rho_conjugation G g x`
   (`Rational/ClassFunctions`).
2. Strongly regular fibres are geometric conjugacy classes. This is the published
   `ClassFunctions.stronglyRegularFibres : ClassFunctions.StronglyRegularFibresStatement.{u}`
   (module `Rational/ClassFunctionsStronglyRegularFibres`), applied to
   `K G hsc hqs F y w S j hS hj hc hyw`.
3. Rational lifting is the published
   `ClassFunctions.stronglyRegularRationalLifting :
   ClassFunctions.StronglyRegularRationalLiftingStatement.{u}`, applied to
   `K G hsc hqs v F w S j hS hj hc hv`.

The published statements `StronglyRegularFibresStatement` and
`StronglyRegularRationalLiftingStatement` are exactly properties 2 and 3 of the target with `V` and
`ρ` fixed to the canonical quotient and the same affineness instance. So each property is closed by
`exact`.

Neither this module nor its Markdown asserts a global `K`-rational section of `ρ`. The published
proof of property 3 chooses the lift point by point when `G` has a simple component of type `A_n`
with `n` even (see `Rational/ClassFunctionsRationalLifting.md`).

## Prerequisites

Property 3 rests on the proof of `StronglyRegularRationalLiftingStatement` (module
`Rational/ClassFunctionsRationalLifting`). That proof uses
`Langlands.GroupScheme.splitEvenChainCrossSection` (module `Rational/EvenChainCrossSection`) and
`Langlands.GroupScheme.evenChainGaloisData` (module `Rational/EvenChainGaloisData`).

## Sources

- R. Steinberg, *Regular elements of semi-simple algebraic groups*, Publ. Math. IHÉS 25 (1965),
  source `steinberg-1965-regular-elements-semisimple-groups`, SHA-256
  `bda20c4a4b3cf4a7e9e5b17a4eacd0147d0c9370063ab3a3778114a53c8349b9` (PDF page = printed page
  − 47). Properties 1 and 2 correspond to 6.5, 6.6 and 6.10 (printed pp.63–64). Property 3
  corresponds to 7.9 (p.68), 9.2–9.4 (pp.72–73) and 9.10–9.19 (pp.74–77): the cross-section `N`
  and, for type `A_n` with `n` even, the substitutes `N''` and `N'''`.
- A. Borel and T. A. Springer, *Rationality properties of linear algebraic groups II*,
  Tôhoku Math. J. 20 (1968), source `borel-springer-1968-rationality-properties-ii`, SHA-256
  `e465d0622ca9540ff21e0d53d7b2fdb00a14cf70a7caceee352c040a3cb1abef` (PDF page = printed page
  − 442), 8.2 (finite Galois splitting fields, printed pp.481–482) and 8.6 (printed pp.483–484),
  which extends Steinberg's argument to arbitrary fields. 8.6 is cited for provenance only and is
  not used as a premise.

The implemented route differs from the literature in two ways. First, `V` is the spectrum of the
conjugation-invariant functions rather than an affine space with Steinberg's fundamental
characters as coordinates. Second, the published proof of property 3 uses point-level descent from
a finite Galois splitting field rather than the statement that the cross-section variety is
defined over `K`. This module only assembles those published results.
