# Fixed-coefficient finiteness on actual rational points

Worker 3642, Task 3642, revision 1.

Module `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalFixedCoefficientFiniteness`,
namespace `Langlands.HarishChandraSchwartz`.

## Mathematical meaning

For a topological group `G`, a normal central subgroup `A`, and a Haar measure `mu`
on `G/A`, the existing `discreteSeriesCentralFixed A hA mu χ H` is the set of
irreducible discrete-series classes with central character `χ` on `A` and a nonzero
`H`-fixed vector. The new submodule
`discreteSeriesCentralFixedCoefficientSpace A hA mu χ H` is the complex linear span
of their `H`-bi-invariant coefficient functions. It uses the canonical `SmoothRep`
coefficient spaces and the same chosen representatives `ω.val.out.obj` as the
published finiteness reduction.

`RationalFixedCoefficientFinitenessStatement.{u,uV}` says that this concrete span
is finite dimensional for every nonarchimedean local field `F`, affine locally
finite type connected reductive group scheme `G/F`, split component `s : T → G`,
Haar measure `mu` on `G(F)/A_G(F)`, compact open subgroup `H` of `G(F)`, and
continuous unitary character `χ` of `A_G(F)` trivial on `A_G(F) ∩ H`.
Here `A_G(F)` is the image of `T(F)`. The topology is the canonical rational-point
topology, and the quotient has its Borel measurable structure. The field universe
`u` and representation-carrier universe `uV` are independent. Positive
characteristic, nonsplit groups and non-quasisplit groups are retained.

This is an unproved analytic target. It has no supplied finite-dimensional
container, coefficient bound, spectral-finiteness assumption, cuspidal projection,
or induction hypothesis. The generic definition does not identify its span with
the full projected cuspidal Schwartz space.

## Source and provenance

The statement is an internal derived target for the final coefficient-space
argument of J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques,
d'après Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333,
DOI 10.1017/S1474748003000082. Registered source
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
Printed page numbers equal PDF page numbers plus 234.

The relevant passages are Proposition VIII.4.1, printed pp.327–330
(PDF pp.93–96), Theorem VIII.4.2, printed pp.330–331 (PDF pp.96–97), and
VIII.5, printed pp.331–332 (PDF pp.97–98), proving Theorem VIII.1.2.
Waldspurger places the fixed coefficients in the finite-dimensional space
`p_χ(°C_H)` and uses independence and nonvanishing of the coefficient spaces.
The present span is the least submodule containing just the coefficients needed
by that argument. The source's conclusion that they lie in `p_χ(°C_H)` therefore
implies its finite dimensionality. Neither the projected cuspidal space nor that
inclusion is constructed or proved here.

The source map's correction of the reference to Corollary III.3.2 on printed
p.330 applies to the prospective analytic proof: the convergence result is
Corollary VIII.3.2. None of the elementary span arguments here uses that
corollary.

## Implemented constructions and proofs

The module imports
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalDiscreteSeriesOrbitFinitenessStatement`.
Through it come the actual discrete-series classes, coefficient spaces, central
characters and the proved generic and rational-point finiteness reductions.

- `mem_discreteSeriesCentralFixedCoefficientSpace` puts each defining coefficient
  into the span by `Submodule.subset_span`.
- `discreteSeriesCentralFixedCoefficientSpace_le_iff` characterizes containment
  in another submodule by containment of each generating coefficient, using
  `Submodule.span_le`.
- `finiteDimensional_discreteSeriesCentralFixedCoefficientSpace_iff` identifies
  finite dimensionality with the existence of exactly the finite-dimensional
  container required by the published VIII.5 reduction. One direction chooses
  the span itself; the other uses the preceding containment criterion and
  `Submodule.finiteDimensional_of_le`.
- `RationalFixedCoefficientFinitenessStatement.orbitFiniteness` constructs an
  `OpenSubgroup` from a subgroup and its openness, applies the target at each
  allowed `χ`, converts it to the container formulation, and invokes
  `finite_rationalDiscreteSeriesFixedOrbits_of_finiteDimensional`. It proves an
  implication from this new target to the existing exact
  `RationalDiscreteSeriesOrbitFinitenessStatement`, with the same universes.

Only these span and assembly arguments are proved. The new target itself,
VIII.4.1 and VIII.4.2 on actual rational points, VIII.1.2, full semistandard
spectral support, and Plancherel inversion remain open.
