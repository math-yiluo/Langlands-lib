# Integral Tate lattices carried by compact Harris level orbits

Let \(X\) be a positive polarized Harris action over a quasi-separated
scheme \(S\) and choose a point \(s\) valued in a field. Use the finite
Weil transition compatibility and the rational comparison for the profinite
integer adeles from `HarrisIntegralLevelLattice`. For a Weil-compatible
frame \(\eta\) at \(s\) and a subgroup \(K\) of the finite-adelic
similitude group of the Harris source, each translate \(\eta k\) carries
the fixed integral source span into the rational Tate module.
`harrisCompactFrameLattice` intersects these integral-adele submodules
over \(k\in K\). Right translation by any element of \(K\) permutes the
terms, so `harrisCompactOrbitLattice` defines the submodule on the raw
right orbit.
When \(K\) preserves the fixed integral source span, each term is
the original `harrisIntegralFrameLattice`.

The integer commensurability bounds assume compact open \(K\), finite
fibres at \(s\) for every finite étale cover of \(S\),
`TorsionFiniteEtaleStatement`, and invertibility in \(\Gamma(S,\mathcal O_S)\)
of every positive torsion index. The intersection of \(K\) with the open
source-span stabilizer has finite index in \(K\). The proof chooses
representatives of its left cosets and applies
`harrisIntegralFrameLattice_integerBounds` to the translated frames.
The product of their positive integer bounds works for the full
intersection. It carries the full integral image into every term, and
it carries the intersection into the integral image using the bound
from one term.

The statements about the original fixed-orbit level tower use the same
point and torsion hypotheses and require the roots-of-unity group schemes
at all positive indices to be finite and étale. For a fixed orbit,
geometric monodromy on the target gives the lattice of the translated
frame, term by term, and commutes with the source action. The translated
frame belongs to the same raw orbit. For a rational isomorphism with
the supplied polarization multiplier condition, the comparison also
uses `PositivePairAdditivity` for the ordered pair of polarized objects.
The resulting finite-adelic frame transport commutes with the source
action. Applying
`harrisIntegralFrameLattice_isogeny` to every translated frame gives
preservation and reflection of membership in the intersection by the
same rational Tate map.

This construction derives from the fixed-span frame lattice in
`HarrisIntegralLevelLattice`, the open stabilizer in
`HarrisIntegralSourceLevels`, and the existing integer bounds and
rational-isogeny compatibility. All lattices are submodules of the
actual rational Tate module of the original representative.
