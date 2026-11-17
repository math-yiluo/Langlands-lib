# The full minimal-torus chamber

This internal realization uses the published
`Langlands.BruhatTits.Cartan.RenardLeviCones.componentPlus`. Its source
meaning is Waldspurger (2003), I.1, printed pp.239–240 (PDF pp.5–6),
and the chamber in Proposition VIII.3.1, printed p.323 (PDF p.89).
The registered primary source is `waldspurger-2003-plancherel`.

For an affine group scheme over an arbitrary nonarchimedean local field,
a commutative torus carrier `S`, a map `i : S → G` and a cocharacter `ν`,
`rationalMinimalChamber i ν` is exactly the image under
`rationalPoints.map i` of `componentPlus F i ν ∅ (𝟙 S)`. In the analytic
applications `i` is a maximal split torus of a connected reductive group
and `ν` is generic. The construction and elementary laws need no extra
reductivity or genericity premises. The word closed refers to the weak
root inequalities. There is no restriction to uniformizer powers.

The norm membership formula quantifies every simple relative root and
requires its normalized norm at a torus representative to be at most one.
`restrictedSimpleCharacters_minimal` identifies these exact characters.
The order formula uses the published `mem_componentPlus_iff_order`:
every root character has nonnegative integral `characterOrder`. The
published relation `characterNorm_eq_rpow` is
`|α(a)| = q^(-characterOrder S α a)`. Thus this uses precisely the positive
valuation convention of source I.1, which explicitly places a minus sign
in the exponent of `q`.

`mem_rationalMinimalChamber_iff_dominant` gives the comparison with the
published positive centralizer valuation, for any displayed algebraic
map `s : S → Z` with bijective real character-restriction evaluation and
`IsSplitTorus S.toGrp`. A group point is in our chamber exactly when it
has a torus representative whose image in `Z(F)` lies in the existing
`dominantCentralizer`. The proof composes `map_mem_leviPlus_iff` and
`leviPlus_minimal`; in particular it constructs no competing valuation.
When `Z` represents the minimal Levi and `s` its split component, this is
the source equality `Ā₀⁺ = H₀⁻¹(ā₀⁺) ∩ A₀`. The displayed map and
restriction-bijection premises are retained, rather than silently
asserting a represented-Levi identification for an arbitrary `Z`.

The torus image centralizes itself. The proof passes through the actual
torus centralizer, standard Levi and standard parabolic subgroup
functors to place every chamber point in `standardParabolicPoints i ν ∅`.
`rationalMinimalChamberInNormKernel` intersects this full ambient set with
`Langlands.Plancherel.rationalCommonNormKernel G`, the actual `G¹` defined
using every rational character of `G`. Its canonical map
`rationalMinimalChamberToParabolic` supplies the point where the existing
`rationalMinimalModulus i ν` can be evaluated. No arbitrary subgroup or
weight replaces these objects. In relative rank zero the chamber equals
the entire torus image, as proved by the empty-simple-root theorem.

The lattice comparison uses the same maximal torus with identity
inclusion, so no separate split component or unproved factorization is
introduced. The proof explicitly identifies
`componentCharacterRestriction (𝟙 S.toGrp)` with the identity and the
published `standardParabolicComponentCharacters` with the same simple
roots. It then identifies `standardComponentCAplus i ν ∅ (𝟙 S.toGrp)`
with the image of `CA F S ∩ componentPlus F i ν ∅ (𝟙 S)` and proves its
inclusion into the full ambient chamber. This is exactly the lattice cut
expressed by published `CAplus_eq_inter`. It does not identify the full
chamber with that section. Comparisons for other component maps would
need their actual algebraic character-restriction identifications; none
are needed or asserted here.

These are constructions and elementary comparison laws, not Cartan,
cell-volume, summability or conjugation-decay proofs. The source I.1
(4)–(5), printed p.241 (PDF p.7), and the proof of VIII.3.2 require those
additional results. All field characteristics, nonsplit and
non-quasi-split cases and relative rank zero remain within scope.
