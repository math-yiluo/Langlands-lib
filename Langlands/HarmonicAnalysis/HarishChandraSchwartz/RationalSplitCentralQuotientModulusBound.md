# Dominant-ray volume bounds in the actual split-central quotient

This internal auxiliary construction for Task 7500 proves an inverse-modulus
upper bound for compact cells along the dominant common-uniformizer lattice.
It retains the supplied compatible measure on the actual split-central left
quotient and allows the compact open subgroup `K` to differ from the structural
subgroup `K0` carrying the simultaneous basis.

The source motivation is Waldspurger, *La formule de Plancherel pour les groupes
p-adiques* (2003), registered as `waldspurger-2003-plancherel`, Corollary VIII.3.2,
printed pp.326–327 (PDF pp.92–93). The cell-volume step on p.327 uses I.1 (5),
printed p.241 (PDF p.7), which compares double-coset volumes with `δ₀(a)⁻¹`.
The implementation here is an internal derivation from the already published
standard-basis ray-index theorem and the compatible-quotient finite-index
volume bound. The bound applies to the individual cells at all dominant
uniformizer powers.

The field is any nonarchimedean local field in arbitrary universe `u`. The
group scheme is affine and locally of finite type, `i : S.toGrp ⟶ G` is a
maximal split torus, and `ν` is the cocharacter indexing the actual standard
parabolic subgroups and simple relative roots. The hypotheses include
`SimultaneousStandardBasisAt i ν K0` for a specified structural subgroup `K0`.
The supplied `K` is an arbitrary compact open subgroup of the actual group of
rational points.

`exists_doubleCosetIndex_uniformizerPowers_le_inverse_modulus` proves that
there is a positive real `D` with

`index(K, ϖ^y) ≤ D * δ₀(ϖ^y)⁻¹`

for every cocharacter `y` whose simple-root pairings are nonnegative. The
actual minimal-parabolic membership proof `hyP` is displayed so that the
modulus is evaluated on its published domain. The basis is a neighborhood
basis of compact open subgroups in the whole group. Choose one member `L`
contained in `K`, using the open neighborhood `K` of the identity. Its
simultaneous parabolic property gives
`index(L, ϖ^y) ≤ δ₀(ϖ^y)⁻¹` by
`Aubert.General.standardBasisMember_rayIndex`. The ray lies in the center of
the actual minimal Levi; the proof constructs that center element and uses
`Jacquet.closedRestrictCharacter_congr` to identify its closed-unipotent Haar
modulus with `rationalMinimalModulus`. Compactness of `K` and openness of `L`
make `[K:L]` finite. The published `doubleCosetIndex_le` then gives the claimed
bound with `D = [K:L]`, which is strictly positive. The argument applies also
when the set of simple roots is empty.

`RationalSplitCentralCellModulusBound i ν s muQ K Y` states that there is a
positive real `C` such that

`muQ (q '' (K * {ϖ^y} * Y)) ≤ ENNReal.ofReal (C * δ₀(ϖ^y)⁻¹)`

for all dominant `y`, with membership in the minimal parabolic displayed
for evaluation of the modulus. Here `q` is the same-representative map to
`LeftQuotient (rationalPoints.map s).range`.

`exists_rationalSplitCentralQuotient_measure_compact_cell_le_inverse_modulus`
proves this proposition for compact `Y` and an actual split component
`s : T.toGrp ⟶ G`, with the displayed Borel structures on its rational-point
image and left quotient. It takes a left-invariant `muG`, a right-invariant
central Haar measure `muA`, and the compatible measure `muQ`. It composes
the real index bound with
`exists_rationalSplitCentralQuotient_measure_compact_cell_le_index`,
multiplies their positive constants, and applies monotonicity of
`ENNReal.ofReal`. The imported finite-index bound derives central Haar
regularity from the actual point topology and estimates the outer measure
of each cell for that same `muQ`.
