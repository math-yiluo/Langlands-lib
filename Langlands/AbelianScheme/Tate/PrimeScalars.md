# Scalar compatibility of actual Tate prime-coordinate maps

This module equips the published prime-coordinate maps of actual Tate limits
with continuous semilinear structures. It uses the existing residue-ring and
p-adic actions and the canonical full and away scalar projections from
`Langlands.Global.ProfiniteIntegerPadicProjection`.

## Actual carriers and scalar projections

Fix a scheme `S`, a commutative group object `G : Grp (Over S)` with
`[IsCommMonObj G.X]`, and `T : Over S`. For a predicate `P : ℕ → Prop`,
`Integral G T P` is the published limit of actual torsion sections at
positive orders selected by `P`. Its scalar action is the existing
`fullModule` action of `Global.ProfiniteIntegerRing`, defined through the
finite residue actions. The full limit uses `P n := True`; the away limit
uses `P n := Nat.Coprime n m` and additionally has the existing action of
`Global.PrimeToProfiniteIntegerRing m`.

Let `p : ℕ` with `[Fact p.Prime]`. The target is the existing
`PrimeAdic.Integral G T p`, a module over the actual p-adic integers
`ℤ_[p]`. Its action at order `p^n` uses `PadicInt.toZModPow n`.

The full scalar map is `Global.ProfiniteIntegerRing.toPadic p`. At order
`p^n` its residue is precisely the `p^n` coordinate of the compatible
residue family. If `h : Nat.Coprime p m`, the away scalar map
`Global.PrimeToProfiniteIntegerRing.toPadic p m h` has the parallel property.
These are published canonical ring homomorphisms, not comparison hypotheses.

## Scalar laws

For `hP : ∀ n : ℕ, P (p^n)`, `toPrime_smul` proves

`toPrime G T P p hP (a • x) = toPadic p a • toPrime G T P p hP x`

for every full residue scalar `a` and selected compatible family `x`.
The implemented proof applies subtype and function extensionality. At each
exponent, it names the torsion coordinate as a value of type
`Level G T (p^n)` and its residue scalar as a value of type `ZMod (p^n)`.
The defining residue equation `toZModPow_toPadic` then identifies the two
scalar actions. No decomposition or bijectivity theorem is used.

`fullToPrime_smul` specializes this result to the full limit.
`awayToPrime_smul` uses the away scalar ring, the coprimality hypothesis,
and its published residue equation. Its proof has the same coordinate
argument. Thus the scalar acting on the target is always the specified
p-adic image of the scalar on the source.

`awayToPrime_restrictAway_smul` proves that restricting a full scalar
multiple to the away limit and reading a retained prime gives
`toPadic p a • fullToPrime G T p x`. The proof uses the existing equality
between the two coordinate restrictions and `fullToPrime_smul`. The
published scalar-ring restriction is compatible with this same projection
by `Global.PrimeToProfiniteIntegerRing.toPadic_restrict`.

`toPrimeProduct_smul` and `toAwayPrimeProduct_smul` give these laws at each
coordinate of the existing full and away products. They do not introduce
a new module structure on those products.

## Bundled maps and continuity

`toPrimeSemilinear G T P p hP` bundles the existing additive map as a
semilinear map over `Global.ProfiniteIntegerRing.toPadic p`.
`toPrimeContinuousSemilinear` adds its already proved continuity.
`fullToPrimeContinuousSemilinear` specializes to the full limit.

`awayToPrimeSemilinear G T p m h` and
`awayToPrimeContinuousSemilinear G T p m h` use the away scalar projection.
All underlying functions and additive maps are unchanged. The source
limit and target prime-adic limit retain their product-subspace topologies.
The constructors reuse `continuous_toPrime` and `continuous_awayToPrime`.
The existing homomorphism naturality equations in `PrimeComparison` apply
to these same functions.

In namespace `Langlands.AbelianScheme.Tate.PrimeComparison`, the
abbreviations `toPrimeContinuousSemilinear`,
`fullToPrimeContinuousSemilinear`, and `awayToPrimeContinuousSemilinear`
specialize the constructions to the actual geometric abelian scheme
`A.toGrp`. These use the published `Integral A T P`, `Full A T`,
`Away A T m`, and `PrimeAdic.Integral A T p` carriers.

## Provenance and limits

Harris and Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), Chapter I, printed p.18 (PDF p.26), supplies the full,
away, and at-prime torsion-limit conventions. Registered source:
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

The scalar compatibility and continuous semilinear packaging here are
derived infrastructure for those conventions. Their proof is the finite
residue calculation described above. Arbitrary commutative group schemes,
test schemes, and selected predicates are explicit generalizations.
Worker 92 supplied the published canonical scalar projections and
coordinated the parallel root-twist API; this module concerns the actual
group-scheme Tate limits.

There are no finiteness, rank, or characteristic hypotheses because these
are coordinate scalar laws. No finite étaleness, profiniteness, product
equivalence, rational restricted-product comparison, monodromy or Weil
pairing is asserted by this unit.
