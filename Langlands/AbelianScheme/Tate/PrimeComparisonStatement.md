# Exact prime-product comparison statements for actual Tate limits

This file states, without proving, that the published canonical prime-coordinate
maps of actual torsion-section limits are topological additive equivalences.
The three declarations in each namespace return `Prop`. Their truth remains a
separate proof obligation.

## Carriers and hypotheses

Fix a scheme `S`, a commutative group object `G : Grp (Over S)` with
`[IsCommMonObj G.X]`, and a test scheme `T : Over S`. The published
`GroupScheme.Tate.Level G T n` is the additive group of sections annihilated by
the actual multiplication morphism `[n]`; it is identified with the sections
of its kernel by `kernelLevelEquiv`. It has the discrete topology.

`Full G T` is the compatible-family limit over positive integers, with
transition from order `b` to order `a`, for `a ∣ b`, given by multiplication
by `b / a`. `Away G T m` restricts to positive orders coprime to `m`.
`PrimeAdic.Integral G T p` is the existing limit over orders `p^n`, including
`n = 0`, with successive transition multiplication by `p`.
All limits have their product-subspace topologies.

`PrimeProduct G T` is the product of these integral prime-adic modules over
`Nat.Primes`. `AwayPrimeProduct G T m` retains precisely the primes coprime
to `m`. The target topologies are product topologies.

These comparison statements require neither finite torsion sections nor
finite étaleness, a rank hypothesis, or a restriction on the characteristic.
They express a primary decomposition of torsion in the abelian group of
sections. In particular, they assert no profiniteness without the separate
finite-level finiteness hypotheses. The modulus `m` is any natural number:
`m = 1` retains all primes, and `m = 0` retains none and permits only torsion
order one on the source.

## Exact statements

In namespace `Langlands.GroupScheme.Tate.PrimeComparison`,
`FullPrimeProductComparison G T` says that there exists an additive
equivalence

`e : Full G T ≃+ PrimeProduct G T`

whose underlying additive homomorphism is exactly `toPrimeProduct G T`,
with both `e` and `e.symm` continuous. Thus the forward map must read each
prime-power coordinate of the original compatible family. Existence of an
unrelated equivalence would not satisfy this statement.

`AwayPrimeProductComparison G T m` makes the corresponding assertion for
`Away G T m`, `AwayPrimeProduct G T m`, and the exact map
`toAwayPrimeProduct G T m`.

`PrimeProductComparisons G T` is the conjunction of the full statement and
the away statement for every `m : ℕ`. This is the single combined target
for a subsequent proof task. Its parameters `S`, `G`, the commutativity
instance, and `T` remain arbitrary.

The forward maps already have proved continuity, homomorphism naturality,
and compatibility with restriction from the full to the away limit in
`PrimeComparison`. The new propositions additionally require bijectivity
and continuity of the inverse. Fixing the exact forward maps ensures that
any witnesses use those same published naturality and restriction laws.
This file does not supply a witness or prove any new comparison law.

## Actual abelian-scheme specialization

The three same-named abbreviations in
`Langlands.AbelianScheme.Tate.PrimeComparison` specialize these propositions
to `A.toGrp`, where `A : AbelianScheme S` is the published geometric bundle.
The carriers and forward maps are definitionally the actual abelian-scheme
aliases in `PrimeComparison`. Taking `T = Over.mk s` for an algebraically
closed field-valued point `s` gives the geometric-fibre application through
the existing `fibreLevelEquiv`; no arbitrary replacement fibre is introduced.

## Provenance and scope

Harris and Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), Chapter I, printed p.18 (PDF p.26), defines the full and
away Tate modules using these torsion limits. Registered source:
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

The exact topological primary-decomposition propositions and their arbitrary
group-scheme/test-scheme generality are derived infrastructure, not a theorem
quoted from that page. Their proposed mathematical justification is the
Chinese remainder decomposition of torsion at each positive order, compatible
with the multiplication transition maps. Each inverse coordinate should
depend on finitely many prime-power coordinates, which is the required route
to continuity even without compactness. This justification describes the
intended obligation; it is not an implemented proof.

The proposition format adapts Worker 92's published
`TwistPrimeComparisonStatement` to the actual group-scheme limits. It does
not identify these carriers with roots-of-unity limits. There is no rational
restricted-product comparison, scalar-ring comparison, monodromy theorem,
Weil pairing, or rank assertion in this file.
