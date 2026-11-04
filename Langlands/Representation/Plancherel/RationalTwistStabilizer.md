# Actual rational-point twist stabilizers

Author: Worker 200.

This derived specialization connects the published generic twist-stabilizer
construction to actual rational points and the actual continuous central
restriction map. The source is J.-L. Waldspurger, *La formule de Plancherel
pour les groupes p-adiques (d'après Harish-Chandra)* (2003), III.7, printed
p.273 (PDF p.39), and the finite quotient used in the proof of III.7.1,
printed p.274 (PDF p.40), source ID `waldspurger-2003-plancherel`, SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
The source writes the stabilizer in the full \(X(G)\) while parameterizing
the unitary orbit by its quotient. This unit supplies the actual-point
comparison under an explicit actual-image finite-index premise.

The quotient input is the conditional actual quotient comparison derived
from Renard, *Représentations des groupes réductifs p-adiques*, 9 July 2026
edition, V.2.6, printed p.108 (PDF p.114), source ID
`renard-2026-representations-groupes-reductifs-padiques`, SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The general reductive proof of finite index remains separate.

## Canonical rational-point topology

Let \(F:\mathrm{Type}\ u\) have `Field`, `ValuativeRel`,
`TopologicalSpace` and `IsNonarchimedeanLocalField`. Let \(G\) be the shared
actual `GroupScheme (Spec (CommRingCat.of F))` with
`IsAffine G.X.left` and `LocallyOfFiniteType G.X.hom`.
Install exactly `rationalPointTopology F G.X` on \(G(F)\).

`rationalPoints_nonarchimedeanGroup` proves
`NonarchimedeanGroup (GroupScheme.rationalPoints G)` for this topology.
The imported `rationalPoint_isTopologicalGroup` supplies continuity of
the group operations. The imported
`BruhatTits.rationalPoint_isLocallyProfinite` and the proved
`Topology.LocallyProfiniteProof.vanDantzig` give a compact open subgroup
inside every identity neighborhood. Forgetting compactness provides the
open-subgroup basis required by `NonarchimedeanGroup`.
Thus the twisting constructions require no additional topology,
open-subgroup-basis, or compact-open-existence hypothesis.

These are the existing group law and actual canonical point topology.
The field and representation-carrier universes `u` and `uV` are independent.
The representations and classes are precisely the canonical
`SmoothRep` and `SmoothDualClass.{0, u, uV}`.

## Full stabilizer and the actual restriction kernel

Let \(T\) be an affine commutative group scheme, \(s:T\to G\) an actual
morphism and `hs : GroupScheme.IsCentral s`. Put \(A=s(T(F))\), the actual
point-map range, and use the existing actual rational norm-character family
\(\nu_G(\psi)=(\operatorname{rationalNormCharacters} G\,\psi).\mathrm{toMul}\).
No finite type condition on \(T\) is needed.

`rationalUnramifiedTwistStabilizerEmbedding s hs omega` embeds the full
unramified twist stabilizer of an actual canonical smooth-dual class
\(\omega\) into the kernel of `rationalUnramifiedCharacterRestrict s`.
The generic central-character theorem puts a stabilizing character in
`centralTrivialUnramifiedCharacters ν_G A`. The actual point-range kernel
equality then supplies membership in the actual restriction kernel.
The underlying continuous character is unchanged, which proves injectivity
by subtype extensionality. The `_apply` theorem gives equality of values
at every actual rational point. No finite-index premise is used for this
embedding.

The explicit remaining premise is
`hindex : (RenardCartan.splitValuationImage s).FiniteIndex`.
This is finite index of the existing actual composite point-map/valuation
range, not an assertion about the cokernel of character restriction.
`finite_rationalUnramifiedTwistStabilizer` transfers the actual restriction
kernel's conditional finiteness along the embedding.
`rationalUnramifiedTwistStabilizer_norm_eq_one` evaluates the proved
norm-one conclusion for its image. Hence every full stabilizer character
is unitary under that premise.

## The discrete-series orbit stabilizer

For this part give the actual point quotient \(G(F)/A\) a measurable space
and a measure `mu` with `Measure.IsHaarMeasure mu`.
The topology on the quotient is the quotient of the canonical point topology.
The subgroup is normal by `hs.range_le_center`.
Each declaration installs that derived normality before introducing the
Haar-measure instance and the dependent discrete-series class; normality is
not an additional premise.
The imported `DiscreteSeriesClass A hs.range_le_center mu` consists of the
canonical irreducible admissible smooth-dual classes satisfying the actual
square-integrability condition on this quotient.

Under `hindex`, `rationalDiscreteSeriesStabilizerEquivFull` specializes
`discreteSeriesStabilizerEquivFull` to the actual point group, actual norm
family and actual point-image subgroup:
\[
 \operatorname{discreteSeriesStabilizer}(\omega)
 \simeq
 \operatorname{unramifiedTwistStabilizer}(\omega.\mathrm{val}).
\]
The finite quotient instance used by that construction is supplied by
`finite_rationalCentralQuotient s hs hindex`; its generic common norm
kernel is definitionally the actual rational one. Both directions retain
the original continuous character, as the `_apply` theorem records.
`finite_rationalDiscreteSeriesStabilizer` transfers finiteness of the full
stabilizer across this multiplicative equivalence.
This is the stabilizer of the actual unitary orbit action, rather than a
new representation relation or an arbitrary parameter quotient.

## Scope

The construction preserves arbitrary nonarchimedean local fields, including
both characteristics. It does not need connectedness, reductivity, splitness,
or a chosen rational-point realization. The intended source application takes
\(s:A_G\to G\) to be the actual split-component inclusion, but the actual-image
finite-index theorem remains a separate proof obligation.
No restriction surjectivity, orbit manifold, orbit measure, finiteness of the
family of discrete-series orbits, finite spectral support, formal-degree
identity, Fourier inversion, or Plancherel theorem is asserted.

Local instances use explicit module-specific names to prevent generated-name
collisions under joint imports. Their types, bodies and local scope are
unchanged.
