# Local Weil transfer and field inclusion

Authors: Worker 1828 (the supplied Lean formula) and Worker 1691 (this
statement pair and original-source comparison).

`Langlands.LocalClassField.ExtensionWeilTransferReciprocityStatement.{u,v}`
is a proposition definition stating the transfer/inclusion square for geometric
local Weil reciprocity. This module supplies a statement target. It does not
prove the square or construct a reciprocity map.

## Quantifiers and actual maps

The proposition quantifies over every prime `p`, every
`F : PadicField.{u} p`, every `E : PadicField.{v} p`, and every
`f : F.Carrier →ₐ[Padic p] E.Carrier`. The carrier universes `u` and `v`
are independent. Such an embedding makes the extension finite, since both
fields are finite over `Padic p`; no Galois or abelian extension condition
is imposed.

The other inputs are arbitrary
`LocalFactor.RankOne.ReciprocityCandidate F` and
`LocalFactor.RankOne.ReciprocityCandidate E`, each satisfying
`GeometricWeilReciprocityRelation` for its canonical topological data.
These are the only hypotheses. The candidate relation includes the geometric
order identity and the geometrically normalized profinite norm-residue
relation. It does not include this transfer square.

Write `R_F = LocalFactor.RankOne.reciprocityUnits F eF` and similarly
`R_E`. Each is the actual projection from the local Weil group to its
topological abelianization, followed by the supplied reciprocity isomorphism
to the field's multiplicative group. The topologies are
`F.canonicalTopologicalData.topology` and
`E.canonicalTopologicalData.topology`.

Let `j = Weil.Local.extensionWeilMap F E f : W_E → W_F` and
`H = j.toMonoidHom.range`. The imported
`extensionWeilMap_injective` identifies `W_E` with `H`;
`InductionAlong.rangeInverse` is precisely the inverse on this range.
It is not a section of the abelianization projection.
The imported `extensionWeilMap_range_finiteIndex` supplies the finite-index
instance required by Mathlib's transfer. In fact the published
`extensionWeilMap_range_index` computes the index as the field-extension
degree.

For every `y : Weil.Local.localWeilGroup F`, the asserted equality is

\[
  \operatorname{transfer}(R_E\circ j^{-1})(y)
    = f^\times(R_F(y)),
  \qquad f^\times=\operatorname{Units.map}(f).
\]

Here `transfer` is literally `MonoidHom.transfer` for the subgroup `H`
and the homomorphism `H → Eˣ` obtained by composing `rangeInverse` with
`R_E`. Its value is fixed by Mathlib's coset-product construction.
No arbitrary transfer map or comparison isomorphism is supplied as a
premise. This is the coordinate form of the usual square
`W_F^ab → W_E^ab` above `Fˣ → Eˣ`, with transfer on the Weil side and
inclusion on the field side.

## Original sources and normalization

Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg,
GTM 67, Springer (1979), registered as `serre-1979-local-fields`,
SHA256 `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The retained original is
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.
Chapter XI, §3, “Functorial Properties of the Reciprocity Map,” diagram
(2), printed p.170 / PDF p.176, has field inclusion above transfer.
The explanation and limiting diagram (2)* on printed p.171 / PDF p.177
give the absolute-Galois version. These pages were read directly, including
the rendered diagram. In Serre's notation the extension is `E'/E`;
these correspond to this module's `E/F`. The ambient finite Galois
extension used to draw Serre's diagram does not require `E'/E` to be
Galois.

John Tate, *Number theoretic background*, in *Automorphic Forms,
Representations and L-Functions*, Proc. Sympos. Pure Math. 33, Part II
(1979), pp.3–26, registered as `tate-1979-number-theoretic-background`,
SHA256 `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
The retained original is
`/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part II.pdf`.
Printed pp.3–4 / PDF pp.12–13 define transfer and state the Weil-group
inclusion/transfer square as (W3). The adjacent formula (1.2.2) gives the
other functorial square, pairing norm with Weil-group inclusion.
Section 1.4.1, printed p.6 / PDF p.15, fixes geometric normalization.
These pages were read directly. Tate writes reciprocity in the direction
`r_F : Fˣ → W_F^ab`; this module uses its inverse, followed by the
quotient projection when evaluated on `W_F`.

The project's geometric normalization sends a uniformizer to geometric
Frobenius, the inverse of arithmetic Frobenius. Equivalently, `R_F`
sends geometric degree one to normalized order one. Serre uses arithmetic
normalization. Replacing arithmetic reciprocity by geometric reciprocity
inverts its values on the abelianized group. In the inverse direction
used here, this replaces `R_F(y)` by `R_F(y)⁻¹`, and likewise for `R_E`.
Both transfer and `fˣ` are homomorphisms and preserve inverses, so inverting
the two sides of the arithmetic square gives exactly the geometric square
with the same transfer and field inclusion. Thus this compatibility has the
same form in both normalizations.

## Relation to the profinite statement and proof boundary

The published
`Langlands.LocalClassField.ProfiniteReciprocityTransferFunctoriality`
in [ProfiniteReciprocityStatement](ProfiniteReciprocityStatement.md) states
the analogous square on absolute-Galois abelianizations. It uses
`Field.absoluteGaloisGroup.mapOfAlgebra`, and its transfer is constrained
by the genuine `MonoidHom.transfer`. It also concludes the finite-index
subgroup realization and continuous descent.

This module states the square directly for the separately presented actual
local Weil groups and their already constructed injective, finite-index
extension map. It does not assume that profinite theorem, a comparison
isomorphism, or the existence of normalized candidates. Comparing the
Weil and Galois transfers through their actual projection maps is one
possible route for a later proof; no such comparison is proved here.
Likewise, the common-closure `TransferRelation` in
[ReciprocitySystem](ReciprocitySystem.md) describes the same mathematical
compatibility for fixing subgroups in a common closure, rather than
supplying a proof for these separately packaged Weil groups.

The Lean formula was supplied by Worker 1828. Its translation to these
actual field embeddings and inverse reciprocity coordinates is documented
above; it is not a verbatim formula in Serre's notation. A later proof can
target the proposition defined here without strengthening its premises.
