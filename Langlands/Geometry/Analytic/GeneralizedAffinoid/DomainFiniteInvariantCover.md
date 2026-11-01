# Common open stabilizers and finite equivariant spectrum quotient covers

Authors: Worker 56; Worker 36, whose published strict rational common-stabilizer
construction supplies the finite intersection pattern adapted here.

## Inputs and common subgroup

Let `K : Type u` be a complete ultrametric normed field, let
`P : PresentedAffinoidAlgebra K` be an actual finite positive-polyradius
affinoid quotient, and let `G : Type v` be a topological group. Fix
`ρ : DomainSpectralAction G P`, an action by actual bounded algebra
automorphisms continuous for the represented-domain spectral topology.
All declarations are in
`PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction`.

For a finite family `D : I → Domain K P`, `finiteLocusOpenSubgroup D`
is the finite intersection of its open setwise locus stabilizers.
The index type may lie in any universe `w`. Its membership theorem says
precisely that an element preserves every represented locus; its order
theorem characterizes the largest open subgroup with that property.
For a prescribed open subgroup `H`,
`finiteFamilyOpenSubgroup H D` is its intersection with this common
stabilizer. The corresponding membership and order theorems characterize
the largest open subgroup inside `H` preserving the whole family.
For an empty index type these constructions give the full group and `H`,
respectively.

`finiteInvariantFamily` retains each complete domain representation as an
object of the invariant-domain category for this subgroup.
`finiteInvariantTarget` retains any given `H`-invariant target in that
same category. `finiteInvariantFamilyArrow` retains each original domain
arrow, including its actual bounded restriction and its structural-map
equation. The three object and arrow formulas are definitional equalities.
The construction uses only subgroup containment to prove invariance; it
neither changes section algebras nor chooses replacement presentations.

## The finite spectrum quotient

Fix `d : ρ.InvariantDomain H` and an actual finite cover
`c : Domain.FiniteCover d.obj`. This cover already stores a natural number
`c.size`, complete representations `c.obj i`, actual bounded domain
arrows `c.map i`, and pointwise covering of the target represented locus.
Put `J = ρ.finiteFamilyOpenSubgroup H c.obj`.

`finiteCoverComponentAction` is the existing action of `J` on the
actual spectrum of the component section algebra. Its operators are
inverse pullbacks of the constructed bounded section automorphisms.
`finiteCoverComponent` composes the equivariant structural
spectrum-to-locus quotient with the locus inclusion induced by the
unchanged bounded domain arrow. Its underlying map is exactly the
published `c.componentMap i`.

`finiteCoverSpectrumAction` acts on the topological disjoint union

```text
Σ i : Fin c.size, BanachSpectrum (c.obj i).algebra.
```

It fixes the component index and uses that component's spectrum action.
Continuity for each fixed group element follows from continuity on each
summand and the continuous summand inclusions. The identity and product
laws are the corresponding component action laws.

`finiteCoverQuotient` has exactly the continuous map `c.totalMap` as its
underlying map. The target is the actual locus `d.obj.locus`, with the
restricted original ambient action. Equivariance follows on each
summand from the constructed equivariant component map.

The underlying quotient is surjective because the component loci cover
and each component section spectrum surjects onto its represented locus.
The finite union is compact and the target locus is Hausdorff, so it is
closed. The existing finite-cover theorem gives its quotient property
for the target's actual subspace topology. Openness, closedness and
continuity out of the target are detected on these unchanged component
maps. The tested continuous map may have an arbitrary topological target
in universe `w` and need not be equivariant.

## Provenance and limits

This is an internal construction. The finite intersection and lifting
pattern adapts `StrictTestDomain/InvariantSubgroupRestriction` and
`StrictTestDomain/FiniteInvariantCover` to full represented domains.
The actual action and quotient maps use `DomainInvariantLocus`,
`DomainInvariantActions` and `DomainTopology`. The Lean proof of
equivariance composes existing equivariant morphisms and evaluates their
commuting equations on each summand. The topological conclusions reuse
the exact finite-cover quotient map. No new literature theorem is
attributed.

The finite cover may be empty when the target locus is empty. No
nonempty-spectrum, nonzero-quotient, reducedness or nontrivial-valuation
assumption is introduced. The target is the represented locus;
surjectivity onto the target section spectrum would require a further
argument and is not claimed. `Action TopCat J` records continuous
operators for fixed group elements. Joint continuity, general analytic
gluing, structure sheaves, analytic etale sites and Harris specialization
remain further constructions.
