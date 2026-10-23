# Compatibility of actual opposite canonical Jacquet lifts

This module states tuple independence and nested-subgroup averaging for the
existing stable-image constructions at inverse block scalars. It adapts the
published `CanonicalLiftCompatibilityStatement` Lean/Markdown pair to the
actual opposite radical. Its three declarations are transparent Prop-valued
definitions in `Langlands.Jacquet`; it supplies no proofs or new carriers.

## Parameters and hypotheses

Every declaration retains the template's parameters: a natural prime `p`
with `[Fact p.Prime]`, a finite p-adic field `F : PadicField.{uF} p`, supplied
`T : F.TopologicalData`, a natural rank `n`, a block shape
`B : GeneralLinear.BlockShape n`, and a carrier `V : Type uV` with
`[AddCommGroup V]` and `[Module ℂ V]`. The universes `uF` and `uV` are
independent. Each clause installs `T.topology` and
`T.generalLinearTopologicalGroup n`, so openness and smoothness refer to
the actual general linear group with this supplied topology.

Each clause quantifies over every
`ρ : Representation ℂ (GeneralLinear n F.Carrier) V` and every
`hAdmissible : IsAdmissible ρ`. Its smoothness witness is exactly
`hρ := hAdmissible.1`. A subgroup's compactness is a separate hypothesis
from its being an `OpenSubgroup`.

Every factorization hypothesis is the existing
`B.HasBlockIwahoriFactorization T K`. This means bijectivity of ordered
multiplication of the actual lower, Levi, and upper intersections with `K`,
together with the published conjugation containments for all weakly
contracting tuples. It is the same weak-chamber specialization used by the
upper template, stronger than the source's strict-chamber requirement.
No opposite factorization predicate is introduced or assumed.

All tuples have type `Fin B.length → F.Carrierˣ` and satisfy the same upper
strict predicate `B.IsStrictlyContracting T`. It requires normalized absolute
value less than one for each forward ratio `a_i/a_j`, with `i < j`.
Here the compressed group element is explicitly
`(B.blockScalar F.Carrier a)⁻¹`. On a lower block `(j,i)` with `i < j`,
conjugation by this inverse scalar multiplies entries by `a_i/a_j`;
this explains the opposite contraction direction without changing the
predicate on `a`. The quotient radical is
`N := B.oppositeUnipotentSubgroup F.Carrier`.

## Tuple independence

`BlockOppositeStableImageTupleIndependenceClause F T B V` takes one compact
open factorizing subgroup `K`, its compactness witness `hK`, and two
independently strictly contracting tuples `a,b`. It asserts

```lean
stableImage ρ hρ K hK (B.blockScalar F.Carrier a)⁻¹ =
  stableImage ρ hρ K hK (B.blockScalar F.Carrier b)⁻¹
```

This is equality of actual submodules of the same
`fixedVectors ρ K.toSubgroup`. The existing `stableImage` is the infimum
of the ranges of all natural powers of `compressedAction`. At the scalar
used here, that compressed action sends a fixed vector `v` to the
normalized finite-orbit average of `ρ ((B.blockScalar F.Carrier a)⁻¹) v`
over `K`. These constructions and the inclusion maps are provided by
`CanonicalLiftDefinitions`. No chosen lift or inverse map is used.

## Nested-subgroup averaging

`BlockOppositeStableImageNestedAverageClause F T B V` takes compact open
subgroups `K1,K0`, compactness witnesses `hK1,hK0`, the inclusion
`K1 ≤ K0`, and the existing factorization predicate for each subgroup.
It then quantifies over independently strictly contracting tuples `a1,a0`
and arbitrary vectors

```lean
w1 : stableImage ρ hρ K1 hK1 (B.blockScalar F.Carrier a1)⁻¹
w0 : stableImage ρ hρ K0 hK0 (B.blockScalar F.Carrier a0)⁻¹
```

Their ambient representatives are the existing inclusion maps:

```lean
v1 := stableImageToRepresentation ρ hρ K1 hK1
  (B.blockScalar F.Carrier a1)⁻¹ w1
v0 := stableImageToRepresentation ρ hρ K0 hK0
  (B.blockScalar F.Carrier a0)⁻¹ w0
```

The asserted implication is

```lean
Jacquet.mk ρ N v1 = Jacquet.mk ρ N v0 →
  Compact.averageMap ρ hρ K0 hK0 v1 = v0
```

Both quotient classes lie in the same ambient `Coinvariants ρ N` for the
opposite radical. The conclusion lies in `V` and averages over the
**larger** subgroup `K0`. The same-class premise is essential. The clause
does not assert that averaging preserves every quotient class or that a
vector `w0` exists for every `w1`.

`BlockOppositeCanonicalLiftCompatibilityStatement F T B V` is exactly
the conjunction of tuple independence followed by nested averaging.
Neither clause assumes tuple independence, core canonical-lift bijectivity,
averaging compatibility, stabilization, generalized-kernel identification,
or the existence of selected inverse maps. In particular, the nested clause
is not conditional on the tuple clause.

There are no positive-rank, nonempty-shape, proper-parabolic, or
nonzero-representation assumptions. Rank zero, empty and one-block shapes,
and zero representations remain in scope. The strict tuple inequalities
are vacuous for shapes with at most one block.

## Source and derived provenance

Bill Casselman, *Introduction to admissible representations of p-adic groups*,
Chapter III, *Induced representations and the Jacquet module*, revision
April 29, 2019, sections 4–6, especially III.5.4–III.5.7 (pages 6–7) and
III.6.2–III.6.3 (pages 7–8). Registered source:
`casselman-2019-jacquet-module`, SHA256
`377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.
Retained original:
`/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter III - Induced representations and the Jacquet module--2019.pdf`.
The original pages 5–8 were read and the fingerprint checked. No separate
project errata note was found for this source. The correction on page 7
retracts an earlier proof over general Noetherian coefficient rings; the
present targets use the field `ℂ`.

These are derived formulations, not verbatim source statements. After
III.5.4, the source describes the sufficiently high power image as a
canonical complement. Expressing its choice independence as equality of
the implemented all-power stable-image submodules requires an operator
comparison and finite-dimensional stabilization. Casselman's `τ_a` is an
unnormalized coset sum; the Library compression uses normalized compact
averaging. The comparison involves a positive finite subgroup-index
factor. Nonzero scalar multiples preserve ranges and kernels of
corresponding powers, but this module does not prove that comparison.

III.5.7 explicitly compares representatives of the same Jacquet class
for `K1 ⊆ K0` and averages over `K0`. The second clause preserves exactly
that direction and premise. Its independent tuple choices also require
choice independence in an eventual proof. Applying this source framework
to the opposite parabolic explains both the lower radical and inverse
scalar direction; III.6.2–III.6.3 motivate its use for the canonical pairing.
No pairing or nondegeneracy assertion is made here.

The internal template is the full published
`Langlands.Representation.Jacquet.CanonicalLiftCompatibilityStatement`
pair, with the radical and scalar direction changed explicitly and all
other parameters and hypotheses retained. An intended proof could
transport upper compatibility through continuous inverse transpose or
actual block reversal, including transport of factorization and normalized
compression. No such transport is an assumption or result of this module.
The upper nested-average proof and the separately stated opposite core
canonical-lift target are not dependencies of these proposition definitions.
