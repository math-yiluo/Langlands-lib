# Closed-subgroup descent from finite Galois invariance

Author: Worker 1442. The component comparison argument is adapted from Worker
1333's published `Rational.UnipotentRadicalDescent` construction.

This is an internal generalization of the finite Galois component assembly in
`IsUnipotentRadical.finiteGaloisOverlap` to an arbitrary actual closed subgroup.
It reuses the published finite Galois tensor decomposition, component-cover
isomorphism assembly, canonical pullback comparisons, and effective descent
of affine closed subgroups. No unipotent-radical predicate is assumed here.

Let `k` and `L` be fields in an arbitrary common universe `u`, with
`Algebra k L`, `FiniteDimensional k L`, and `IsGalois k L`. Let `G` be a group
scheme over `Spec k`, `H` a group scheme over `Spec L`, and
`i : H ⟶ (GroupScheme.baseChange (algebraBaseMap k L)).obj G` a closed
inclusion. The main hypothesis is that for every actual automorphism
`σ : L ≃ₐ[k] L`, the range of the pullback of `i` along `galoisBaseMap k L σ`,
followed by the canonical ambient `descentBaseChangeIso`, equals the range of
`i`. Both ranges are subgroup functors evaluated on all relative test schemes,
not just field-valued points. No characteristic, perfection, or splitness
restriction is imposed.

`IsClosedSubgroup.overlap_range_eq_of_galois_range_eq` proves equality of the
two all-test subgroup ranges over the actual double overlap
`Spec L ×[Spec k] Spec L`, with the first transported by the ambient canonical
overlap isomorphism. Its proof first uses equality of ranges of closed
inclusions to construct a source isomorphism for each automorphism. It then
normalizes the inverse source isomorphism by the identity-pullback comparison,
proving its inclusion equation by cancellation and naturality.

The finite Galois tensor decomposition indexes the components of the overlap
by `Fin (Module.finrank k L)`. On each component the two projections are the
identity and the spectrum map of the corresponding Galois automorphism.
Direct-pullback comparison isomorphisms therefore turn the normalized source
isomorphism into an actual isomorphism between the two restrictions of `H`.
The inclusion equation follows by cancelling the direct-pullback comparisons,
using `Descent.pullIso_canonicalOverlap_eq` to identify the restricted ambient
canonical overlap, and applying inverse-comparison naturality. The latter two
generic lemmas are imported from `Rational.UnipotentRadicalDescent`.
`FiniteComponents.groupIso` assembles the component isomorphisms. Componentwise
extensionality proves that the assembled isomorphism respects the original
inclusion, and `SubgroupFunctor.range_iso_comp` gives the required equality of
ranges on the full overlap.

`IsClosedSubgroup.finiteGaloisDatum` is an actual
`Descent.Datum (fieldMap k L) H`, constructed by applying the canonical ambient
datum's `closedSubgroup` construction to the proved overlap equality. Thus it
contains the source overlap isomorphism and its triple-overlap cocycle. The
cocycle is derived by cancellation of the monic closed inclusion against the
ambient cocycle; it is not an additional premise. The theorem
`compatible_finiteGaloisDatum` proves that `i` is compatible with this datum and
the canonical ambient datum. Neither declaration requires affineness of `G`.

`IsClosedSubgroup.exists_descent_of_galois_range_eq` additionally assumes
`IsAffineHom G.X.hom`. It supplies an actual group scheme `H₀` over `Spec k`,
an inclusion `j : H₀ ⟶ G`, an isomorphism
`e : (GroupScheme.baseChange (fieldMap k L)).obj H₀ ≅ H`, proofs that `H₀`
is affine and `j` is closed, and the exact recovery equation
`(GroupScheme.baseChange (fieldMap k L)).map j = e.hom ≫ i`. It applies the
published effective closed-subgroup descent theorem to the overlap equality,
using flatness and surjectivity of a field-extension map of spectra and
affineness of the ambient group.

These constructions require invariance under every automorphism of a finite
Galois extension. Establishing that invariance from a single Frobenius
comparison, producing a finite field of definition for a geometric subgroup,
and constructing an invariant geometric maximal torus remain separate
obligations. This module neither proves the finite-field maximal-torus target
nor uses the no-torus unipotence theorem or forward maximal-torus base-change
preservation. Its provenance is the internal categorical composition described
above, not an assertion of an external existence theorem.
