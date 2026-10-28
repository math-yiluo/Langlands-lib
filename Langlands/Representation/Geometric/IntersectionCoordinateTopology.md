# Continuous transport from Levi coordinates to actual intersections

This module identifies the coordinate subgroups of the block Levi `B.Levi R`
with the actual intersection subgroups of the embedded Levi
`M = B.leviSubgroup R` in Bernstein--Zelevinsky (1977), section 6.3. The
identifications are isomorphisms of topological groups. Every map is the
restriction of the published block equivalence `B.leviEquiv R`, or of its
continuous form `B.leviEquivContinuous R`, together with subtype re-association
and subgroup relabelling. No abstract choice of isomorphism is made. The module
states no Haar law, no modulus formula and no orbit or Jacquet comparison.

## Scope and conventions

Throughout, `R : Type uR` is any commutative ring. The topological statements
assume a topology on `R` with `IsTopologicalRing R`. The algebraic equivalence
`coordinateIntersectionMulEquiv` needs no topology on `R`. Also `n` is any
natural number, including `n = 0`, `B : GeneralLinear.BlockShape n` is any block
shape, `w : Equiv.Perm (Fin n)` is any permutation, and `K` is any subgroup of
`GeneralLinear n R`. We write `g = GeneralLinear.permutation n R w` and
`M = B.leviSubgroup R`. No closedness, field, positive-rank, minimality,
standard-intersection or Haar hypothesis is used. No case distinction on `n` is
needed.

Source intersections use the inverse conjugation convention of BZ77. Section 2.6
(printed p. 447) writes `w(h) = w h w⁻¹`. Hence `M ∩ w⁻¹(K)` consists of the
`m ∈ M` with `g m g⁻¹ ∈ K`. In Lean this subgroup appears in three forms:

- the coordinate subgroup `K.comap (conjugatedLeviMap R B w)` of `B.Levi R`.
  It consists of the block tuples `x` with `g (B.leviEmbedding R x) g⁻¹ ∈ K`;
- `General.intersectionIn M K g`, the subgroup of `M` of elements `m` with
  `g m g⁻¹ ∈ K`;
- the ambient subgroup `intersectionSource M K g = M ⊓ K.comap (conj g)` of
  `GeneralLinear n R`.

All subgroups carry the subspace topology induced from their ambient group.
`B.Levi R` is a product of general linear groups with the product topology.
`GeneralLinear n R` is Mathlib's `Matrix.GeneralLinearGroup (Fin n) R` with
its topology as the units of the matrix ring.

## The generic equivalences

`leviEquiv_symm_mem_comap` proves that `(B.leviEquiv R).symm y` lies in the
coordinate subgroup for every `y` in `General.intersectionIn M K g`. This is the
canonical membership proof used by the inverse map.

`coordinateIntersectionMulEquiv R B w K` is the algebraic equivalence

`K.comap (conjugatedLeviMap R B w) ≃* General.intersectionIn M K g`.

Its forward map sends `x` to `⟨B.leviEquiv R x.val, x.property⟩`. Its inverse
sends `y` to `⟨(B.leviEquiv R).symm y.val, leviEquiv_symm_mem_comap R B w K y⟩`.

`coordinateIntersectionEquiv R B w K` is the same multiplicative equivalence as
a continuous multiplicative equivalence (`≃ₜ*`). Both directions are continuous
in the induced subgroup topologies, because they are restrictions of
`B.leviEquivContinuous R` and of its inverse. The following value lemmas are
proved, all by `rfl` except the last:

- `coordinateIntersectionEquiv_apply`: the forward value is literally
  `⟨B.leviEquiv R x.val, x.property⟩`.
- `coordinateIntersectionEquiv_apply_eq_leviEquivContinuous`: the underlying
  element of `M` is `B.leviEquivContinuous R x.val`.
- `coordinateIntersectionEquiv_apply_val`: its ambient matrix is
  `B.leviEmbedding R x.val`.
- `coordinateIntersectionEquiv_symm_apply`: the inverse value is
  `⟨(B.leviEquiv R).symm y.val, leviEquiv_symm_mem_comap R B w K y⟩`.
- `leviEmbedding_coordinateIntersectionEquiv_symm`: the block embedding of the
  inverse value is the ambient matrix of `y`.

`General.intersectionInAmbientContinuous M K w` is defined for an arbitrary
topological group `G`, subgroups `M, K` and an element `w : G`. It packages the
published re-association `General.intersectionInAmbient M K w` as a continuous
multiplicative equivalence

`General.intersectionIn M K w ≃ₜ* intersectionSource M K w`.

Its continuity fields are the published lemmas
`continuous_intersectionInAmbient` and `continuous_intersectionInAmbient_symm`.
Both directions keep the underlying element of `G` unchanged.

`coordinateIntersectionAmbientEquiv R B w K` is the composite

`K.comap (conjugatedLeviMap R B w) ≃ₜ* intersectionSource M K g`.

Its proved value formulas are as follows. The ambient value of `x` is
`B.leviEmbedding R x.val`. The inverse of an ambient element `h` is
`(B.leviEquiv R).symm ⟨h.val, h.property.1⟩`, where `h.property.1` is the proof
that `h ∈ M`. The block embedding of that inverse value is `h.val`.

## The three source intersections

`sourceParabolic R B C w`, `sourceLevi R B C w` and `sourceUnipotent R B C w`
are by definition the coordinate subgroups for `K = C.parabolic R`,
`C.leviSubgroup R` and `C.unipotentSubgroup R`. So the generic equivalence
applies to them without change. The abbreviations
`sourceParabolicIntersectionEquiv`, `sourceLeviIntersectionEquiv` and
`sourceUnipotentIntersectionEquiv` record these three specializations of
`coordinateIntersectionEquiv`. Their targets are the actual BZ77 groups
`M ∩ w⁻¹(Q)`, `M ∩ w⁻¹(N)` and `M ∩ w⁻¹(V)`, for
`Q = C.parabolic R`, `N = C.leviSubgroup R` and `V = C.unipotentSubgroup R`.

The published algebraic equivalence `DiagonalCharacter.sourceActualEquiv` in
`IntersectionLeviDiagonalCharacterProof` has literally the same forward and
inverse formulas as the Levi specialization. This module does not import that
proof module and states no agreement lemma with it. The imported pairs are not
changed.

## Refined subgroups and action compatibility

Fix block shapes `B, C`, a permutation `w`, a block refinement
`S : BlockRefinement B` and `hS : IsIntersectionRefinement (F := R) B C w S`.
`subgroupEqualityContinuous h` relabels an actual subgroup along an equality
`h : H = K` of subgroups. It is a continuous multiplicative equivalence that
leaves the underlying element unchanged in both directions.

- `refinedLeviIntersectionEquiv R B C w S hS` is the relabelling
  `refinedLevi R B S = sourceLevi R B C w` (from `hS.2.1`), followed by
  `coordinateIntersectionEquiv` for `K = N`. Its type is
  `refinedLevi R B S ≃ₜ* General.intersectionIn M N g`.
- `refinedUnipotentIntersectionEquiv R B C w S hS` is the relabelling
  `refinedUnipotent R B S = sourceUnipotent R B C w` (from `hS.2.2`), followed
  by `coordinateIntersectionAmbientEquiv` for `K = V`. Its type is
  `refinedUnipotent R B S ≃ₜ* intersectionSource M V g`.

Their forward ambient values are proved by `rfl` to be the literal block
embeddings `B.leviEmbedding R m.val` and `B.leviEmbedding R u.val` of the
original coordinate values. Inverse value formulas and the block embeddings of
inverse values are also proved.

`refinedUnipotentIntersectionEquiv_normalizerConj` proves the exact action
compatibility. For every `m : refinedLevi R B S` and `u : refinedUnipotent R B S`,

```
E_U (HaarModulus.normalizerConj (refinedUnipotent R B S)
       (refinedLeviNormalizer R B S m) u)
  = HaarModulus.normalizerConj (intersectionSource M V g)
      (General.intersectionToCorrectionNormalizer M N M V g M.le_normalizer
        (C.leviSubgroup_le_normalizer_unipotentSubgroup R) (E_L m))
      (E_U u),
```

where `E_L = refinedLeviIntersectionEquiv R B C w S hS` and
`E_U = refinedUnipotentIntersectionEquiv R B C w S hS`. The proof uses subtype
extensionality. Both sides have ambient matrix
`B.leviEmbedding R m.val * B.leviEmbedding R u.val * (B.leviEmbedding R m.val)⁻¹`,
and the two sides agree by the homomorphism laws `map_mul` and `map_inv` of
`B.leviEmbedding R`. No action-conjugacy premise or Haar-scaling conclusion is
involved.

## Provenance

Original source: Bernstein and Zelevinsky, *Induced representations of
reductive p-adic groups I* (1977), section 6.3, printed p. 468 (PDF page 29).
It states that `(M ∩ w⁻¹(Q), M ∩ w⁻¹(N), M ∩ w⁻¹(V))` is a parabolic triple of
subgroups in `M`. The conjugation convention is from section 2.6, printed
p. 447. Literature ID `bernstein-zelevinsky-1977-induced-i`; SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`. No project
errata entry for this source was found.

The source does not name the topological packaging or the coordinate
identification. Both are internal derivations from the published block
embedding API (`B.leviEquiv`, `B.leviEquivContinuous`, `B.leviEmbedding`) and
the published actual-subgroup APIs (`General.intersectionIn`,
`General.intersectionInAmbient` and its continuity lemmas,
`General.intersectionToCorrectionNormalizer`, `HaarModulus.normalizerConj`,
`refinedLeviNormalizer`, `IsIntersectionRefinement`). The arbitrary
commutative topological-ring scope follows from these APIs.

Author: Worker 823.
