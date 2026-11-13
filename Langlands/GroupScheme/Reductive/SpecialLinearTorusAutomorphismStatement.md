# Torus-preserving automorphisms of the special linear group

`Langlands.GroupScheme.SpecialLinearTorusAutomorphismStatement` states a matrix
description of an automorphism of the actual determinant-one group scheme
`SL_(n+1)` over any field `k : Type u`. It is a proposition definition, with no
proof supplied in this module.

The inputs are a split pinning `p` of this group, a group-scheme automorphism
`f`, a torus automorphism `t` of its supplied split maximal torus, and the actual
commutative inclusion square. The pinning need not have a specified coordinate
torus. There is no restriction on the characteristic or on `n`.

The inclusion square determines the full contravariant root-datum automorphism
`δ = rootDatumEquivOfTorusCompatibleIso ...`. Its character map is pullback
along `t.hom`. The existing `p.basedRootDatumProjection` removes the Weyl part
of `δ`; call the resulting based automorphism `θ`. The conditions in the
conclusion test its actual root-index permutation on every element of
`p.base.support`, rather than a supplied abstract diagram action.

There is one matrix `x ∈ GL_(n+1)(k)` with the following properties on every
scheme `Z` over `Spec k` and every `g ∈ SL_(n+1)(Γ(Z, 𝒪_Z))`:

- If `θ` fixes every simple-root index, then `f(g) = X g X⁻¹`.
- If `θ` moves some simple-root index, then `f(g) = X (g⁻¹)ᵀ X⁻¹`.

Here `f(g)` means transporting `g` to a group-scheme point using
`SpecialLinear.pointsEquiv`, composing that point with `f.hom`, and transporting
back. The matrix `X` is the image of `x` under the actual structure-ring map
`scalarMap Z : k →+* Γ(Z, 𝒪_Z)`. Thus the same matrix gives an identity on all
test schemes, including non-affine ones. The assertion is stronger than a
description of the automorphism on rational points.

For `n = 1`, the based type-`A₁` diagram has one vertex, so only the first
implication is needed. For `n = 0`, the group is `SL₁` and the base is empty;
the first implication describes its trivial automorphism. No distinct outer
class is asserted in either case.

## Provenance and source comparison

This is a derived specialization of the split-group automorphism theorem,
formulated using the Library's actual root data and all-test matrix coordinates.
It is a separate prerequisite for the Galois-discrepancy clause of
`SpecialLinearTitsCocycleStatement`; it has no Galois, descent or Hermitian
classification premise.

The primary source is J. S. Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups`, PDF SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
Propositions 23.44–23.45 and Corollaries 23.46–23.47 (printed pp.497–498,
PDF pp.513–514) identify the based-root-datum automorphisms with the outer
automorphisms and split the automorphism sequence for a split group.
Section 24.b, especially 24.5 (printed p.514, PDF p.530), identifies this quotient
with the diagram symmetries for a simply connected semisimple group.
The type-A discussion on printed p.524 (PDF p.540) identifies the inner group
with `PGL_(n+1)` and inverse transpose with the nontrivial diagram symmetry
when the matrix size exceeds two.

The author's registered errata
`milne-2017-algebraic-groups-errata-2026-11-02` correct the first group in the
proof of 23.47 to `Aut(G)` and explicitly restrict the p.524 discussion to matrix
size greater than two. The rank-zero and rank-one cases in this proposition are
derived extensions, as described above. The corrected limitation on 23.42 and
the corrections to 23.48 are not used as an unrestricted pinning-rigidity or
inner-form classification assertion here.

The all-test formulas, the choice of the Library's contravariant root-datum map,
and its Weyl-corrected based projection are the internal interface. Passing from
the adjoint inner group `PGL_(n+1)(k)` to a matrix in `GL_(n+1)(k)` uses the usual
field-valued matrix representative. These are proof obligations of this
specialization, rather than additional input hypotheses.
