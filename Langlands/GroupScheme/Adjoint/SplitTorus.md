# Maximal split tori in an actual adjoint quotient

This module records data for the image of an actual maximal split torus under
an actual adjoint quotient, over any field `k : Type u`. It also records the
additional real cocharacter surjectivity needed to identify the real space of
that image. Neither interface asserts that the data exist.

## Provenance and boundaries

Milne, *Algebraic Groups* (2017), Definition 12.14 and the following paragraph,
printed p.236 / PDF p.252, defines split tori and states that a quotient of a
split torus is split. Remark 17.63, printed p.373 / PDF p.389, identifies the
adjoint group with the quotient of a reductive group by its full centre.
Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition (2015),
Definitions A.1.8 and A.1.10–11, printed pp.468–470 / PDF pp.494–496, provide
the actual scheme-theoretic kernel, centre and faithfully flat quotient
conventions used by the imported interfaces. The retained official Milne
errata snapshot of 2026-11-02 has no correction to the cited Milne passages.

The structures here are derived packaging on the Library's group schemes,
maximal split torus predicate and real cocharacter spaces. In particular,
maximality of the supplied image and surjectivity on real cocharacters are
explicit data, rather than consequences proved from the cited sources here.
The module constructs no torus image, adjoint quotient or apartment and
does not prove their existence or a root-theoretic comparison.

## Scheme-level image data

For an actual quotient homomorphism `q : G ⟶ A`, actual torus inclusions
`i : T.toGrp ⟶ G` and `j : T_ad.toGrp ⟶ A`, and an actual commutative
group-scheme homomorphism `p : T ⟶ T_ad`, `IsAdjointSplitTorusImage q i j p`
records:

1. `IsAdjointQuotient q`.
2. `IsMaximalSplitTorus i` and `IsMaximalSplitTorus j`, including that both
   tori are split and both inclusions are closed immersions.
3. The actual square `groupHom p ≫ j = i ≫ q`.
4. Flatness, surjectivity and local finite presentation of the underlying
   scheme morphism of `p`.

These are actual torus objects and morphisms over `k`; `T_ad` is not a
quotient of a rational-point group. The fppf covering map onto `T_ad` and the
closed inclusion `j` express its role as the scheme-level image of the
restriction of `q`. No surjectivity on points of any fixed test scheme is
claimed. No finiteness of `p` is required: the intersection with the source
centre can contain a positive-dimensional torus. There is no smoothness or
reducedness assumption on its actual kernel.

`fppf` extracts the three underlying scheme-morphism properties.
`comp_eq_one_iff_mem_center` proves on every test scheme that `p(x) = 1`
if and only if `i(x)` lies in the full centre of `G`. The proof uses the
quotient's all-test kernel characterization, the commutative square, and
cancellation of the monomorphism underlying the closed immersion `j`.
`mem_range_kernel_iff` combines this with the published actual-kernel
range criterion. It therefore identifies the entire functor of points of
the kernel with the preimage of the centre, including infinitesimal points.
`cocharacter_comp_eq` composes the square with an actual integral cocharacter;
its proof is associativity of the categorical compositions.

## Real cocharacter data

`IsAdjointSplitTorusComparison q i j p` extends the scheme-level image
interface by surjectivity of the existing
`RealTorusSpace.cocharacterMapReal p`. This map is the real scalar extension
of actual postcomposition `ν ↦ ν ≫ p` on cocharacters, acting between the
existing spaces `RealTorusSpace.V T = ℝ ⊗[ℤ] X_*(T)` and
`RealTorusSpace.V T_ad`.

`realQuotientEquiv` applies Mathlib's linear first isomorphism theorem to
construct

`V T / ker(cocharacterMapReal p) ≃ₗ[ℝ] V T_ad`.

`realQuotientEquiv_mk` is the theorem's formula on quotient classes.
`exists_real_lift` is precisely the recorded real surjectivity. These results
require no integral surjectivity, splitting of the lattice map, primitive
cocharacter lift, finite kernel, or positive-rank assumption.

The later structural successor must prove real surjectivity for the genuine
image of a genuine adjoint quotient. It must also identify the displayed
kernel with the published `RealTorusSpace.relativeCentralDirections i`,
the simultaneous annihilator of the actual relative roots. That comparison,
and hence the identification of a root-annihilator apartment translation
quotient with `V T_ad`, is not a field or theorem of this module.
