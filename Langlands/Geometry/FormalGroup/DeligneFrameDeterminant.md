# Determinants of actual Deligne frame lattices

This module supplies derived algebra and an actual change of rational frame for
Deligne's data. All declarations are in `Langlands.DeligneFormalSpace`, with the
frame-specific declarations in its `FramedLatticePiSheaf` namespace.

The motivating source is Drinfeld, *Coverings of p-adic Symmetric Regions*
(1976), Section 2 A, printed pp.109–110 (PDF pp.3–4), item 4 and condition (c).
Registered source: `drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The source specifies a rational frame and the literal normalized determinant
lattice, and asserts a natural projective action. The change-of-frame formulas
below are derived linear algebra for the existing actual stalk lattices; this
passage does not give these formulas separately. The module does not construct
the full normalized projective action.

## The basis wedge and its integral lattice

`alternatingMap_apply_eq_det_smul` works over any commutative ring `R`, with
modules `M` and `N` and a basis `b` indexed by the finite type of arguments.
For an arbitrary module-valued alternating map `A`, it proves

`A(v) = det_b(v) • A(b)`.

The proof compares `A` with the composite of `b.det` and the linear map sending a
scalar to that scalar times `A(b)`. Basis extensionality reduces equality to
injectively indexed basis vectors. Such an indexing is a permutation, and the
two alternating maps have the same permutation sign and basis value. This
extends the scalar-target determinant formula to the target needed here.

For the remaining algebra, `O` is a commutative ring, `F` a field with an
`O`-algebra structure, and `V` an actual object of `ModuleCat F`. Coefficients,
modules and spaces use the common universe `u`. No injectivity, fraction-field,
valuation or flatness assumption is made on `O → F`.

`integralCoordinateRangeMap F f`, for an `F`-linear map `f : F^d → V`, is the
actual `O`-linear map `v ↦ f(algebraMap O F ∘ v)` from `O^d` to `V` with scalars
restricted to `O`. `exteriorStalkLattice_integralCoordinateRange` proves that the
existing top exterior lattice of its range is

`O · (f(e_0) ∧ … ∧ f(e_(d-1)))`.

Each tuple of vectors in the integral range admits integral coordinate
preimages. The alternating-map formula expresses its wedge as the standard
basis wedge multiplied by the determinant of those coordinates in `F`. The
ring-map determinant formula identifies that coefficient with the image of the
corresponding determinant in `O`, proving containment in the stated `O`-span.
Conversely the standard basis vectors have integral coordinate preimages, so
the basis wedge belongs to the defining generating set of the exterior
lattice. This also applies to dimension zero and to noninjective `f`; it makes
no assertion that the generator is nonzero.

`scaleStalkLattice_span_singleton` identifies the scalar image of a cyclic
lattice with the span of its scaled generator. `scaleStalkLattice_mul` proves
that successive scalar images multiply their scalars, after taking exterior
powers. `scaleStalkLattice_algebraMap_unit` proves that scalar multiplication by
the image of any `O`-unit preserves every `O`-submodule of `V`: its inverse unit
gives the reverse containment.

`exteriorBasisWedge_comp` proves that precomposing `f` by any `F`-linear
endomorphism `g` multiplies its basis wedge by the actual `LinearMap.det g`.
It uses the alternating-map formula and the determinant of a linear map
applied to a basis. Combining this with the cyclic-span descriptions gives
`exteriorStalkLattice_integralCoordinateRange_comp`: the top exterior integral
range of `f ∘ g` is the scalar image by `det(g)` of the corresponding lattice
for `f`. This algebraic identity does not require `g` to be invertible.

## Changing the actual rational frame

For the existing `M : FramedLatticePiSheaf d π X F` and an `F`-linear
automorphism `g` of `F^d`, `M.reframe F g` retains the lattice sheaf and
precomposes the rational frame with the image of `g` under the actual constant
sheaf functor. Thus its frame is `r ∘ g`. No admissibility field is supplied to
this construction.

`frameStalkMap_reframe` computes the actual constant-vector stalk map of this
new frame. It is the original `M.frameStalkMap F x` precomposed with `g`.
The proof evaluates naturality of the actual sheafification unit on the
constant presheaf map at the top open set, then composes with the original
frame, homogeneous inclusion and germ map. It therefore concerns the existing
sheafification-based frame map, rather than an additional chosen stalk frame.

`integralFrameStalkMap_eq` identifies the existing integral frame map with
`integralCoordinateRangeMap` of that stalk map. Consequently
`exteriorFrameStalkLattice_eq_span` describes the existing top exterior frame
lattice by its basis-frame wedge, and `exteriorFrameStalkLattice_reframe` proves
that this lattice scales by `det(g)` when the frame changes.

For the remaining three theorems, assume `d ≠ 0` and that the image of `π` in
`F` is nonzero, so that the existing rational `Π`-automorphism and all its
integer powers are available. For every integer `n` and point `x`,
`exteriorTranslatedFrameStalkLattice_reframe` proves the same determinant
scaling for the top exterior lattice of `Π^n r O^d`. The proof transports the
untranslated formula by the actual exterior power of `Π^n`, using the
previously constructed compatibility of exterior lattice formation and scalar
images with linear maps.

`normalizedFrameDeterminant_reframe` then proves the literal formula

`normalized(r ∘ g, n, x) = det(g) · normalized(r, n, x)`,

where `normalized(r,n,x)` is the existing
`π^(-n) ∧^d(Π^n r O^d)` in the exterior power of the actual total rational stalk.
Scalar commutativity gives the result after the translated formula; the
normalizing scalar is applied after the exterior power.
Finally, `normalizedFrameDeterminant_reframe_of_det_unit` proves equality of
the two normalized lattices if the actual determinant of `g` equals the image
of a specified unit of `O`.

## Scope

These are constructions and proved identities on the existing framed data and
actual stalk lattices. Arbitrary rational frame changes can change determinant
normalization. A grading shift and its coherence, central triviality, the full
`PGL(d,F)` action on admissible isomorphism classes, comparison with equality
of exterior subsheaves, the full moduli equivalence and representability remain
outside this module.
