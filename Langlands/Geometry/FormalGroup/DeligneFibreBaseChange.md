# Actual residue-field fibres under base change

This module constructs the canonical comparison between the fibre of a
structural pullback and the residue-field extension of the original fibre.
For the actual homogeneous Pi maps it proves the comparison square and the
forward inclusion of zero loci.

The source motivation is Drinfeld, *Coverings of p-adic Symmetric Regions*
(1976), §2 A, printed pp.109–110 (PDF pp.3–4): the tangent sheaf has cyclically
graded invertible components, and condition (a) restricts the corresponding
lattice component to the set of zeros of Pi on the tangent line. The
comparison here is derived categorical infrastructure for these actual zero
loci. It does not prove the source's special-formal-module construction or
Proposition 2.4.

## Parameters and actual fibres

All schemes and coefficient types lie in the same universe. Let
`f : S' ⟶ S` be any scheme morphism and `x : S'`. No flatness, nilpotence or
local-field hypothesis is needed for this comparison.

Write `q : Spec κ(x) ⟶ S'` and `p : Spec κ(f x) ⟶ S` for the canonical
residue-field maps, and `r : Spec κ(x) ⟶ Spec κ(f x)` for the map induced by
`f.residueFieldMap x`. Mathlib proves the actual equality `r ≫ p = q ≫ f`.
`structuralFibreBaseChangeIso` is the natural isomorphism

```
f* followed by q*  ≅  p* followed by r*.
```

It composes the canonical structural pullback composition comparison for
`q ≫ f`, pullback congruence along that equality, and the inverse composition
comparison for `r ≫ p`. Its objects are actual sheaves of modules on the
residue-field schemes.

## Homogeneous components and Pi

Let `d` be a positive natural number, let `a` be a global structural section
of `S`, and let `M` be an actual `GradedPiSheaf` with `Pi^d = a`. In the
existing pullback, each homogeneous component is the actual range of the
pulled split inclusion. `pullbackComponentIso_hom_pi` proves that the
canonical isomorphisms from the pulled original components to these ranges
commute with the degree-one Pi maps. The proof composes with the monic
inclusion into the total module and uses the original component-Pi square
and functoriality. `pullbackComponentIso_inv_pi` derives the inverse square
by cancellation.

`GradedPiSheaf.fibrePullbackIso` first pulls back the inverse range
comparison along `q`, then applies `structuralFibreBaseChangeIso` to the
original component. It is therefore an isomorphism

```
(f* M)^i at x  ≅  r* (M^i at f x).
```

Here each fibre is the actual structural pullback defined by
`fibreComponent`, rather than an assumed tensor presentation.
`fibrePullbackIso_pi` combines the inverse component-Pi square with
naturality of the structural comparison to prove the square for the actual
fibre Pi maps.

## Vanishing and scope

`fibrePi_pullback_eq_zero_iff` proves that the pulled fibre Pi map is zero
exactly when the actual `r*` image of the original fibre Pi map is zero.
Cancellation by the two comparison isomorphisms proves both implications.
`mem_piZeroLocus_pullback` then uses preservation of zero by structural
pullback. `preimage_piZeroLocus_subset` records the resulting inclusion

```
f ⁻¹' (M.piZeroLocus i) ⊆ (M.pullback f).piZeroLocus i.
```

The reverse inclusion requires reflection of zero along the residue-field
extension and is not asserted here. This module does not establish equality
of zero loci, constancy transport on those loci, conditions (b) or (c),
admissibility transport, the admissible Nilp functor, the PGL action,
representability or the comparison with special formal modules.
