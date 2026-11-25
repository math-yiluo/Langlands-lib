# Finite freeness of actual integral Hom groups

`Langlands.AbelianScheme.homFiniteFree` proves exactly
`Langlands.AbelianScheme.HomFiniteFreeStatement.{u}`.
For every algebraically closed characteristic-zero field `k : Type u` and
actual abelian schemes `A`, `B` over `Spec k`, it gives

```lean
Module.Free ℤ (A ⟶ B) ∧ Module.Finite ℤ (A ⟶ B)
```

The integer module is the existing canonical one on actual group-scheme
homomorphisms. The universe `u` is arbitrary. The theorem adds no
mathematical premises and requires no chosen basis, lattice, polarization,
dimension bound or Tate comparison.

The proof applies the published algebraic criterion
`Langlands.Algebra.IntegralLocalLattice.finiteFree` to the actual group
`A ⟶ B`, its rationalization `Hom0 A B = ℚ ⊗[ℤ] (A ⟶ B)`, and the canonical
integer-linear map `homToHom0`. Its three inputs are:

- `Rosati.homToHom0_injective_of_charZero A B`, imported through
  `HomTorsionRestriction`, specializes `Tate.ofHom_injective`. Equality
  in the rationalization gives equality after multiplication by a
  nonzero integer. `Tate.hom_nsmul_injective` cancels the corresponding
  positive multiple: multiplication on the source abelian scheme is
  an isogeny whose underlying scheme map is an effective epimorphism.
  Characteristic zero ensures that each positive integer is a unit on
  `Spec k`. This lemma has no Rosati hypothesis.
- `hom_modN_finite A B 2 (by decide)` proves that the quotient of actual
  Hom by twice Hom is finite. The published torsion-restriction proof
  identifies this quotient with an image in the finite function set
  between geometric two-torsion points.
- `homLocalLattice k A B` proves that the inverse image of every finitely
  generated rational submodule of `Hom0 A B` is finitely generated over
  the integers. Its published proof obtains a positive quadratic
  cube function from mixed Euler coefficients of ample line bundles;
  positivity and a uniform denominator bound give this local lattice
  property. The ample bundles are constructed within that proof.

The algebraic criterion uses the finite quotient modulo two to bound
rationally independent families in the image. The local lattice property
then gives finite generation of the whole integral group. Injection into
the rational vector space gives torsion-freeness, and the structure
theorem over the integers gives freeness. Finite-dimensionality of the
whole rational Hom space is not an input.

This is an internal composition of the published results in
`Langlands.Algebra.IntegralLocalLattice`,
`Langlands.AbelianScheme.HomTorsionRestriction`, and
`Langlands.AbelianScheme.HomLocalLatticeProof`. The target is the
finite-freeness part of J. S. Milne, *Abelian Varieties*, author revision
of 2 January 2022, Theorem 12.5, printed/PDF pp.21–22, registered as
`milne-abelian-varieties-1986-author-2022`. The implemented mixed-Euler
and modulo-two route is explained in the imported modules' Markdown;
it differs from Milne's degree-polynomial and prime-adic argument.
The theorem asserts neither the source's rank bound nor its additional
Tate-module conclusion.
