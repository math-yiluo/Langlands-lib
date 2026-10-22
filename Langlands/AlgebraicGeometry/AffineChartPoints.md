# Points of schemes over affine spectra through affine charts

Author: Worker 268.

Module `Langlands.AlgebraicGeometry.AffineChartPoints`, namespace
`Langlands.AlgebraicGeometry`. This is a helper module for the proof
`Langlands.AbelianScheme.torsionFiniteEtale` (module
`Langlands.AbelianScheme.TorsionFiniteEtale`). It describes points of a scheme
over `S` with values in spectra of algebras over an affine open of `S`. It
contains no statement target.

## Setting

Fix a scheme `S`, an open `S₀ : S.Opens` and `hS₀ : IsAffineOpen S₀`. All
algebras below are commutative rings `C : Type u` with
`[Algebra Γ(S, S₀) C]`.

## Test objects

- `testMap hS₀ C : Spec (CommRingCat.of C) ⟶ S` is the composite
  `Spec.map (algebraMap Γ(S, S₀) C) ≫ hS₀.fromSpec`. `testObj hS₀ C : Over S`
  is `Spec C` with this structure map.
- For an algebra map `q : C →ₐ[Γ(S, S₀)] C'`, `testHom hS₀ q : testObj hS₀ C' ⟶
  testObj hS₀ C` is `Spec.map q` as a morphism over `S`. The lemmas are
  `testHom_left` (its underlying morphism is `Spec.map q`), `testHom_id`, and
  `testHom_comp`: `testHom hS₀ (q'.comp q) = testHom hS₀ q' ≫ testHom hS₀ q`.
- `specMap_surjective`: if a ring map `q : C →+* C'` is surjective and every
  element of its kernel is nilpotent, then `Spec.map q` is surjective on
  underlying points. The proof identifies the range of `PrimeSpectrum.comap q`
  with the zero locus of the kernel (`range_comap_of_surjective`), which is
  everything because the kernel lies in the nilradical.
- `range_testHom_comp`: under the same hypotheses on an algebra map `q`, for
  every `x : testObj hS₀ C ⟶ Y` over `S` the image of `testHom hS₀ q ≫ x` equals
  the image of `x`.

## Charts

`Chart S₀ Y`, for `Y : Over S`, is a structure with an open `U` of `Y.left`, a
proof `isAffine : IsAffineOpen U`, and `le : U ≤ Y.hom ⁻¹ᵁ S₀`. For a chart `c`:

- `c.Ring` is `Γ(Y.left, c.U)` with its commutative ring structure, and the
  `Γ(S, S₀)`-algebra structure given by `Y.hom.appLE S₀ c.U c.le`
  (`algebraMap_eq`).
- `c.fromSpec` is the open immersion `c.isAffine.fromSpec`, with range `c.U`
  (`range_fromSpec`) and `fromSpec_hom`: `c.fromSpec ≫ Y.hom` equals
  `Spec.map (algebraMap Γ(S, S₀) c.Ring) ≫ hS₀.fromSpec`.
- `c.pt hS₀ ψ : testObj hS₀ C ⟶ Y`, for `ψ : c.Ring →ₐ[Γ(S, S₀)] C`, is
  `Spec.map ψ ≫ c.fromSpec` as a morphism over `S` (`pt_left`).

The properties of these points are:

- `pt_injective`: `ψ ↦ c.pt hS₀ ψ` is injective. This cancels the
  monomorphism `c.fromSpec` and uses that `Spec.map` is injective.
- `testHom_comp_pt`: `testHom hS₀ q ≫ c.pt hS₀ ψ = c.pt hS₀ (q.comp ψ)`.
- `range_pt`: the image of `c.pt hS₀ ψ` lies in `c.U`.
- `exists_pt`: every `x : testObj hS₀ C ⟶ Y` over `S` with image contained in
  `c.U` equals `c.pt hS₀ ψ` for some algebra map `ψ`. The proof lifts `x.left`
  through the open immersion `c.fromSpec` (`IsOpenImmersion.lift`). It writes
  the lift as `Spec.map φ` (`Spec.map_surjective`). Then it checks that `φ` is
  a `Γ(S, S₀)`-algebra map by comparing structure maps to `S` and cancelling
  the monomorphism `hS₀.fromSpec`.

## Provenance

These are internal helper results with no literature source. They are the
standard description of `Spec C`-valued points of a scheme through an affine
open: the adjunction between `Spec` and global sections and the universal
property of open immersions, both as provided by Mathlib.
