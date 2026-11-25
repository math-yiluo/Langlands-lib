# Modules of lifts restrict to localizations as localizations of modules

Namespace `Langlands.AlgebraicGeometry.SmoothLifting`. Fix a smooth morphism
`f : X ⟶ S`, a ring `C` with a square-zero ideal `I`, lifting data
`(x₀, s)`, and a global lift `e`. `LiftModule hI e` is the `C`-module of
global lifts based at `e`. It is defined in `LiftModule.lean`.

## Quasi-coherence for a single element `c : C`

- `exists_pow_lin_eq_of_restr`: two global lifts that agree on `C[1/c]` are
  identified in `LiftModule hI e` after multiplication by some power of
  `c`.
- `exists_restr_eq_pow_lin`: every lift on `C[1/c]` becomes, after
  multiplication by some power of `c`, the restriction of a global lift.
  - Work in a finite chart cover `D(gᵢ)`.
  - Extend the lift chartwise with `Chart.exists_extension_loc`.
  - The auxiliary `exists_pair_torsion` shows that the pairwise differences
    of these extensions are killed by a power of `c`.
  - `exists_glue_corrected` glues the corrected chart lifts.

## Linear structure and packaging

- `LiftModule.instModuleOf`: when the ring is `CommRingCat.of T` for a type
  `T`, the module structure is registered as a `T`-module. Instance search
  does not see through `CommRingCat.of`.
- `LiftModule.instModuleBc`, `LiftModule.instModuleBcOf`, and the matching
  scalar-tower instances: lifts for the data base-changed to a `C`-algebra
  `T` form a `C`-module by restriction of scalars along `C → T`.
- `LiftModule.resLin T hI e`: restriction of lifts `y ↦ y|_T`, as a
  `C`-linear map. `LiftModule.res_lin` is the underlying computation. It
  rests on `gcomb_res`.
- `LiftModule.isLocalizedModule_resLin` (assumes `[Smooth f]`):
  `resLin (Loc c)` is `IsLocalizedModule (Submonoid.powers c)`.
- `LiftModule.equivOfIff`: two lifting data over `C` with the same global
  lifts and the same base point have linearly equivalent modules of lifts.
  The map is the identity on morphisms. Linearity is
  `gcomb_data_indep`.

## Provenance

The statements are internal to the lifting of homomorphisms from groups of
multiplicative type through nilpotent thickenings. They formalize, in
the explicit chart language of this development, that lifts along a
square-zero thickening form a quasi-coherent module. Compare Stacks
Project, More on Morphisms, Lemma 37.11.7 (Tag 02H6), where lifts form a
torsor under a quasi-coherent sheaf of homomorphisms.
