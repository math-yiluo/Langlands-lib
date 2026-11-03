# Finite linear models for proper Hom over a noetherian affine base

`CoherentSheaves.NoetherianHomFiniteLinearModelsStatement.{u}` asserts the
following proposition. Let `R : CommRingCat.{u}` be noetherian, and let
`p : Y → Spec R` be proper and locally of finite presentation. For any two
finitely presented actual module sheaves `M, N` on `Y`, if `N` is flat
over `Spec R` through `p`, then
`intrinsicModuleHomPresheaf p M N` has local finite homogeneous linear
models in the sense of `FiniteLinearEquations.HasLocalModels`.

Thus there is a jointly surjective open cover of `Spec R` by actual
spectra `jᵢ : Spec Rᵢ → Spec R`, and on each full slice over `Spec Rᵢ`
the restricted presheaf is naturally isomorphic to solutions of one
finite matrix over `Rᵢ`. Its solutions on a test scheme are vectors of
global sections of that scheme's structure sheaf, with the scalar
action induced by its structure map. The source Hom presheaf consists
of all maps between the ordinary pullbacks of `M` and `N` to
`T ×[Spec R] Y`, with values explicitly lifted to `Type (u+1)`.
Both the natural isomorphisms and their restriction maps concern every
scheme test, including tests that are not affine.

Only the target module is required to be flat over the base. There is
no hypothesis that `M` is flat, that `p` is flat or smooth, or that the
modules are locally free. Finite presentation of the module sheaves is
the Library's sheaf finite presentation, which implies quasi-coherence.
The index of the open cover and all its rings and schemes lie in the
same universe `u`. The proposition asserts local model existence;
global representability and the Hom sheaf property are separate
obligations.

The source is the Stacks Project, Section 99.3, Situation 99.3.1 and
Lemma 99.3.9 with its proof, followed by the final finite-matrix
construction in the proof of Lemma 99.3.8. The retained original is
`08JS.html`, registered as `stacks-hom-functor-08js-2026-11-02`.
This statement specializes that argument to schemes with affine
noetherian base, proper ambient morphism and finitely presented
modules. Properness gives the required proper support of the target.
The proof of Lemma 99.3.9 reduces ordinary Hom after every base change
to the degree-zero sections of a perfect complex; the proof of Lemma
99.3.8 then obtains a finite homogeneous matrix after an affine open
cover on which its degree-zero projective module is free. The present
conclusion records this intermediate matrix description, rather than
deducing the matrix description from representability alone.

This file defines the proposition and supplies no proof of it.
