# Tensor stability of local equivalences of scheme-module presheaves

The declaration
`Langlands.Scheme.Modules.tensorLocalEquivalencesIsMonoidalStatement`
is a proposition definition, parameterized by an arbitrary
`X : AlgebraicGeometry.Scheme.{u}`. It states the local-equivalence prerequisite
for descending the sectionwise tensor product to sheaves of modules.
It supplies no proof or typeclass instance of this proposition.

## Exact statement

Let `C = PresheafOfModulesOfCommRing.{u} X.presheaf`. An object is a presheaf
of modules over the structure presheaf of `X`, with module carriers in universe
`u`. The monoidal structure is Mathlib's existing sectionwise one: on an open
`U`, the tensor of `M` and `N` has sections
`M(U) ⊗[𝒪_X(U)] N(U)`, with the induced restriction maps.

Let `J = Opens.grothendieckTopology X`, the site of open subsets of `X` with
its usual open-cover topology. This is the actual root-namespace spelling
in the pinned Mathlib environment of the topology described in the task.
Define the morphism property on `C` by

```lean
J.W.inverseImage (PresheafOfModules.toPresheaf.{u} X.ringCatSheaf.obj)
```

Here `toPresheaf` forgets the module structure to the presheaf of abelian
groups, and `J.W` is the class of local equivalences, equivalently the maps
inverted by sheafification. The ring presheaf `X.ringCatSheaf.obj` is
`X.presheaf` composed with the forgetful functor from commutative rings to
rings, so this is the specified morphism property on `C`.

The proposition is exactly `W.IsMonoidal`. In Mathlib this includes
multiplicativity (identities belong to `W` and `W` is closed under composition)
and these two conditions for every presheaf `P` and every morphism `f` in `C`:
if `W f`, then `W (P ◁ f)` and `W (f ▷ P)`.
There are no hypotheses of flatness, quasicoherence, local freeness, or
affineness. The assertion concerns local equivalences; it does not assert
that tensoring preserves arbitrary monomorphisms.

## Provenance and role

This is an internal prerequisite derived from the standard sheaf tensor
construction, rather than a verbatim statement from the literature. The
original source is the Stacks Project, Section 17.16 (tag 01CA), introductory
definition of tensor product by sheafification and Lemma 17.16.2 (tag 05NA).
That lemma identifies the sheafification of the tensor of two module
presheaves with the tensor of their sheafifications. Its natural compatibility
with morphisms explains the prerequisite: after sheafification a local
equivalence is an isomorphism, and tensoring that isomorphism gives an
isomorphism. This describes the mathematical provenance; a separate proof
must establish the Lean proposition.

The registered source is `stacks-module-tensor-products-2026-10-21`,
*Stacks Project - Tensor products of sheaves of modules (HTML snapshot
2026-10-21)*, retained as the same-named HTML file in the project literature.
Its SHA256 is
`825127394e5828c3a56f5134b8823afba20547d7ba5173f624b2f9556a058e34`.

The implementation interfaces in Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435` are:

- `Algebra/Category/ModuleCat/Presheaf/Monoidal.lean`:
  `PresheafOfModulesOfCommRing.monoidalCategory` and `symmetricCategory` give
  the sectionwise tensor and symmetry used here.
- `Algebra/Category/ModuleCat/Sheaf/Localization.lean`:
  `PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms`
  and the localization instance identify this `W` with the class inverted by
  module sheafification, specializing the ring map to the identity.
- `CategoryTheory/Localization/Monoidal/Basic.lean`:
  `CategoryTheory.MorphismProperty.IsMonoidal` is the exact target.
  Together with the existing localization, a proof permits the construction
  `LocalizedMonoidal`.
- `CategoryTheory/Localization/Monoidal/Braided.lean` transports the symmetric
  structure to that localization. Constructing this structure and relating it
  to the chosen category of scheme-module sheaves are later tasks.

The environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`. This file does not
construct the sheafified tensor bifunctor or prove monoidal pullback.
